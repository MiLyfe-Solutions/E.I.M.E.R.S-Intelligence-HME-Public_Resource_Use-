import V185TrunkScan23Chunk0537

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3180724 : List Nat := [2, 5, 3, 1, 1, 1, 2, 8]
def baseStart_3180724 : Nat := 118140960795 + 3180724 * 2 ^ 59
def prefixEnd_3180724 : Nat := 4983230072969 + 3 ^ 40 * 3180724 * 2
def baseEnd_3180724 : Nat := 60490379307093282830449

theorem tailTrace_3180724 : CollatzResearch.WordTrace tailWord_3180724 prefixEnd_3180724 60490379307093282830449 := by
  unfold tailWord_3180724
  simp only [CollatzResearch.WordTrace]
  refine ⟨58005267464393823628002613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77340356619191764837336817 58005267464393823628002613)
  ·
    refine ⟨5437993824786920965125245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58005267464393823628002613 5437993824786920965125245)
    ·
      refine ⟨2039247684295095361921967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5437993824786920965125245 2039247684295095361921967)
      ·
        refine ⟨3058871526442643042882951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039247684295095361921967 3058871526442643042882951)
        ·
          refine ⟨4588307289663964564324427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058871526442643042882951 4588307289663964564324427)
          ·
            refine ⟨6882460934495946846486641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588307289663964564324427 6882460934495946846486641)
            ·
              refine ⟨5161845700871960134864981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6882460934495946846486641 5161845700871960134864981)
              ·
                refine ⟨60490379307093282830449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5161845700871960134864981 60490379307093282830449)
                ·
                  rfl

theorem cell23_3180724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 8].length) (baseStart_3180724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180724 prefixEnd_3180724 := by exact prefixLift 3180724
  have htrace : WordTrace (prefixWord ++ tailWord_3180724) baseStart_3180724 baseEnd_3180724 := by
    simpa [prefixWord, tailWord_3180724, baseEnd_3180724] using wordTrace_append hprefix tailTrace_3180724
  have hstable : (prefixWord ++ tailWord_3180724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180724).length < 2 ^ (prefixWord ++ tailWord_3180724).sum := by decide
  have hdescent : baseEnd_3180724 < baseStart_3180724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180734 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3180734 : Nat := 118140960795 + 3180734 * 2 ^ 59
def prefixEnd_3180734 : Nat := 4983230072969 + 3 ^ 40 * 3180734 * 2
def baseEnd_3180734 : Nat := 1633245376098063597297077

theorem tailTrace_3180734 : CollatzResearch.WordTrace tailWord_3180734 prefixEnd_3180734 1633245376098063597297077 := by
  unfold tailWord_3180734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501362457343927370483657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77340599772500945975912837 14501362457343927370483657)
  ·
    refine ⟨10876021843007945527862743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14501362457343927370483657 10876021843007945527862743)
    ·
      refine ⟨16314032764511918291794115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876021843007945527862743 16314032764511918291794115)
      ·
        refine ⟨24471049146767877437691173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314032764511918291794115 24471049146767877437691173)
        ·
          refine ⟨4588321715018977019567095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24471049146767877437691173 4588321715018977019567095)
          ·
            refine ⟨6882482572528465529350643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588321715018977019567095 6882482572528465529350643)
            ·
              refine ⟨10323723858792698294025965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882482572528465529350643 10323723858792698294025965)
              ·
                refine ⟨3871396447047261860259737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323723858792698294025965 3871396447047261860259737)
                ·
                  refine ⟨2903547335285446395194803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871396447047261860259737 2903547335285446395194803)
                  ·
                    refine ⟨4355321002928169592792205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903547335285446395194803 4355321002928169592792205)
                    ·
                      refine ⟨1633245376098063597297077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355321002928169592792205 1633245376098063597297077)
                      ·
                        rfl

theorem cell23_3180734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3180734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180734 prefixEnd_3180734 := by exact prefixLift 3180734
  have htrace : WordTrace (prefixWord ++ tailWord_3180734) baseStart_3180734 baseEnd_3180734 := by
    simpa [prefixWord, tailWord_3180734, baseEnd_3180734] using wordTrace_append hprefix tailTrace_3180734
  have hstable : (prefixWord ++ tailWord_3180734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180734).length < 2 ^ (prefixWord ++ tailWord_3180734).sum := by decide
  have hdescent : baseEnd_3180734 < baseStart_3180734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180780 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 5]
def baseStart_3180780 : Nat := 118140960795 + 3180780 * 2 ^ 59
def prefixEnd_3180780 : Nat := 4983230072969 + 3 ^ 40 * 3180780 * 2
def baseEnd_3180780 : Nat := 181474332912018935257985

theorem tailTrace_3180780 : CollatzResearch.WordTrace tailWord_3180780 prefixEnd_3180780 181474332912018935257985 := by
  unfold tailWord_3180780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58006288708292384410021897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77341718277723179213362529 58006288708292384410021897)
  ·
    refine ⟨43504716531219288307516423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58006288708292384410021897 43504716531219288307516423)
    ·
      refine ⟨65257074796828932461274635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43504716531219288307516423 65257074796828932461274635)
      ·
        refine ⟨97885612195243398691911953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65257074796828932461274635 97885612195243398691911953)
        ·
          refine ⟨73414209146432549018933965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97885612195243398691911953 73414209146432549018933965)
          ·
            refine ⟨27530328429912205882100237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73414209146432549018933965 27530328429912205882100237)
            ·
              refine ⟨10323873161217077205787589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27530328429912205882100237 10323873161217077205787589)
              ·
                refine ⟨1935726217728201976085173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10323873161217077205787589 1935726217728201976085173)
                ·
                  refine ⟨181474332912018935257985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1935726217728201976085173 181474332912018935257985)
                  ·
                    rfl

theorem cell23_3180780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_3180780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180780 prefixEnd_3180780 := by exact prefixLift 3180780
  have htrace : WordTrace (prefixWord ++ tailWord_3180780) baseStart_3180780 baseEnd_3180780 := by
    simpa [prefixWord, tailWord_3180780, baseEnd_3180780] using wordTrace_append hprefix tailTrace_3180780
  have hstable : (prefixWord ++ tailWord_3180780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180780).length < 2 ^ (prefixWord ++ tailWord_3180780).sum := by decide
  have hdescent : baseEnd_3180780 < baseStart_3180780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180790 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3180790 : Nat := 118140960795 + 3180790 * 2 ^ 59
def prefixEnd_3180790 : Nat := 4983230072969 + 3 ^ 40 * 3180790 * 2
def baseEnd_3180790 : Nat := 1633274131014715378196819

theorem tailTrace_3180790 : CollatzResearch.WordTrace tailWord_3180790 prefixEnd_3180790 1633274131014715378196819 := by
  unfold tailWord_3180790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250808884159283782994239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77341961431032360351938549 7250808884159283782994239)
  ·
    refine ⟨10876213326238925674491359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7250808884159283782994239 10876213326238925674491359)
    ·
      refine ⟨16314319989358388511737039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10876213326238925674491359 16314319989358388511737039)
      ·
        refine ⟨24471479984037582767605559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314319989358388511737039 24471479984037582767605559)
        ·
          refine ⟨36707219976056374151408339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24471479984037582767605559 36707219976056374151408339)
          ·
            refine ⟨55060829964084561227112509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36707219976056374151408339 55060829964084561227112509)
            ·
              refine ⟨20647811236531710460167191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55060829964084561227112509 20647811236531710460167191)
              ·
                refine ⟨30971716854797565690250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20647811236531710460167191 30971716854797565690250787)
                ·
                  refine ⟨46457575282196348535376181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30971716854797565690250787 46457575282196348535376181)
                  ·
                    refine ⟨4355397682705907675191517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46457575282196348535376181 4355397682705907675191517)
                    ·
                      refine ⟨1633274131014715378196819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355397682705907675191517 1633274131014715378196819)
                      ·
                        rfl

theorem cell23_3180790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3180790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180790 prefixEnd_3180790 := by exact prefixLift 3180790
  have htrace : WordTrace (prefixWord ++ tailWord_3180790) baseStart_3180790 baseEnd_3180790 := by
    simpa [prefixWord, tailWord_3180790, baseEnd_3180790] using wordTrace_append hprefix tailTrace_3180790
  have hstable : (prefixWord ++ tailWord_3180790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180790).length < 2 ^ (prefixWord ++ tailWord_3180790).sum := by decide
  have hdescent : baseEnd_3180790 < baseStart_3180790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180810 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_3180810 : Nat := 118140960795 + 3180810 * 2 ^ 59
def prefixEnd_3180810 : Nat := 4983230072969 + 3 ^ 40 * 3180810 * 2
def baseEnd_3180810 : Nat := 544428133542601766648909

theorem tailTrace_3180810 : CollatzResearch.WordTrace tailWord_3180810 prefixEnd_3180810 544428133542601766648909 := by
  unfold tailWord_3180810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003417901619020985908971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77342447737650722629090589 29003417901619020985908971)
  ·
    refine ⟨43505126852428531478863457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003417901619020985908971 43505126852428531478863457)
    ·
      refine ⟨32628845139321398609147593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43505126852428531478863457 32628845139321398609147593)
      ·
        refine ⟨24471633854491048956860695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32628845139321398609147593 24471633854491048956860695)
        ·
          refine ⟨36707450781736573435291043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24471633854491048956860695 36707450781736573435291043)
          ·
            refine ⟨55061176172604860152936565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36707450781736573435291043 55061176172604860152936565)
            ·
              refine ⟨5161985266181705639337803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55061176172604860152936565 5161985266181705639337803)
              ·
                refine ⟨7742977899272558459006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161985266181705639337803 7742977899272558459006705)
                ·
                  refine ⟨5807233424454418844255029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7742977899272558459006705 5807233424454418844255029)
                  ·
                    refine ⟨544428133542601766648909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807233424454418844255029 544428133542601766648909)
                    ·
                      rfl

theorem cell23_3180810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_3180810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180810 prefixEnd_3180810 := by exact prefixLift 3180810
  have htrace : WordTrace (prefixWord ++ tailWord_3180810) baseStart_3180810 baseEnd_3180810 := by
    simpa [prefixWord, tailWord_3180810, baseEnd_3180810] using wordTrace_append hprefix tailTrace_3180810
  have hstable : (prefixWord ++ tailWord_3180810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180810).length < 2 ^ (prefixWord ++ tailWord_3180810).sum := by decide
  have hdescent : baseEnd_3180810 < baseStart_3180810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180833 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3180833 : Nat := 118140960795 + 3180833 * 2 ^ 59
def prefixEnd_3180833 : Nat := 4983230072969 + 3 ^ 40 * 3180833 * 2
def baseEnd_3180833 : Nat := 1633296210682858709959121

theorem tailTrace_3180833 : CollatzResearch.WordTrace tailWord_3180833 prefixEnd_3180833 1633296210682858709959121 := by
  unfold tailWord_3180833
  simp only [CollatzResearch.WordTrace]
  refine ⟨116014510485392758871723153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77343006990261839247815435 116014510485392758871723153)
  ·
    refine ⟨87010882864044569153792365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116014510485392758871723153 87010882864044569153792365)
    ·
      refine ⟨32629081074016713432672137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87010882864044569153792365 32629081074016713432672137)
      ·
        refine ⟨24471810805512535074504103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32629081074016713432672137 24471810805512535074504103)
        ·
          refine ⟨36707716208268802611756155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24471810805512535074504103 36707716208268802611756155)
          ·
            refine ⟨55061574312403203917634233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36707716208268802611756155 55061574312403203917634233)
            ·
              refine ⟨41296180734302402938225675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55061574312403203917634233 41296180734302402938225675)
              ·
                refine ⟨61944271101453604407338513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41296180734302402938225675 61944271101453604407338513)
                ·
                  refine ⟨46458203326090203305503885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61944271101453604407338513 46458203326090203305503885)
                  ·
                    refine ⟨17421826247283826239563957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46458203326090203305503885 17421826247283826239563957)
                    ·
                      refine ⟨1633296210682858709959121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17421826247283826239563957 1633296210682858709959121)
                      ·
                        rfl

theorem cell23_3180833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3180833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180833 prefixEnd_3180833 := by exact prefixLift 3180833
  have htrace : WordTrace (prefixWord ++ tailWord_3180833) baseStart_3180833 baseEnd_3180833 := by
    simpa [prefixWord, tailWord_3180833, baseEnd_3180833] using wordTrace_append hprefix tailTrace_3180833
  have hstable : (prefixWord ++ tailWord_3180833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180833).length < 2 ^ (prefixWord ++ tailWord_3180833).sum := by decide
  have hdescent : baseEnd_3180833 < baseStart_3180833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180857 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_3180857 : Nat := 118140960795 + 3180857 * 2 ^ 59
def prefixEnd_3180857 : Nat := 4983230072969 + 3 ^ 40 * 3180857 * 2
def baseEnd_3180857 : Nat := 544436178072855538686337

theorem tailTrace_3180857 : CollatzResearch.WordTrace tailWord_3180857 prefixEnd_3180857 544436178072855538686337 := by
  unfold tailWord_3180857
  simp only [CollatzResearch.WordTrace]
  refine ⟨116015385837305810970596825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77343590558203873980397883 116015385837305810970596825)
  ·
    refine ⟨87011539377979358227947619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116015385837305810970596825 87011539377979358227947619)
    ·
      refine ⟨130517309066969037341921429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87011539377979358227947619 130517309066969037341921429)
      ·
        refine ⟨6117998862514173625402567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130517309066969037341921429 6117998862514173625402567)
        ·
          refine ⟨9176998293771260438103851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117998862514173625402567 9176998293771260438103851)
          ·
            refine ⟨13765497440656890657155777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176998293771260438103851 13765497440656890657155777)
            ·
              refine ⟨10324123080492667992866833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13765497440656890657155777 10324123080492667992866833)
              ·
                refine ⟨7743092310369500994650125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10324123080492667992866833 7743092310369500994650125)
                ·
                  refine ⟨2903659616388562872993797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7743092310369500994650125 2903659616388562872993797)
                  ·
                    refine ⟨544436178072855538686337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2903659616388562872993797 544436178072855538686337)
                    ·
                      rfl

theorem cell23_3180857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_3180857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180857 prefixEnd_3180857 := by exact prefixLift 3180857
  have htrace : WordTrace (prefixWord ++ tailWord_3180857) baseStart_3180857 baseEnd_3180857 := by
    simpa [prefixWord, tailWord_3180857, baseEnd_3180857] using wordTrace_append hprefix tailTrace_3180857
  have hstable : (prefixWord ++ tailWord_3180857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180857).length < 2 ^ (prefixWord ++ tailWord_3180857).sum := by decide
  have hdescent : baseEnd_3180857 < baseStart_3180857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180900 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3180900 : Nat := 118140960795 + 3180900 * 2 ^ 59
def prefixEnd_3180900 : Nat := 4983230072969 + 3 ^ 40 * 3180900 * 2
def baseEnd_3180900 : Nat := 544443537962236649273771

theorem tailTrace_3180900 : CollatzResearch.WordTrace tailWord_3180900 prefixEnd_3180900 544443537962236649273771 := by
  unfold tailWord_3180900
  simp only [CollatzResearch.WordTrace]
  refine ⟨58008477088075014657206077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77344636117433352876274769 58008477088075014657206077)
  ·
    refine ⟨21753178908028130496452279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58008477088075014657206077 21753178908028130496452279)
    ·
      refine ⟨32629768362042195744678419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21753178908028130496452279 32629768362042195744678419)
      ·
        refine ⟨48944652543063293617017629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32629768362042195744678419 48944652543063293617017629)
        ·
          refine ⟨18354244703648735106381611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48944652543063293617017629 18354244703648735106381611)
          ·
            refine ⟨27531367055473102659572417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18354244703648735106381611 27531367055473102659572417)
            ·
              refine ⟨20648525291604826994679313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27531367055473102659572417 20648525291604826994679313)
              ·
                refine ⟨15486393968703620246009485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20648525291604826994679313 15486393968703620246009485)
                ·
                  refine ⟨5807397738263857592253557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15486393968703620246009485 5807397738263857592253557)
                  ·
                    refine ⟨544443537962236649273771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807397738263857592253557 544443537962236649273771)
                    ·
                      rfl

theorem cell23_3180900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3180900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180900 prefixEnd_3180900 := by exact prefixLift 3180900
  have htrace : WordTrace (prefixWord ++ tailWord_3180900) baseStart_3180900 baseEnd_3180900 := by
    simpa [prefixWord, tailWord_3180900, baseEnd_3180900] using wordTrace_append hprefix tailTrace_3180900
  have hstable : (prefixWord ++ tailWord_3180900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180900).length < 2 ^ (prefixWord ++ tailWord_3180900).sum := by decide
  have hdescent : baseEnd_3180900 < baseStart_3180900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180904 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 6]
def baseStart_3180904 : Nat := 118140960795 + 3180904 * 2 ^ 59
def prefixEnd_3180904 : Nat := 4983230072969 + 3 ^ 40 * 3180904 * 2
def baseEnd_3180904 : Nat := 181481407534369770241255

theorem tailTrace_3180904 : CollatzResearch.WordTrace tailWord_3180904 prefixEnd_3180904 181481407534369770241255 := by
  unfold tailWord_3180904
  simp only [CollatzResearch.WordTrace]
  refine ⟨58008550034067768998778883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77344733378757025331705177 58008550034067768998778883)
  ·
    refine ⟨87012825051101653498168325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58008550034067768998778883 87012825051101653498168325)
    ·
      refine ⟨16314904697081560030906561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87012825051101653498168325 16314904697081560030906561)
      ·
        refine ⟨12236178522811170023179921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16314904697081560030906561 12236178522811170023179921)
        ·
          refine ⟨9177133892108377517384941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12236178522811170023179921 9177133892108377517384941)
          ·
            refine ⟨3441425209540641569019353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9177133892108377517384941 3441425209540641569019353)
            ·
              refine ⟨2581068907155481176764515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441425209540641569019353 2581068907155481176764515)
              ·
                refine ⟨3871603360733221765146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581068907155481176764515 3871603360733221765146773)
                ·
                  refine ⟨181481407534369770241255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3871603360733221765146773 181481407534369770241255)
                  ·
                    rfl

theorem cell23_3180904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_3180904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180904 prefixEnd_3180904 := by exact prefixLift 3180904
  have htrace : WordTrace (prefixWord ++ tailWord_3180904) baseStart_3180904 baseEnd_3180904 := by
    simpa [prefixWord, tailWord_3180904, baseEnd_3180904] using wordTrace_append hprefix tailTrace_3180904
  have hstable : (prefixWord ++ tailWord_3180904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180904).length < 2 ^ (prefixWord ++ tailWord_3180904).sum := by decide
  have hdescent : baseEnd_3180904 < baseStart_3180904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180917 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3180917 : Nat := 118140960795 + 3180917 * 2 ^ 59
def prefixEnd_3180917 : Nat := 4983230072969 + 3 ^ 40 * 3180917 * 2
def baseEnd_3180917 : Nat := 544446447685945460436245

theorem tailTrace_3180917 : CollatzResearch.WordTrace tailWord_3180917 prefixEnd_3180917 544446447685945460436245 := by
  unfold tailWord_3180917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116017574217088441217781005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77345049478058960811854003 116017574217088441217781005)
  ·
    refine ⟨43506590331408165456667877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116017574217088441217781005 43506590331408165456667877)
    ·
      refine ⟨8157485687139031023125227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43506590331408165456667877 8157485687139031023125227)
      ·
        refine ⟨12236228530708546534687841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157485687139031023125227 12236228530708546534687841)
        ·
          refine ⟨9177171398031409901015881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12236228530708546534687841 9177171398031409901015881)
          ·
            refine ⟨6882878548523557425761911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9177171398031409901015881 6882878548523557425761911)
            ·
              refine ⟨10324317822785336138642867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882878548523557425761911 10324317822785336138642867)
              ·
                refine ⟨15486476734178004207964301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10324317822785336138642867 15486476734178004207964301)
                ·
                  refine ⟨5807428775316751577986613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15486476734178004207964301 5807428775316751577986613)
                  ·
                    refine ⟨544446447685945460436245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807428775316751577986613 544446447685945460436245)
                    ·
                      rfl

theorem cell23_3180917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3180917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180917 prefixEnd_3180917 := by exact prefixLift 3180917
  have htrace : WordTrace (prefixWord ++ tailWord_3180917) baseStart_3180917 baseEnd_3180917 := by
    simpa [prefixWord, tailWord_3180917, baseEnd_3180917] using wordTrace_append hprefix tailTrace_3180917
  have hstable : (prefixWord ++ tailWord_3180917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180917).length < 2 ^ (prefixWord ++ tailWord_3180917).sum := by decide
  have hdescent : baseEnd_3180917 < baseStart_3180917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180948 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3180948 : Nat := 118140960795 + 3180948 * 2 ^ 59
def prefixEnd_3180948 : Nat := 4983230072969 + 3 ^ 40 * 3180948 * 2
def baseEnd_3180948 : Nat := 1633355260958125760021093

theorem tailTrace_3180948 : CollatzResearch.WordTrace tailWord_3180948 prefixEnd_3180948 1633355260958125760021093 := by
  unfold tailWord_3180948
  simp only [CollatzResearch.WordTrace]
  refine ⟨58009352439988066756079749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77345803253317422341439665 58009352439988066756079749)
  ·
    refine ⟨10876753582497762516764953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58009352439988066756079749 10876753582497762516764953)
    ·
      refine ⟨8157565186873321887573715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10876753582497762516764953 8157565186873321887573715)
      ·
        refine ⟨12236347780309982831360573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157565186873321887573715 12236347780309982831360573)
        ·
          refine ⟨4588630417616243561760215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12236347780309982831360573 4588630417616243561760215)
          ·
            refine ⟨6882945626424365342640323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588630417616243561760215 6882945626424365342640323)
            ·
              refine ⟨10324418439636548013960485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882945626424365342640323 10324418439636548013960485)
              ·
                refine ⟨1935828457431852752617591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10324418439636548013960485 1935828457431852752617591)
                ·
                  refine ⟨2903742686147779128926387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935828457431852752617591 2903742686147779128926387)
                  ·
                    refine ⟨4355614029221668693389581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2903742686147779128926387 4355614029221668693389581)
                    ·
                      refine ⟨1633355260958125760021093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355614029221668693389581 1633355260958125760021093)
                      ·
                        rfl

theorem cell23_3180948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3180948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180948 prefixEnd_3180948 := by exact prefixLift 3180948
  have htrace : WordTrace (prefixWord ++ tailWord_3180948) baseStart_3180948 baseEnd_3180948 := by
    simpa [prefixWord, tailWord_3180948, baseEnd_3180948] using wordTrace_append hprefix tailTrace_3180948
  have hstable : (prefixWord ++ tailWord_3180948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180948).length < 2 ^ (prefixWord ++ tailWord_3180948).sum := by decide
  have hdescent : baseEnd_3180948 < baseStart_3180948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180960 : List Nat := [2, 1, 1, 4, 1, 3, 3, 8]
def baseStart_3180960 : Nat := 118140960795 + 3180960 * 2 ^ 59
def prefixEnd_3180960 : Nat := 4983230072969 + 3 ^ 40 * 3180960 * 2
def baseEnd_3180960 : Nat := 60494867508369619002631

theorem tailTrace_3180960 : CollatzResearch.WordTrace tailWord_3180960 prefixEnd_3180960 60494867508369619002631 := by
  unfold tailWord_3180960
  simp only [CollatzResearch.WordTrace]
  refine ⟨58009571277966329780798167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77346095037288439707730889 58009571277966329780798167)
  ·
    refine ⟨87014356916949494671197251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58009571277966329780798167 87014356916949494671197251)
    ·
      refine ⟨130521535375424242006795877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87014356916949494671197251 130521535375424242006795877)
      ·
        refine ⟨24472787882892045376274227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130521535375424242006795877 24472787882892045376274227)
        ·
          refine ⟨36709181824338068064411341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24472787882892045376274227 36709181824338068064411341)
          ·
            refine ⟨13765943184126775524154253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36709181824338068064411341 13765943184126775524154253)
            ·
              refine ⟨5162228694047540821557845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13765943184126775524154253 5162228694047540821557845)
              ·
                refine ⟨60494867508369619002631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5162228694047540821557845 60494867508369619002631)
                ·
                  rfl

theorem cell23_3180960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_3180960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180960 prefixEnd_3180960 := by exact prefixLift 3180960
  have htrace : WordTrace (prefixWord ++ tailWord_3180960) baseStart_3180960 baseEnd_3180960 := by
    simpa [prefixWord, tailWord_3180960, baseEnd_3180960] using wordTrace_append hprefix tailTrace_3180960
  have hstable : (prefixWord ++ tailWord_3180960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180960).length < 2 ^ (prefixWord ++ tailWord_3180960).sum := by decide
  have hdescent : baseEnd_3180960 < baseStart_3180960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180967 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3180967 : Nat := 118140960795 + 3180967 * 2 ^ 59
def prefixEnd_3180967 : Nat := 4983230072969 + 3 ^ 40 * 3180967 * 2
def baseEnd_3180967 : Nat := 1633365017090561185683505

theorem tailTrace_3180967 : CollatzResearch.WordTrace tailWord_3180967 prefixEnd_3180967 1633365017090561185683505 := by
  unfold tailWord_3180967
  simp only [CollatzResearch.WordTrace]
  refine ⟨116019397866907299757101155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77346265244604866504734103 116019397866907299757101155)
  ·
    refine ⟨174029096800360949635651733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116019397866907299757101155 174029096800360949635651733)
    ·
      refine ⟨8157613912516919514171175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174029096800360949635651733 8157613912516919514171175)
      ·
        refine ⟨12236420868775379271256763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157613912516919514171175 12236420868775379271256763)
        ·
          refine ⟨18354631303163068906885145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236420868775379271256763 18354631303163068906885145)
          ·
            refine ⟨13765973477372301680163859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18354631303163068906885145 13765973477372301680163859)
            ·
              refine ⟨20648960216058452520245789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13765973477372301680163859 20648960216058452520245789)
              ·
                refine ⟨7743360081021919695092171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20648960216058452520245789 7743360081021919695092171)
                ·
                  refine ⟨11615040121532879542638257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7743360081021919695092171 11615040121532879542638257)
                  ·
                    refine ⟨8711280091149659656978693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11615040121532879542638257 8711280091149659656978693)
                    ·
                      refine ⟨1633365017090561185683505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8711280091149659656978693 1633365017090561185683505)
                      ·
                        rfl

theorem cell23_3180967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3180967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180967 prefixEnd_3180967 := by exact prefixLift 3180967
  have htrace : WordTrace (prefixWord ++ tailWord_3180967) baseStart_3180967 baseEnd_3180967 := by
    simpa [prefixWord, tailWord_3180967, baseEnd_3180967] using wordTrace_append hprefix tailTrace_3180967
  have hstable : (prefixWord ++ tailWord_3180967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180967).length < 2 ^ (prefixWord ++ tailWord_3180967).sum := by decide
  have hdescent : baseEnd_3180967 < baseStart_3180967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180977 : List Nat := [1, 2, 2, 4, 1, 3, 3, 7]
def baseStart_3180977 : Nat := 118140960795 + 3180977 * 2 ^ 59
def prefixEnd_3180977 : Nat := 4983230072969 + 3 ^ 40 * 3180977 * 2
def baseEnd_3180977 : Nat := 60495190811003931354017

theorem tailTrace_3180977 : CollatzResearch.WordTrace tailWord_3180977 prefixEnd_3180977 60495190811003931354017 := by
  unfold tailWord_3180977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116019762596871071464965185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77346508397914047643310123 116019762596871071464965185)
  ·
    refine ⟨87014821947653303598723889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116019762596871071464965185 87014821947653303598723889)
    ·
      refine ⟨65261116460739977699042917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87014821947653303598723889 65261116460739977699042917)
      ·
        refine ⟨12236459336388745818570547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65261116460739977699042917 12236459336388745818570547)
        ·
          refine ⟨18354689004583118727855821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236459336388745818570547 18354689004583118727855821)
          ·
            refine ⟨6883008376718669522945933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18354689004583118727855821 6883008376718669522945933)
            ·
              refine ⟨2581128141269501071104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6883008376718669522945933 2581128141269501071104725)
              ·
                refine ⟨60495190811003931354017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2581128141269501071104725 60495190811003931354017)
                ·
                  rfl

theorem cell23_3180977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 7].length) (baseStart_3180977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180977 prefixEnd_3180977 := by exact prefixLift 3180977
  have htrace : WordTrace (prefixWord ++ tailWord_3180977) baseStart_3180977 baseEnd_3180977 := by
    simpa [prefixWord, tailWord_3180977, baseEnd_3180977] using wordTrace_append hprefix tailTrace_3180977
  have hstable : (prefixWord ++ tailWord_3180977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180977).length < 2 ^ (prefixWord ++ tailWord_3180977).sum := by decide
  have hdescent : baseEnd_3180977 < baseStart_3180977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3180988 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_3180988 : Nat := 118140960795 + 3180988 * 2 ^ 59
def prefixEnd_3180988 : Nat := 4983230072969 + 3 ^ 40 * 3180988 * 2
def baseEnd_3180988 : Nat := 1633375800184305603520909

theorem tailTrace_3180988 : CollatzResearch.WordTrace tailWord_3180988 prefixEnd_3180988 1633375800184305603520909 := by
  unfold tailWord_3180988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58010081899915610171807809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77346775866554146895743745 58010081899915610171807809)
  ·
    refine ⟨43507561424936707628855857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58010081899915610171807809 43507561424936707628855857)
    ·
      refine ⟨32630671068702530721641893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43507561424936707628855857 32630671068702530721641893)
      ·
        refine ⟨6118250825381724510307855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32630671068702530721641893 6118250825381724510307855)
        ·
          refine ⟨9177376238072586765461783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118250825381724510307855 9177376238072586765461783)
          ·
            refine ⟨13766064357108880148192675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9177376238072586765461783 13766064357108880148192675)
            ·
              refine ⟨20649096535663320222289013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13766064357108880148192675 20649096535663320222289013)
              ·
                refine ⟨1935852800218436270839595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20649096535663320222289013 1935852800218436270839595)
                ·
                  refine ⟨2903779200327654406259393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935852800218436270839595 2903779200327654406259393)
                  ·
                    refine ⟨2177834400245740804694545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903779200327654406259393 2177834400245740804694545)
                    ·
                      refine ⟨1633375800184305603520909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177834400245740804694545 1633375800184305603520909)
                      ·
                        rfl

theorem cell23_3180988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_3180988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3180988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3180988 prefixEnd_3180988 := by exact prefixLift 3180988
  have htrace : WordTrace (prefixWord ++ tailWord_3180988) baseStart_3180988 baseEnd_3180988 := by
    simpa [prefixWord, tailWord_3180988, baseEnd_3180988] using wordTrace_append hprefix tailTrace_3180988
  have hstable : (prefixWord ++ tailWord_3180988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3180988).length < 2 ^ (prefixWord ++ tailWord_3180988).sum := by decide
  have hdescent : baseEnd_3180988 < baseStart_3180988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3180988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181031 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3181031 : Nat := 118140960795 + 3181031 * 2 ^ 59
def prefixEnd_3181031 : Nat := 4983230072969 + 3 ^ 40 * 3181031 * 2
def baseEnd_3181031 : Nat := 1633397879852448935283211

theorem tailTrace_3181031 : CollatzResearch.WordTrace tailWord_3181031 prefixEnd_3181031 1633397879852448935283211 := by
  unfold tailWord_3181031
  simp only [CollatzResearch.WordTrace]
  refine ⟨116021732138675438687430947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77347821425783625791620631 116021732138675438687430947)
  ·
    refine ⟨174032598208013158031146421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116021732138675438687430947 174032598208013158031146421)
    ·
      refine ⟨16315556082001233565419977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174032598208013158031146421 16315556082001233565419977)
      ·
        refine ⟨12236667061500925174064983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16315556082001233565419977 12236667061500925174064983)
        ·
          refine ⟨18355000592251387761097475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236667061500925174064983 18355000592251387761097475)
          ·
            refine ⟨27532500888377081641646213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355000592251387761097475 27532500888377081641646213)
            ·
              refine ⟨5162343916570702807808665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27532500888377081641646213 5162343916570702807808665)
              ·
                refine ⟨3871757937428027105856499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162343916570702807808665 3871757937428027105856499)
                ·
                  refine ⟨5807636906142040658784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871757937428027105856499 5807636906142040658784749)
                  ·
                    refine ⟨2177863839803265247044281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5807636906142040658784749 2177863839803265247044281)
                    ·
                      refine ⟨1633397879852448935283211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177863839803265247044281 1633397879852448935283211)
                      ·
                        rfl

theorem cell23_3181031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3181031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181031 prefixEnd_3181031 := by exact prefixLift 3181031
  have htrace : WordTrace (prefixWord ++ tailWord_3181031) baseStart_3181031 baseEnd_3181031 := by
    simpa [prefixWord, tailWord_3181031, baseEnd_3181031] using wordTrace_append hprefix tailTrace_3181031
  have hstable : (prefixWord ++ tailWord_3181031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181031).length < 2 ^ (prefixWord ++ tailWord_3181031).sum := by decide
  have hdescent : baseEnd_3181031 < baseStart_3181031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181067 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 7]
def baseStart_3181067 : Nat := 118140960795 + 3181067 * 2 ^ 59
def prefixEnd_3181067 : Nat := 4983230072969 + 3 ^ 40 * 3181067 * 2
def baseEnd_3181067 : Nat := 181490707239556754937005

theorem tailTrace_3181067 : CollatzResearch.WordTrace tailWord_3181067 prefixEnd_3181067 181490707239556754937005 := by
  unfold tailWord_3181067
  simp only [CollatzResearch.WordTrace]
  refine ⟨116023045166545016835741455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77348696777696677890494303 116023045166545016835741455)
  ·
    refine ⟨174034567749817525253612183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116023045166545016835741455 174034567749817525253612183)
    ·
      refine ⟨261051851624726287880418275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174034567749817525253612183 261051851624726287880418275)
      ·
        refine ⟨391577777437089431820627413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261051851624726287880418275 391577777437089431820627413)
        ·
          refine ⟨9177604158681783558295955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 391577777437089431820627413 9177604158681783558295955)
          ·
            refine ⟨13766406238022675337443933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9177604158681783558295955 13766406238022675337443933)
            ·
              refine ⟨5162402339258503251541475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13766406238022675337443933 5162402339258503251541475)
              ·
                refine ⟨7743603508887754877312213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162402339258503251541475 7743603508887754877312213)
                ·
                  refine ⟨181490707239556754937005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7743603508887754877312213 181490707239556754937005)
                  ·
                    rfl

theorem cell23_3181067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 7].length) (baseStart_3181067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181067 prefixEnd_3181067 := by exact prefixLift 3181067
  have htrace : WordTrace (prefixWord ++ tailWord_3181067) baseStart_3181067 baseEnd_3181067 := by
    simpa [prefixWord, tailWord_3181067, baseEnd_3181067] using wordTrace_append hprefix tailTrace_3181067
  have hstable : (prefixWord ++ tailWord_3181067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181067).length < 2 ^ (prefixWord ++ tailWord_3181067).sum := by decide
  have hdescent : baseEnd_3181067 < baseStart_3181067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181077 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_3181077 : Nat := 118140960795 + 3181077 * 2 ^ 59
def prefixEnd_3181077 : Nat := 4983230072969 + 3 ^ 40 * 3181077 * 2
def baseEnd_3181077 : Nat := 1633421499962555755307999

theorem tailTrace_3181077 : CollatzResearch.WordTrace tailWord_3181077 prefixEnd_3181077 1633421499962555755307999 := by
  unfold tailWord_3181077
  simp only [CollatzResearch.WordTrace]
  refine ⟨116023409896508788543605485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77348939931005859029070323 116023409896508788543605485)
  ·
    refine ⟨43508778711190795703852057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116023409896508788543605485 43508778711190795703852057)
    ·
      refine ⟨32631584033393096777889043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43508778711190795703852057 32631584033393096777889043)
      ·
        refine ⟨48947376050089645166833565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32631584033393096777889043 48947376050089645166833565)
        ·
          refine ⟨18355266018783616937562587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48947376050089645166833565 18355266018783616937562587)
          ·
            refine ⟨27532899028175425406343881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355266018783616937562587 27532899028175425406343881)
            ·
              refine ⟨20649674271131569054757911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27532899028175425406343881 20649674271131569054757911)
              ·
                refine ⟨30974511406697353582136867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20649674271131569054757911 30974511406697353582136867)
                ·
                  refine ⟨46461767110046030373205301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30974511406697353582136867 46461767110046030373205301)
                  ·
                    refine ⟨4355790666566815347487997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46461767110046030373205301 4355790666566815347487997)
                    ·
                      refine ⟨1633421499962555755307999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4355790666566815347487997 1633421499962555755307999)
                      ·
                        rfl

theorem cell23_3181077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_3181077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181077 prefixEnd_3181077 := by exact prefixLift 3181077
  have htrace : WordTrace (prefixWord ++ tailWord_3181077) baseStart_3181077 baseEnd_3181077 := by
    simpa [prefixWord, tailWord_3181077, baseEnd_3181077] using wordTrace_append hprefix tailTrace_3181077
  have hstable : (prefixWord ++ tailWord_3181077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181077).length < 2 ^ (prefixWord ++ tailWord_3181077).sum := by decide
  have hdescent : baseEnd_3181077 < baseStart_3181077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181118 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_3181118 : Nat := 118140960795 + 3181118 * 2 ^ 59
def prefixEnd_3181118 : Nat := 4983230072969 + 3 ^ 40 * 3181118 * 2
def baseEnd_3181118 : Nat := 181493616963265566099479

theorem tailTrace_3181118 : CollatzResearch.WordTrace tailWord_3181118 prefixEnd_3181118 181493616963265566099479 := by
  unfold tailWord_3181118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503113161170031568231001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77349936859573501697232005 14503113161170031568231001)
  ·
    refine ⟨10877334870877523676173251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14503113161170031568231001 10877334870877523676173251)
    ·
      refine ⟨16316002306316285514259877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877334870877523676173251 16316002306316285514259877)
      ·
        refine ⟨3059250432434303533923727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16316002306316285514259877 3059250432434303533923727)
        ·
          refine ⟨4588875648651455300885591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059250432434303533923727 4588875648651455300885591)
          ·
            refine ⟨6883313472977182951328387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588875648651455300885591 6883313472977182951328387)
            ·
              refine ⟨10324970209465774426992581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883313472977182951328387 10324970209465774426992581)
              ·
                refine ⟨1935931914274832705061109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10324970209465774426992581 1935931914274832705061109)
                ·
                  refine ⟨181493616963265566099479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1935931914274832705061109 181493616963265566099479)
                  ·
                    rfl

theorem cell23_3181118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_3181118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181118 prefixEnd_3181118 := by exact prefixLift 3181118
  have htrace : WordTrace (prefixWord ++ tailWord_3181118) baseStart_3181118 baseEnd_3181118 := by
    simpa [prefixWord, tailWord_3181118, baseEnd_3181118] using wordTrace_append hprefix tailTrace_3181118
  have hstable : (prefixWord ++ tailWord_3181118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181118).length < 2 ^ (prefixWord ++ tailWord_3181118).sum := by decide
  have hdescent : baseEnd_3181118 < baseStart_3181118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181134 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_3181134 : Nat := 118140960795 + 3181134 * 2 ^ 59
def prefixEnd_3181134 : Nat := 4983230072969 + 3 ^ 40 * 3181134 * 2
def baseEnd_3181134 : Nat := 1633450768359862032295237

theorem tailTrace_3181134 : CollatzResearch.WordTrace tailWord_3181134 prefixEnd_3181134 1633450768359862032295237 := by
  unfold tailWord_3181134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503186107162785909803807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77350325904868191518953637 14503186107162785909803807)
  ·
    refine ⟨21754779160744178864705711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14503186107162785909803807 21754779160744178864705711)
    ·
      refine ⟨32632168741116268297058567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21754779160744178864705711 32632168741116268297058567)
      ·
        refine ⟨48948253111674402445587851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32632168741116268297058567 48948253111674402445587851)
        ·
          refine ⟨73422379667511603668381777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48948253111674402445587851 73422379667511603668381777)
          ·
            refine ⟨55066784750633702751286333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73422379667511603668381777 55066784750633702751286333)
            ·
              refine ⟨20650044281487638531732375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55066784750633702751286333 20650044281487638531732375)
              ·
                refine ⟨30975066422231457797598563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20650044281487638531732375 30975066422231457797598563)
                ·
                  refine ⟨46462599633347186696397845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30975066422231457797598563 46462599633347186696397845)
                  ·
                    refine ⟨2177934357813149376393649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46462599633347186696397845 2177934357813149376393649)
                    ·
                      refine ⟨1633450768359862032295237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2177934357813149376393649 1633450768359862032295237)
                      ·
                        rfl

theorem cell23_3181134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_3181134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181134 prefixEnd_3181134 := by exact prefixLift 3181134
  have htrace : WordTrace (prefixWord ++ tailWord_3181134) baseStart_3181134 baseEnd_3181134 := by
    simpa [prefixWord, tailWord_3181134, baseEnd_3181134] using wordTrace_append hprefix tailTrace_3181134
  have hstable : (prefixWord ++ tailWord_3181134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181134).length < 2 ^ (prefixWord ++ tailWord_3181134).sum := by decide
  have hdescent : baseEnd_3181134 < baseStart_3181134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181148 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3181148 : Nat := 118140960795 + 3181148 * 2 ^ 59
def prefixEnd_3181148 : Nat := 4983230072969 + 3 ^ 40 * 3181148 * 2
def baseEnd_3181148 : Nat := 544485985696341659173391

theorem tailTrace_3181148 : CollatzResearch.WordTrace tailWord_3181148 prefixEnd_3181148 544485985696341659173391 := by
  unfold tailWord_3181148
  simp only [CollatzResearch.WordTrace]
  refine ⟨58012999739625783834720049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77350666319501045112960065 58012999739625783834720049)
  ·
    refine ⟨43509749804719337876040037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58012999739625783834720049 43509749804719337876040037)
    ·
      refine ⟨8158078088384875851757507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43509749804719337876040037 8158078088384875851757507)
      ·
        refine ⟨12237117132577313777636261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8158078088384875851757507 12237117132577313777636261)
        ·
          refine ⟨2294459462358246333306799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12237117132577313777636261 2294459462358246333306799)
          ·
            refine ⟨3441689193537369499960199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294459462358246333306799 3441689193537369499960199)
            ·
              refine ⟨5162533790306054249940299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441689193537369499960199 5162533790306054249940299)
              ·
                refine ⟨7743800685459081374910449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162533790306054249940299 7743800685459081374910449)
                ·
                  refine ⟨5807850514094311031182837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743800685459081374910449 5807850514094311031182837)
                  ·
                    refine ⟨544485985696341659173391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807850514094311031182837 544485985696341659173391)
                    ·
                      rfl

theorem cell23_3181148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3181148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181148 prefixEnd_3181148 := by exact prefixLift 3181148
  have htrace : WordTrace (prefixWord ++ tailWord_3181148) baseStart_3181148 baseEnd_3181148 := by
    simpa [prefixWord, tailWord_3181148, baseEnd_3181148] using wordTrace_append hprefix tailTrace_3181148
  have hstable : (prefixWord ++ tailWord_3181148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181148).length < 2 ^ (prefixWord ++ tailWord_3181148).sum := by decide
  have hdescent : baseEnd_3181148 < baseStart_3181148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181177 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3181177 : Nat := 118140960795 + 3181177 * 2 ^ 59
def prefixEnd_3181177 : Nat := 4983230072969 + 3 ^ 40 * 3181177 * 2
def baseEnd_3181177 : Nat := 1633472848028005364057539

theorem tailTrace_3181177 : CollatzResearch.WordTrace tailWord_3181177 prefixEnd_3181177 1633472848028005364057539 := by
  unfold tailWord_3181177
  simp only [CollatzResearch.WordTrace]
  refine ⟨116027057196146505622245785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77351371464097670414830523 116027057196146505622245785)
  ·
    refine ⟨87020292897109879216684339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116027057196146505622245785 87020292897109879216684339)
    ·
      refine ⟨130530439345664818825026509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87020292897109879216684339 130530439345664818825026509)
      ·
        refine ⟨48948914754624307059384941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130530439345664818825026509 48948914754624307059384941)
        ·
          refine ⟨18355843032984115147269353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48948914754624307059384941 18355843032984115147269353)
          ·
            refine ⟨13766882274738086360452015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18355843032984115147269353 13766882274738086360452015)
            ·
              refine ⟨20650323412107129540678023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13766882274738086360452015 20650323412107129540678023)
              ·
                refine ⟨30975485118160694311017035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20650323412107129540678023 30975485118160694311017035)
                ·
                  refine ⟨46463227677241041466525553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30975485118160694311017035 46463227677241041466525553)
                  ·
                    refine ⟨34847420757930781099894165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46463227677241041466525553 34847420757930781099894165)
                    ·
                      refine ⟨1633472848028005364057539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34847420757930781099894165 1633472848028005364057539)
                      ·
                        rfl

theorem cell23_3181177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3181177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181177 prefixEnd_3181177 := by exact prefixLift 3181177
  have htrace : WordTrace (prefixWord ++ tailWord_3181177) baseStart_3181177 baseEnd_3181177 := by
    simpa [prefixWord, tailWord_3181177, baseEnd_3181177] using wordTrace_append hprefix tailTrace_3181177
  have hstable : (prefixWord ++ tailWord_3181177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181177).length < 2 ^ (prefixWord ++ tailWord_3181177).sum := by decide
  have hdescent : baseEnd_3181177 < baseStart_3181177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181187 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 5, 5]
def baseStart_3181187 : Nat := 118140960795 + 3181187 * 2 ^ 59
def prefixEnd_3181187 : Nat := 4983230072969 + 3 ^ 40 * 3181187 * 2
def baseEnd_3181187 : Nat := 544492660944850108310831

theorem tailTrace_3181187 : CollatzResearch.WordTrace tailWord_3181187 prefixEnd_3181187 544492660944850108310831 := by
  unfold tailWord_3181187
  simp only [CollatzResearch.WordTrace]
  refine ⟨116027421926110277330109815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77351614617406851553406543 116027421926110277330109815)
  ·
    refine ⟨174041132889165415995164723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116027421926110277330109815 174041132889165415995164723)
    ·
      refine ⟨261061699333748123992747085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174041132889165415995164723 261061699333748123992747085)
      ·
        refine ⟨97898137250155546497280157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261061699333748123992747085 97898137250155546497280157)
        ·
          refine ⟨36711801468808329936480059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97898137250155546497280157 36711801468808329936480059)
          ·
            refine ⟨55067702203212494904720089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36711801468808329936480059 55067702203212494904720089)
            ·
              refine ⟨41300776652409371178540067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55067702203212494904720089 41300776652409371178540067)
              ·
                refine ⟨61951164978614056767810101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41300776652409371178540067 61951164978614056767810101)
                ·
                  refine ⟨5807921716745067821982197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61951164978614056767810101 5807921716745067821982197)
                  ·
                    refine ⟨544492660944850108310831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5807921716745067821982197 544492660944850108310831)
                    ·
                      rfl

theorem cell23_3181187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].length) (baseStart_3181187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181187 prefixEnd_3181187 := by exact prefixLift 3181187
  have htrace : WordTrace (prefixWord ++ tailWord_3181187) baseStart_3181187 baseEnd_3181187 := by
    simpa [prefixWord, tailWord_3181187, baseEnd_3181187] using wordTrace_append hprefix tailTrace_3181187
  have hstable : (prefixWord ++ tailWord_3181187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181187).length < 2 ^ (prefixWord ++ tailWord_3181187).sum := by decide
  have hdescent : baseEnd_3181187 < baseStart_3181187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181235 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 1, 1, 3]
def baseStart_3181235 : Nat := 118140960795 + 3181235 * 2 ^ 59
def prefixEnd_3181235 : Nat := 4983230072969 + 3 ^ 40 * 3181235 * 2
def baseEnd_3181235 : Nat := 1633502629905966137132273

theorem tailTrace_3181235 : CollatzResearch.WordTrace tailWord_3181235 prefixEnd_3181235 1633502629905966137132273 := by
  unfold tailWord_3181235
  simp only [CollatzResearch.WordTrace]
  refine ⟨116029172629936381527857159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77352781753290921018571439 116029172629936381527857159)
  ·
    refine ⟨174043758944904572291785739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116029172629936381527857159 174043758944904572291785739)
    ·
      refine ⟨261065638417356858437678609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174043758944904572291785739 261065638417356858437678609)
      ·
        refine ⟨195799228813017643828258957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261065638417356858437678609 195799228813017643828258957)
        ·
          refine ⟨73424710804881616435597109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195799228813017643828258957 73424710804881616435597109)
          ·
            refine ⟨6883566637957651540837229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73424710804881616435597109 6883566637957651540837229)
            ·
              refine ⟨2581337489234119327813961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6883566637957651540837229 2581337489234119327813961)
              ·
                refine ⟨1936003116925589495860471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581337489234119327813961 1936003116925589495860471)
                ·
                  refine ⟨2904004675388384243790707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936003116925589495860471 2904004675388384243790707)
                  ·
                    refine ⟨4356007013082576365686061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904004675388384243790707 4356007013082576365686061)
                    ·
                      refine ⟨1633502629905966137132273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356007013082576365686061 1633502629905966137132273)
                      ·
                        rfl

theorem cell23_3181235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 1, 3].length) (baseStart_3181235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181235 prefixEnd_3181235 := by exact prefixLift 3181235
  have htrace : WordTrace (prefixWord ++ tailWord_3181235) baseStart_3181235 baseEnd_3181235 := by
    simpa [prefixWord, tailWord_3181235, baseEnd_3181235] using wordTrace_append hprefix tailTrace_3181235
  have hstable : (prefixWord ++ tailWord_3181235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181235).length < 2 ^ (prefixWord ++ tailWord_3181235).sum := by decide
  have hdescent : baseEnd_3181235 < baseStart_3181235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181244 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3181244 : Nat := 118140960795 + 3181244 * 2 ^ 59
def prefixEnd_3181244 : Nat := 4983230072969 + 3 ^ 40 * 3181244 * 2
def baseEnd_3181244 : Nat := 1633507251231856601919731

theorem tailTrace_3181244 : CollatzResearch.WordTrace tailWord_3181244 prefixEnd_3181244 1633507251231856601919731 := by
  unfold tailWord_3181244
  simp only [CollatzResearch.WordTrace]
  refine ⟨58014750443451888032467393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77353000591269184043289857 58014750443451888032467393)
  ·
    refine ⟨43511062832588916024350545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58014750443451888032467393 43511062832588916024350545)
    ·
      refine ⟨32633297124441687018262909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43511062832588916024350545 32633297124441687018262909)
      ·
        refine ⟨12237486421665632631848591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32633297124441687018262909 12237486421665632631848591)
        ·
          refine ⟨18356229632498448947772887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12237486421665632631848591 18356229632498448947772887)
          ·
            refine ⟨27534344448747673421659331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18356229632498448947772887 27534344448747673421659331)
            ·
              refine ⟨41301516673121510132488997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27534344448747673421659331 41301516673121510132488997)
              ·
                refine ⟨7744034376210283149841687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41301516673121510132488997 7744034376210283149841687)
                ·
                  refine ⟨11616051564315424724762531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744034376210283149841687 11616051564315424724762531)
                  ·
                    refine ⟨17424077346473137087143797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11616051564315424724762531 17424077346473137087143797)
                    ·
                      refine ⟨1633507251231856601919731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17424077346473137087143797 1633507251231856601919731)
                      ·
                        rfl

theorem cell23_3181244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3181244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181244 prefixEnd_3181244 := by exact prefixLift 3181244
  have htrace : WordTrace (prefixWord ++ tailWord_3181244) baseStart_3181244 baseEnd_3181244 := by
    simpa [prefixWord, tailWord_3181244, baseEnd_3181244] using wordTrace_append hprefix tailTrace_3181244
  have hstable : (prefixWord ++ tailWord_3181244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181244).length < 2 ^ (prefixWord ++ tailWord_3181244).sum := by decide
  have hdescent : baseEnd_3181244 < baseStart_3181244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181247 : List Nat := [1, 1, 2, 2, 2, 4, 1, 10]
def baseStart_3181247 : Nat := 118140960795 + 3181247 * 2 ^ 59
def prefixEnd_3181247 : Nat := 4983230072969 + 3 ^ 40 * 3181247 * 2
def baseEnd_3181247 : Nat := 60500325617548892228971

theorem tailTrace_3181247 : CollatzResearch.WordTrace tailWord_3181247 prefixEnd_3181247 60500325617548892228971 := by
  unfold tailWord_3181247
  simp only [CollatzResearch.WordTrace]
  refine ⟨116029610305892907577293995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77353073537261938384862663 116029610305892907577293995)
  ·
    refine ⟨174044415458839361365940993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116029610305892907577293995 174044415458839361365940993)
    ·
      refine ⟨130533311594129521024455745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174044415458839361365940993 130533311594129521024455745)
      ·
        refine ⟨97899983695597140768341809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130533311594129521024455745 97899983695597140768341809)
        ·
          refine ⟨73424987771697855576256357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97899983695597140768341809 73424987771697855576256357)
          ·
            refine ⟨13767185207193347920548067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73424987771697855576256357 13767185207193347920548067)
            ·
              refine ⟨20650777810790021880822101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13767185207193347920548067 20650777810790021880822101)
              ·
                refine ⟨60500325617548892228971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20650777810790021880822101 60500325617548892228971)
                ·
                  rfl

theorem cell23_3181247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 10].length) (baseStart_3181247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181247 prefixEnd_3181247 := by exact prefixLift 3181247
  have htrace : WordTrace (prefixWord ++ tailWord_3181247) baseStart_3181247 baseEnd_3181247 := by
    simpa [prefixWord, tailWord_3181247, baseEnd_3181247] using wordTrace_append hprefix tailTrace_3181247
  have hstable : (prefixWord ++ tailWord_3181247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181247).length < 2 ^ (prefixWord ++ tailWord_3181247).sum := by decide
  have hdescent : baseEnd_3181247 < baseStart_3181247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181258 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3181258 : Nat := 118140960795 + 3181258 * 2 ^ 59
def prefixEnd_3181258 : Nat := 4983230072969 + 3 ^ 40 * 3181258 * 2
def baseEnd_3181258 : Nat := 1633514439961019547144667

theorem tailTrace_3181258 : CollatzResearch.WordTrace tailWord_3181258 prefixEnd_3181258 1633514439961019547144667 := by
  unfold tailWord_3181258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29007502877213264113986107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77353341005902037637296285 29007502877213264113986107)
  ·
    refine ⟨43511254315819896170979161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29007502877213264113986107 43511254315819896170979161)
    ·
      refine ⟨32633440736864922128234371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43511254315819896170979161 32633440736864922128234371)
      ·
        refine ⟨48950161105297383192351557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633440736864922128234371 48950161105297383192351557)
        ·
          refine ⟨9178155207243259348565917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48950161105297383192351557 9178155207243259348565917)
          ·
            refine ⟨3441808202716222255712219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9178155207243259348565917 3441808202716222255712219)
            ·
              refine ⟨5162712304074333383568329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441808202716222255712219 5162712304074333383568329)
              ·
                refine ⟨3872034228055750037676247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162712304074333383568329 3872034228055750037676247)
                ·
                  refine ⟨5808051342083625056514371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872034228055750037676247 5808051342083625056514371)
                  ·
                    refine ⟨8712077013125437584771557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5808051342083625056514371 8712077013125437584771557)
                    ·
                      refine ⟨1633514439961019547144667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8712077013125437584771557 1633514439961019547144667)
                      ·
                        rfl

theorem cell23_3181258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3181258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181258 prefixEnd_3181258 := by exact prefixLift 3181258
  have htrace : WordTrace (prefixWord ++ tailWord_3181258) baseStart_3181258 baseEnd_3181258 := by
    simpa [prefixWord, tailWord_3181258, baseEnd_3181258] using wordTrace_append hprefix tailTrace_3181258
  have hstable : (prefixWord ++ tailWord_3181258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181258).length < 2 ^ (prefixWord ++ tailWord_3181258).sum := by decide
  have hdescent : baseEnd_3181258 < baseStart_3181258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181294 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3181294 : Nat := 118140960795 + 3181294 * 2 ^ 59
def prefixEnd_3181294 : Nat := 4983230072969 + 3 ^ 40 * 3181294 * 2
def baseEnd_3181294 : Nat := 544510975088193802098167

theorem tailTrace_3181294 : CollatzResearch.WordTrace tailWord_3181294 prefixEnd_3181294 544510975088193802098167 := by
  unfold tailWord_3181294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503915567090329325531867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77354216357815089736169957 14503915567090329325531867)
  ·
    refine ⟨21755873350635493988297801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14503915567090329325531867 21755873350635493988297801)
    ·
      refine ⟨16316905012976620491223351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21755873350635493988297801 16316905012976620491223351)
      ·
        refine ⟨24475357519464930736835027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316905012976620491223351 24475357519464930736835027)
        ·
          refine ⟨36713036279197396105252541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24475357519464930736835027 36713036279197396105252541)
          ·
            refine ⟨13767388604699023539469703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36713036279197396105252541 13767388604699023539469703)
            ·
              refine ⟨20651082907048535309204555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13767388604699023539469703 20651082907048535309204555)
              ·
                refine ⟨30976624360572802963806833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20651082907048535309204555 30976624360572802963806833)
                ·
                  refine ⟨23232468270429602222855125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30976624360572802963806833 23232468270429602222855125)
                  ·
                    refine ⟨544510975088193802098167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23232468270429602222855125 544510975088193802098167)
                    ·
                      rfl

theorem cell23_3181294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3181294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181294 prefixEnd_3181294 := by exact prefixLift 3181294
  have htrace : WordTrace (prefixWord ++ tailWord_3181294) baseStart_3181294 baseEnd_3181294 := by
    simpa [prefixWord, tailWord_3181294, baseEnd_3181294] using wordTrace_append hprefix tailTrace_3181294
  have hstable : (prefixWord ++ tailWord_3181294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181294).length < 2 ^ (prefixWord ++ tailWord_3181294).sum := by decide
  have hdescent : baseEnd_3181294 < baseStart_3181294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181308 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_3181308 : Nat := 118140960795 + 3181308 * 2 ^ 59
def prefixEnd_3181308 : Nat := 4983230072969 + 3 ^ 40 * 3181308 * 2
def baseEnd_3181308 : Nat := 1633540113993744351519437

theorem tailTrace_3181308 : CollatzResearch.WordTrace tailWord_3181308 prefixEnd_3181308 1633540113993744351519437 := by
  unfold tailWord_3181308
  simp only [CollatzResearch.WordTrace]
  refine ⟨58015917579335957497632289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77354556772447943330176385 58015917579335957497632289)
  ·
    refine ⟨43511938184501968123224217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58015917579335957497632289 43511938184501968123224217)
    ·
      refine ⟨32633953638376476092418163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43511938184501968123224217 32633953638376476092418163)
      ·
        refine ⟨48950930457564714138627245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633953638376476092418163 48950930457564714138627245)
        ·
          refine ⟨18356598921586767801985217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48950930457564714138627245 18356598921586767801985217)
          ·
            refine ⟨13767449191190075851488913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18356598921586767801985217 13767449191190075851488913)
            ·
              refine ⟨10325586893392556888616685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767449191190075851488913 10325586893392556888616685)
              ·
                refine ⟨3872095085022208833231257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10325586893392556888616685 3872095085022208833231257)
                ·
                  refine ⟨2904071313766656624923443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872095085022208833231257 2904071313766656624923443)
                  ·
                    refine ⟨4356106970649984937385165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904071313766656624923443 4356106970649984937385165)
                    ·
                      refine ⟨1633540113993744351519437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356106970649984937385165 1633540113993744351519437)
                      ·
                        rfl

theorem cell23_3181308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_3181308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181308 prefixEnd_3181308 := by exact prefixLift 3181308
  have htrace : WordTrace (prefixWord ++ tailWord_3181308) baseStart_3181308 baseEnd_3181308 := by
    simpa [prefixWord, tailWord_3181308, baseEnd_3181308] using wordTrace_append hprefix tailTrace_3181308
  have hstable : (prefixWord ++ tailWord_3181308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181308).length < 2 ^ (prefixWord ++ tailWord_3181308).sum := by decide
  have hdescent : baseEnd_3181308 < baseStart_3181308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181331 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 1, 4, 2]
def baseStart_3181331 : Nat := 118140960795 + 3181331 * 2 ^ 59
def prefixEnd_3181331 : Nat := 4983230072969 + 3 ^ 40 * 3181331 * 2
def baseEnd_3181331 : Nat := 1633551924048797761531831

theorem tailTrace_3181331 : CollatzResearch.WordTrace tailWord_3181331 prefixEnd_3181331 1633551924048797761531831 := by
  unfold tailWord_3181331
  simp only [CollatzResearch.WordTrace]
  refine ⟨116032674037588589923351847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77355116025059059948901231 116032674037588589923351847)
  ·
    refine ⟨174049011056382884885027771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116032674037588589923351847 174049011056382884885027771)
    ·
      refine ⟨261073516584574327327541657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174049011056382884885027771 261073516584574327327541657)
      ·
        refine ⟨195805137438430745495656243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261073516584574327327541657 195805137438430745495656243)
        ·
          refine ⟨293707706157646118243484365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195805137438430745495656243 293707706157646118243484365)
          ·
            refine ⟨110140389809117294341306637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293707706157646118243484365 110140389809117294341306637)
            ·
              refine ⟨41302646178418985377989989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110140389809117294341306637 41302646178418985377989989)
              ·
                refine ⟨7744246158453559758373123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41302646178418985377989989 7744246158453559758373123)
                ·
                  refine ⟨11616369237680339637559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744246158453559758373123 11616369237680339637559685)
                  ·
                    refine ⟨2178069232065063682042441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11616369237680339637559685 2178069232065063682042441)
                    ·
                      refine ⟨1633551924048797761531831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178069232065063682042441 1633551924048797761531831)
                      ·
                        rfl

theorem cell23_3181331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 4, 2].length) (baseStart_3181331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181331 prefixEnd_3181331 := by exact prefixLift 3181331
  have htrace : WordTrace (prefixWord ++ tailWord_3181331) baseStart_3181331 baseEnd_3181331 := by
    simpa [prefixWord, tailWord_3181331, baseEnd_3181331] using wordTrace_append hprefix tailTrace_3181331
  have hstable : (prefixWord ++ tailWord_3181331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181331).length < 2 ^ (prefixWord ++ tailWord_3181331).sum := by decide
  have hdescent : baseEnd_3181331 < baseStart_3181331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181335 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_3181335 : Nat := 118140960795 + 3181335 * 2 ^ 59
def prefixEnd_3181335 : Nat := 4983230072969 + 3 ^ 40 * 3181335 * 2
def baseEnd_3181335 : Nat := 1633553977971415745881813

theorem tailTrace_3181335 : CollatzResearch.WordTrace tailWord_3181335 prefixEnd_3181335 1633553977971415745881813 := by
  unfold tailWord_3181335
  simp only [CollatzResearch.WordTrace]
  refine ⟨116032819929574098606497459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77355213286382732404331639 116032819929574098606497459)
  ·
    refine ⟨174049229894361147909746189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116032819929574098606497459 174049229894361147909746189)
    ·
      refine ⟨65268461210385430466154821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174049229894361147909746189 65268461210385430466154821)
      ·
        refine ⟨12237836476947268212404029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65268461210385430466154821 12237836476947268212404029)
        ·
          refine ⟨4589188678855225579651511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12237836476947268212404029 4589188678855225579651511)
          ·
            refine ⟨6883783018282838369477267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589188678855225579651511 6883783018282838369477267)
            ·
              refine ⟨10325674527424257554215901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883783018282838369477267 10325674527424257554215901)
              ·
                refine ⟨3872127947784096582830963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10325674527424257554215901 3872127947784096582830963)
                ·
                  refine ⟨5808191921676144874246445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872127947784096582830963 5808191921676144874246445)
                  ·
                    refine ⟨2178071970628554327842417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5808191921676144874246445 2178071970628554327842417)
                    ·
                      refine ⟨1633553977971415745881813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178071970628554327842417 1633553977971415745881813)
                      ·
                        rfl

theorem cell23_3181335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_3181335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181335 prefixEnd_3181335 := by exact prefixLift 3181335
  have htrace : WordTrace (prefixWord ++ tailWord_3181335) baseStart_3181335 baseEnd_3181335 := by
    simpa [prefixWord, tailWord_3181335, baseEnd_3181335] using wordTrace_append hprefix tailTrace_3181335
  have hstable : (prefixWord ++ tailWord_3181335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181335).length < 2 ^ (prefixWord ++ tailWord_3181335).sum := by decide
  have hdescent : baseEnd_3181335 < baseStart_3181335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181365 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_3181365 : Nat := 118140960795 + 3181365 * 2 ^ 59
def prefixEnd_3181365 : Nat := 4983230072969 + 3 ^ 40 * 3181365 * 2
def baseEnd_3181365 : Nat := 1633569382391050628506675

theorem tailTrace_3181365 : CollatzResearch.WordTrace tailWord_3181365 prefixEnd_3181365 1633569382391050628506675 := by
  unfold tailWord_3181365
  simp only [CollatzResearch.WordTrace]
  refine ⟨116033914119465413730089549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77355942746310275820059699 116033914119465413730089549)
  ·
    refine ⟨43512717794799530148783581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116033914119465413730089549 43512717794799530148783581)
    ·
      refine ⟨16317269173049823805793843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43512717794799530148783581 16317269173049823805793843)
      ·
        refine ⟨24475903759574735708690765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16317269173049823805793843 24475903759574735708690765)
        ·
          refine ⟨9178463909840525890759037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24475903759574735708690765 9178463909840525890759037)
          ·
            refine ⟨3441923966190197209034639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9178463909840525890759037 3441923966190197209034639)
            ·
              refine ⟨5162885949285295813551959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441923966190197209034639 5162885949285295813551959)
              ·
                refine ⟨7744328923927943720327939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162885949285295813551959 7744328923927943720327939)
                ·
                  refine ⟨11616493385891915580491909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744328923927943720327939 11616493385891915580491909)
                  ·
                    refine ⟨2178092509854734171342233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11616493385891915580491909 2178092509854734171342233)
                    ·
                      refine ⟨1633569382391050628506675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178092509854734171342233 1633569382391050628506675)
                      ·
                        rfl

theorem cell23_3181365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_3181365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181365 prefixEnd_3181365 := by exact prefixLift 3181365
  have htrace : WordTrace (prefixWord ++ tailWord_3181365) baseStart_3181365 baseEnd_3181365 := by
    simpa [prefixWord, tailWord_3181365, baseEnd_3181365] using wordTrace_append hprefix tailTrace_3181365
  have hstable : (prefixWord ++ tailWord_3181365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181365).length < 2 ^ (prefixWord ++ tailWord_3181365).sum := by decide
  have hdescent : baseEnd_3181365 < baseStart_3181365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181384 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_3181384 : Nat := 118140960795 + 3181384 * 2 ^ 59
def prefixEnd_3181384 : Nat := 4983230072969 + 3 ^ 40 * 3181384 * 2
def baseEnd_3181384 : Nat := 544526379507828684723029

theorem tailTrace_3181384 : CollatzResearch.WordTrace tailWord_3181384 prefixEnd_3181384 544526379507828684723029 := by
  unfold tailWord_3181384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58017303553198289987515603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77356404737597719983354137 58017303553198289987515603)
  ·
    refine ⟨87025955329797434981273405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58017303553198289987515603 87025955329797434981273405)
    ·
      refine ⟨32634733248674038117977527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87025955329797434981273405 32634733248674038117977527)
      ·
        refine ⟨48952099873011057176966291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32634733248674038117977527 48952099873011057176966291)
        ·
          refine ⟨73428149809516585765449437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48952099873011057176966291 73428149809516585765449437)
          ·
            refine ⟨27535556178568719662043539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73428149809516585765449437 27535556178568719662043539)
            ·
              refine ⟨41303334267853079493065309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27535556178568719662043539 41303334267853079493065309)
              ·
                refine ⟨15488750350444904809899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41303334267853079493065309 15488750350444904809899491)
                ·
                  refine ⟨23233125525667357214849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15488750350444904809899491 23233125525667357214849237)
                  ·
                    refine ⟨544526379507828684723029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23233125525667357214849237 544526379507828684723029)
                    ·
                      rfl

theorem cell23_3181384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_3181384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181384 prefixEnd_3181384 := by exact prefixLift 3181384
  have htrace : WordTrace (prefixWord ++ tailWord_3181384) baseStart_3181384 baseEnd_3181384 := by
    simpa [prefixWord, tailWord_3181384, baseEnd_3181384] using wordTrace_append hprefix tailTrace_3181384
  have hstable : (prefixWord ++ tailWord_3181384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181384).length < 2 ^ (prefixWord ++ tailWord_3181384).sum := by decide
  have hdescent : baseEnd_3181384 < baseStart_3181384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181388 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 5]
def baseStart_3181388 : Nat := 118140960795 + 3181388 * 2 ^ 59
def prefixEnd_3181388 : Nat := 4983230072969 + 3 ^ 40 * 3181388 * 2
def baseEnd_3181388 : Nat := 181509021382900448724341

theorem tailTrace_3181388 : CollatzResearch.WordTrace tailWord_3181388 prefixEnd_3181388 181509021382900448724341 := by
  unfold tailWord_3181388
  simp only [CollatzResearch.WordTrace]
  refine ⟨58017376499191044329088409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77356501998921392438784545 58017376499191044329088409)
  ·
    refine ⟨43513032374393283246816307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58017376499191044329088409 43513032374393283246816307)
    ·
      refine ⟨65269548561589924870224461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43513032374393283246816307 65269548561589924870224461)
      ·
        refine ⟨24476080710596221826334173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65269548561589924870224461 24476080710596221826334173)
        ·
          refine ⟨9178530266473583184875315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24476080710596221826334173 9178530266473583184875315)
          ·
            refine ⟨13767795399710374777312973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178530266473583184875315 13767795399710374777312973)
            ·
              refine ⟨5162923274891390541492365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13767795399710374777312973 5162923274891390541492365)
              ·
                refine ⟨1936096228084271453059637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5162923274891390541492365 1936096228084271453059637)
                ·
                  refine ⟨181509021382900448724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936096228084271453059637 181509021382900448724341)
                  ·
                    rfl

theorem cell23_3181388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_3181388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181388 prefixEnd_3181388 := by exact prefixLift 3181388
  have htrace : WordTrace (prefixWord ++ tailWord_3181388) baseStart_3181388 baseEnd_3181388 := by
    simpa [prefixWord, tailWord_3181388, baseEnd_3181388] using wordTrace_append hprefix tailTrace_3181388
  have hstable : (prefixWord ++ tailWord_3181388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181388).length < 2 ^ (prefixWord ++ tailWord_3181388).sum := by decide
  have hdescent : baseEnd_3181388 < baseStart_3181388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181401 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_3181401 : Nat := 118140960795 + 3181401 * 2 ^ 59
def prefixEnd_3181401 : Nat := 4983230072969 + 3 ^ 40 * 3181401 * 2
def baseEnd_3181401 : Nat := 544529289231537495885503

theorem tailTrace_3181401 : CollatzResearch.WordTrace tailWord_3181401 prefixEnd_3181401 544529289231537495885503 := by
  unfold tailWord_3181401
  simp only [CollatzResearch.WordTrace]
  refine ⟨116035227147334991878400057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77356818098223327918933371 116035227147334991878400057)
  ·
    refine ⟨87026420360501243908800043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116035227147334991878400057 87026420360501243908800043)
    ·
      refine ⟨130539630540751865863200065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87026420360501243908800043 130539630540751865863200065)
      ·
        refine ⟨97904722905563899397400049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130539630540751865863200065 97904722905563899397400049)
        ·
          refine ⟨73428542179172924548050037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97904722905563899397400049 73428542179172924548050037)
          ·
            refine ⟨6883925829297461676379691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73428542179172924548050037 6883925829297461676379691)
            ·
              refine ⟨10325888743946192514569537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883925829297461676379691 10325888743946192514569537)
              ·
                refine ⟨7744416557959644385927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10325888743946192514569537 7744416557959644385927153)
                ·
                  refine ⟨5808312418469733289445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744416557959644385927153 5808312418469733289445365)
                  ·
                    refine ⟨544529289231537495885503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5808312418469733289445365 544529289231537495885503)
                    ·
                      rfl

theorem cell23_3181401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_3181401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181401 prefixEnd_3181401 := by exact prefixLift 3181401
  have htrace : WordTrace (prefixWord ++ tailWord_3181401) baseStart_3181401 baseEnd_3181401 := by
    simpa [prefixWord, tailWord_3181401, baseEnd_3181401] using wordTrace_append hprefix tailTrace_3181401
  have hstable : (prefixWord ++ tailWord_3181401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181401).length < 2 ^ (prefixWord ++ tailWord_3181401).sum := by decide
  have hdescent : baseEnd_3181401 < baseStart_3181401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181411 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3181411 : Nat := 118140960795 + 3181411 * 2 ^ 59
def prefixEnd_3181411 : Nat := 4983230072969 + 3 ^ 40 * 3181411 * 2
def baseEnd_3181411 : Nat := 1633593002501157448531463

theorem tailTrace_3181411 : CollatzResearch.WordTrace tailWord_3181411 prefixEnd_3181411 1633593002501157448531463 := by
  unfold tailWord_3181411
  simp only [CollatzResearch.WordTrace]
  refine ⟨116035591877298763586264087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77357061251532509057509391 116035591877298763586264087)
  ·
    refine ⟨174053387815948145379396131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116035591877298763586264087 174053387815948145379396131)
    ·
      refine ⟨261080081723922218069094197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174053387815948145379396131 261080081723922218069094197)
      ·
        refine ⟨24476257661617707943977581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261080081723922218069094197 24476257661617707943977581)
        ·
          refine ⟨9178596623106640478991593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24476257661617707943977581 9178596623106640478991593)
          ·
            refine ⟨6883947467329980359243695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178596623106640478991593 6883947467329980359243695)
            ·
              refine ⟨10325921200994970538865543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883947467329980359243695 10325921200994970538865543)
              ·
                refine ⟨15488881801492455808298315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325921200994970538865543 15488881801492455808298315)
                ·
                  refine ⟨23233322702238683712447473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15488881801492455808298315 23233322702238683712447473)
                  ·
                    refine ⟨17424992026679012784335605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23233322702238683712447473 17424992026679012784335605)
                    ·
                      refine ⟨1633593002501157448531463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17424992026679012784335605 1633593002501157448531463)
                      ·
                        rfl

theorem cell23_3181411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3181411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181411 prefixEnd_3181411 := by exact prefixLift 3181411
  have htrace : WordTrace (prefixWord ++ tailWord_3181411) baseStart_3181411 baseEnd_3181411 := by
    simpa [prefixWord, tailWord_3181411, baseEnd_3181411] using wordTrace_append hprefix tailTrace_3181411
  have hstable : (prefixWord ++ tailWord_3181411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181411).length < 2 ^ (prefixWord ++ tailWord_3181411).sum := by decide
  have hdescent : baseEnd_3181411 < baseStart_3181411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181421 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3181421 : Nat := 118140960795 + 3181421 * 2 ^ 59
def prefixEnd_3181421 : Nat := 4983230072969 + 3 ^ 40 * 3181421 * 2
def baseEnd_3181421 : Nat := 1633598137307702409406417

theorem tailTrace_3181421 : CollatzResearch.WordTrace tailWord_3181421 prefixEnd_3181421 1633598137307702409406417 := by
  unfold tailWord_3181421
  simp only [CollatzResearch.WordTrace]
  refine ⟨116035956607262535294128117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77357304404841690196085411 116035956607262535294128117)
  ·
    refine ⟨10878370931930862683824511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116035956607262535294128117 10878370931930862683824511)
    ·
      refine ⟨16317556397896294025736767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10878370931930862683824511 16317556397896294025736767)
      ·
        refine ⟨24476334596844441038605151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16317556397896294025736767 24476334596844441038605151)
        ·
          refine ⟨36714501895266661557907727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24476334596844441038605151 36714501895266661557907727)
          ·
            refine ⟨55071752842899992336861591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36714501895266661557907727 55071752842899992336861591)
            ·
              refine ⟨82607629264349988505292387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55071752842899992336861591 82607629264349988505292387)
              ·
                refine ⟨123911443896524982757938581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82607629264349988505292387 123911443896524982757938581)
                ·
                  refine ⟨5808348932649608566778371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123911443896524982757938581 5808348932649608566778371)
                  ·
                    refine ⟨8712523398974412850167557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5808348932649608566778371 8712523398974412850167557)
                    ·
                      refine ⟨1633598137307702409406417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8712523398974412850167557 1633598137307702409406417)
                      ·
                        rfl

theorem cell23_3181421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3181421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181421 prefixEnd_3181421 := by exact prefixLift 3181421
  have htrace : WordTrace (prefixWord ++ tailWord_3181421) baseStart_3181421 baseEnd_3181421 := by
    simpa [prefixWord, tailWord_3181421, baseEnd_3181421] using wordTrace_append hprefix tailTrace_3181421
  have hstable : (prefixWord ++ tailWord_3181421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181421).length < 2 ^ (prefixWord ++ tailWord_3181421).sum := by decide
  have hdescent : baseEnd_3181421 < baseStart_3181421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181431 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 3, 4]
def baseStart_3181431 : Nat := 118140960795 + 3181431 * 2 ^ 59
def prefixEnd_3181431 : Nat := 4983230072969 + 3 ^ 40 * 3181431 * 2
def baseEnd_3181431 : Nat := 544534424038082456760457

theorem tailTrace_3181431 : CollatzResearch.WordTrace tailWord_3181431 prefixEnd_3181431 544534424038082456760457 := by
  unfold tailWord_3181431
  simp only [CollatzResearch.WordTrace]
  refine ⟨116036321337226307001992147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77357547558150871334661431 116036321337226307001992147)
  ·
    refine ⟨174054482005839460502988221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116036321337226307001992147 174054482005839460502988221)
    ·
      refine ⟨65270430752189797688620583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174054482005839460502988221 65270430752189797688620583)
      ·
        refine ⟨97905646128284696532930875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65270430752189797688620583 97905646128284696532930875)
        ·
          refine ⟨146858469192427044799396313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97905646128284696532930875 146858469192427044799396313)
          ·
            refine ⟨110143851894320283599547235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146858469192427044799396313 110143851894320283599547235)
            ·
              refine ⟨165215777841480425399320853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110143851894320283599547235 165215777841480425399320853)
              ·
                refine ⟨7744489586319394940593165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165215777841480425399320853 7744489586319394940593165)
                ·
                  refine ⟨2904183594869773102722437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7744489586319394940593165 2904183594869773102722437)
                  ·
                    refine ⟨544534424038082456760457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2904183594869773102722437 544534424038082456760457)
                    ·
                      rfl

theorem cell23_3181431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_3181431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181431 prefixEnd_3181431 := by exact prefixLift 3181431
  have htrace : WordTrace (prefixWord ++ tailWord_3181431) baseStart_3181431 baseEnd_3181431 := by
    simpa [prefixWord, tailWord_3181431, baseEnd_3181431] using wordTrace_append hprefix tailTrace_3181431
  have hstable : (prefixWord ++ tailWord_3181431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181431).length < 2 ^ (prefixWord ++ tailWord_3181431).sum := by decide
  have hdescent : baseEnd_3181431 < baseStart_3181431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181434 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3181434 : Nat := 118140960795 + 3181434 * 2 ^ 59
def prefixEnd_3181434 : Nat := 4983230072969 + 3 ^ 40 * 3181434 * 2
def baseEnd_3181434 : Nat := 1633604812556210858543857

theorem tailTrace_3181434 : CollatzResearch.WordTrace tailWord_3181434 prefixEnd_3181434 1633604812556210858543857 := by
  unfold tailWord_3181434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009107689053859628587839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77357620504143625676234237 29009107689053859628587839)
  ·
    refine ⟨43513661533580789442881759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29009107689053859628587839 43513661533580789442881759)
    ·
      refine ⟨65270492300371184164322639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43513661533580789442881759 65270492300371184164322639)
      ·
        refine ⟨97905738450556776246483959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65270492300371184164322639 97905738450556776246483959)
        ·
          refine ⟨146858607675835164369725939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97905738450556776246483959 146858607675835164369725939)
          ·
            refine ⟨220287911513752746554588909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146858607675835164369725939 220287911513752746554588909)
            ·
              refine ⟨82607966817657279957970841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220287911513752746554588909 82607966817657279957970841)
              ·
                refine ⟨61955975113242959968478131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82607966817657279957970841 61955975113242959968478131)
                ·
                  refine ⟨92933962669864439952717197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61955975113242959968478131 92933962669864439952717197)
                  ·
                    refine ⟨34850236001199164982268949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92933962669864439952717197 34850236001199164982268949)
                    ·
                      refine ⟨1633604812556210858543857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34850236001199164982268949 1633604812556210858543857)
                      ·
                        rfl

theorem cell23_3181434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3181434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181434 prefixEnd_3181434 := by exact prefixLift 3181434
  have htrace : WordTrace (prefixWord ++ tailWord_3181434) baseStart_3181434 baseEnd_3181434 := by
    simpa [prefixWord, tailWord_3181434, baseEnd_3181434] using wordTrace_append hprefix tailTrace_3181434
  have hstable : (prefixWord ++ tailWord_3181434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181434).length < 2 ^ (prefixWord ++ tailWord_3181434).sum := by decide
  have hdescent : baseEnd_3181434 < baseStart_3181434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181461 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 6]
def baseStart_3181461 : Nat := 118140960795 + 3181461 * 2 ^ 59
def prefixEnd_3181461 : Nat := 4983230072969 + 3 ^ 40 * 3181461 * 2
def baseEnd_3181461 : Nat := 181513186281542472545137

theorem tailTrace_3181461 : CollatzResearch.WordTrace tailWord_3181461 prefixEnd_3181461 181513186281542472545137 := by
  unfold tailWord_3181461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116037415527117622125584237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77358277018078414750389491 116037415527117622125584237)
  ·
    refine ⟨43514030822669108297094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116037415527117622125584237 43514030822669108297094089)
    ·
      refine ⟨32635523117001831222820567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43514030822669108297094089 32635523117001831222820567)
      ·
        refine ⟨48953284675502746834230851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32635523117001831222820567 48953284675502746834230851)
        ·
          refine ⟨73429927013254120251346277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48953284675502746834230851 73429927013254120251346277)
          ·
            refine ⟨13768111314985147547127427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73429927013254120251346277 13768111314985147547127427)
            ·
              refine ⟨20652166972477721320691141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13768111314985147547127427 20652166972477721320691141)
              ·
                refine ⟨3872281307339572747629589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20652166972477721320691141 3872281307339572747629589)
                ·
                  refine ⟨181513186281542472545137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3872281307339572747629589 181513186281542472545137)
                  ·
                    rfl

theorem cell23_3181461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_3181461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181461 prefixEnd_3181461 := by exact prefixLift 3181461
  have htrace : WordTrace (prefixWord ++ tailWord_3181461) baseStart_3181461 baseEnd_3181461 := by
    simpa [prefixWord, tailWord_3181461, baseEnd_3181461] using wordTrace_append hprefix tailTrace_3181461
  have hstable : (prefixWord ++ tailWord_3181461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181461).length < 2 ^ (prefixWord ++ tailWord_3181461).sum := by decide
  have hdescent : baseEnd_3181461 < baseStart_3181461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181492 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3181492 : Nat := 118140960795 + 3181492 * 2 ^ 59
def prefixEnd_3181492 : Nat := 4983230072969 + 3 ^ 40 * 3181492 * 2
def baseEnd_3181492 : Nat := 1633634594434171631618591

theorem tailTrace_3181492 : CollatzResearch.WordTrace tailWord_3181492 prefixEnd_3181492 1633634594434171631618591 := by
  unfold tailWord_3181492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58019273095002657209981365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77359030793336876279975153 58019273095002657209981365)
  ·
    refine ⟨5439306852656499113435753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58019273095002657209981365 5439306852656499113435753)
    ·
      refine ⟨4079480139492374335076815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5439306852656499113435753 4079480139492374335076815)
      ·
        refine ⟨6119220209238561502615223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079480139492374335076815 6119220209238561502615223)
        ·
          refine ⟨9178830313857842253922835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119220209238561502615223 9178830313857842253922835)
          ·
            refine ⟨13768245470786763380884253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9178830313857842253922835 13768245470786763380884253)
            ·
              refine ⟨5163092051545036267831595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13768245470786763380884253 5163092051545036267831595)
              ·
                refine ⟨7744638077317554401747393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163092051545036267831595 7744638077317554401747393)
                ·
                  refine ⟨5808478557988165801310545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744638077317554401747393 5808478557988165801310545)
                  ·
                    refine ⟨4356358918491124350982909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5808478557988165801310545 4356358918491124350982909)
                    ·
                      refine ⟨1633634594434171631618591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356358918491124350982909 1633634594434171631618591)
                      ·
                        rfl

theorem cell23_3181492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3181492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181492 prefixEnd_3181492 := by exact prefixLift 3181492
  have htrace : WordTrace (prefixWord ++ tailWord_3181492) baseStart_3181492 baseEnd_3181492 := by
    simpa [prefixWord, tailWord_3181492, baseEnd_3181492] using wordTrace_append hprefix tailTrace_3181492
  have hstable : (prefixWord ++ tailWord_3181492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181492).length < 2 ^ (prefixWord ++ tailWord_3181492).sum := by decide
  have hdescent : baseEnd_3181492 < baseStart_3181492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181498 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_3181498 : Nat := 118140960795 + 3181498 * 2 ^ 59
def prefixEnd_3181498 : Nat := 4983230072969 + 3 ^ 40 * 3181498 * 2
def baseEnd_3181498 : Nat := 1633637675318098608143563

theorem tailTrace_3181498 : CollatzResearch.WordTrace tailWord_3181498 prefixEnd_3181498 1633637675318098608143563 := by
  unfold tailWord_3181498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009691256995894361170287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77359176685322384963120765 29009691256995894361170287)
  ·
    refine ⟨43514536885493841541755431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29009691256995894361170287 43514536885493841541755431)
    ·
      refine ⟨65271805328240762312633147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43514536885493841541755431 65271805328240762312633147)
      ·
        refine ⟨97907707992361143468949721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65271805328240762312633147 97907707992361143468949721)
        ·
          refine ⟨73430780994270857601712291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97907707992361143468949721 73430780994270857601712291)
          ·
            refine ⟨110146171491406286402568437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73430780994270857601712291 110146171491406286402568437)
            ·
              refine ⟨10326203577319339350240791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110146171491406286402568437 10326203577319339350240791)
              ·
                refine ⟨15489305365979009025361187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10326203577319339350240791 15489305365979009025361187)
                ·
                  refine ⟨23233958048968513538041781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15489305365979009025361187 23233958048968513538041781)
                  ·
                    refine ⟨2178183567090798144191417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23233958048968513538041781 2178183567090798144191417)
                    ·
                      refine ⟨1633637675318098608143563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178183567090798144191417 1633637675318098608143563)
                      ·
                        rfl

theorem cell23_3181498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_3181498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181498 prefixEnd_3181498 := by exact prefixLift 3181498
  have htrace : WordTrace (prefixWord ++ tailWord_3181498) baseStart_3181498 baseEnd_3181498 := by
    simpa [prefixWord, tailWord_3181498, baseEnd_3181498] using wordTrace_append hprefix tailTrace_3181498
  have hstable : (prefixWord ++ tailWord_3181498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181498).length < 2 ^ (prefixWord ++ tailWord_3181498).sum := by decide
  have hdescent : baseEnd_3181498 < baseStart_3181498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181522 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3181522 : Nat := 118140960795 + 3181522 * 2 ^ 59
def prefixEnd_3181522 : Nat := 4983230072969 + 3 ^ 40 * 3181522 * 2
def baseEnd_3181522 : Nat := 1633649998853806514243453

theorem tailTrace_3181522 : CollatzResearch.WordTrace tailWord_3181522 prefixEnd_3181522 1633649998853806514243453 := by
  unfold tailWord_3181522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009910094974157385888705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77359760253264419695703213 29009910094974157385888705)
  ·
    refine ⟨21757432571230618039416529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29009910094974157385888705 21757432571230618039416529)
    ·
      refine ⟨16318074428422963529562397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21757432571230618039416529 16318074428422963529562397)
      ·
        refine ⟨6119277910658611323585899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16318074428422963529562397 6119277910658611323585899)
        ·
          refine ⟨9178916865987916985378849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119277910658611323585899 9178916865987916985378849)
          ·
            refine ⟨6884187649490937739034137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178916865987916985378849 6884187649490937739034137)
            ·
              refine ⟨5163140737118203304275603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884187649490937739034137 5163140737118203304275603)
              ·
                refine ⟨7744711105677304956413405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163140737118203304275603 7744711105677304956413405)
                ·
                  refine ⟨2904266664628989358655027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7744711105677304956413405 2904266664628989358655027)
                  ·
                    refine ⟨4356399996943484037982541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904266664628989358655027 4356399996943484037982541)
                    ·
                      refine ⟨1633649998853806514243453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356399996943484037982541 1633649998853806514243453)
                      ·
                        rfl

theorem cell23_3181522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3181522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181522 prefixEnd_3181522 := by exact prefixLift 3181522
  have htrace : WordTrace (prefixWord ++ tailWord_3181522) baseStart_3181522 baseEnd_3181522 := by
    simpa [prefixWord, tailWord_3181522, baseEnd_3181522] using wordTrace_append hprefix tailTrace_3181522
  have hstable : (prefixWord ++ tailWord_3181522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181522).length < 2 ^ (prefixWord ++ tailWord_3181522).sum := by decide
  have hdescent : baseEnd_3181522 < baseStart_3181522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181551 : List Nat := [1, 1, 2, 1, 4, 4, 1, 9]
def baseStart_3181551 : Nat := 118140960795 + 3181551 * 2 ^ 59
def prefixEnd_3181551 : Nat := 4983230072969 + 3 ^ 40 * 3181551 * 2
def baseEnd_3181551 : Nat := 60506107029362477806697

theorem tailTrace_3181551 : CollatzResearch.WordTrace tailWord_3181551 prefixEnd_3181551 60506107029362477806697 := by
  unfold tailWord_3181551
  simp only [CollatzResearch.WordTrace]
  refine ⟨116040698096791567496360507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77360465397861044997573671 116040698096791567496360507)
  ·
    refine ⟨174061047145187351244540761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116040698096791567496360507 174061047145187351244540761)
    ·
      refine ⟨130545785358890513433405571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174061047145187351244540761 130545785358890513433405571)
      ·
        refine ⟨195818678038335770150108357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130545785358890513433405571 195818678038335770150108357)
        ·
          refine ⟨36716002132187956903145317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195818678038335770150108357 36716002132187956903145317)
          ·
            refine ⟨6884250399785241919339747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36716002132187956903145317 6884250399785241919339747)
            ·
              refine ⟨10326375599677862879009621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884250399785241919339747 10326375599677862879009621)
              ·
                refine ⟨60506107029362477806697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10326375599677862879009621 60506107029362477806697)
                ·
                  rfl

theorem cell23_3181551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 9].length) (baseStart_3181551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181551 prefixEnd_3181551 := by exact prefixLift 3181551
  have htrace : WordTrace (prefixWord ++ tailWord_3181551) baseStart_3181551 baseEnd_3181551 := by
    simpa [prefixWord, tailWord_3181551, baseEnd_3181551] using wordTrace_append hprefix tailTrace_3181551
  have hstable : (prefixWord ++ tailWord_3181551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181551).length < 2 ^ (prefixWord ++ tailWord_3181551).sum := by decide
  have hdescent : baseEnd_3181551 < baseStart_3181551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181605 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_3181605 : Nat := 118140960795 + 3181605 * 2 ^ 59
def prefixEnd_3181605 : Nat := 4983230072969 + 3 ^ 40 * 3181605 * 2
def baseEnd_3181605 : Nat := 1633692617748129689505571

theorem tailTrace_3181605 : CollatzResearch.WordTrace tailWord_3181605 prefixEnd_3181605 1633692617748129689505571 := by
  unfold tailWord_3181605
  simp only [CollatzResearch.WordTrace]
  refine ⟨116042667638595934718826269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77361778425730623145884179 116042667638595934718826269)
  ·
    refine ⟨43516000364473475519559851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116042667638595934718826269 43516000364473475519559851)
    ·
      refine ⟨65274000546710213279339777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43516000364473475519559851 65274000546710213279339777)
      ·
        refine ⟨48955500410032659959504833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65274000546710213279339777 48955500410032659959504833)
        ·
          refine ⟨36716625307524494969628625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48955500410032659959504833 36716625307524494969628625)
          ·
            refine ⟨27537468980643371227221469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36716625307524494969628625 27537468980643371227221469)
            ·
              refine ⟨10326550867741264210208051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27537468980643371227221469 10326550867741264210208051)
              ·
                refine ⟨15489826301611896315312077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10326550867741264210208051 15489826301611896315312077)
                ·
                  refine ⟨5808684863104461118242029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15489826301611896315312077 5808684863104461118242029)
                  ·
                    refine ⟨2178256823664172919340761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5808684863104461118242029 2178256823664172919340761)
                    ·
                      refine ⟨1633692617748129689505571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178256823664172919340761 1633692617748129689505571)
                      ·
                        rfl

theorem cell23_3181605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_3181605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181605 prefixEnd_3181605 := by exact prefixLift 3181605
  have htrace : WordTrace (prefixWord ++ tailWord_3181605) baseStart_3181605 baseEnd_3181605 := by
    simpa [prefixWord, tailWord_3181605, baseEnd_3181605] using wordTrace_append hprefix tailTrace_3181605
  have hstable : (prefixWord ++ tailWord_3181605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181605).length < 2 ^ (prefixWord ++ tailWord_3181605).sum := by decide
  have hdescent : baseEnd_3181605 < baseStart_3181605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181631 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3181631 : Nat := 118140960795 + 3181631 * 2 ^ 59
def prefixEnd_3181631 : Nat := 4983230072969 + 3 ^ 40 * 3181631 * 2
def baseEnd_3181631 : Nat := 1633705968245146587780451

theorem tailTrace_3181631 : CollatzResearch.WordTrace tailWord_3181631 prefixEnd_3181631 1633705968245146587780451 := by
  unfold tailWord_3181631
  simp only [CollatzResearch.WordTrace]
  refine ⟨116043615936501741159272747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77362410624334494106181831 116043615936501741159272747)
  ·
    refine ⟨174065423904752611738909121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116043615936501741159272747 174065423904752611738909121)
    ·
      refine ⟨130549067928564458804181841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174065423904752611738909121 130549067928564458804181841)
      ·
        refine ⟨97911800946423344103136381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130549067928564458804181841 97911800946423344103136381)
        ·
          refine ⟨36716925354908754038676143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97911800946423344103136381 36716925354908754038676143)
          ·
            refine ⟨55075388032363131058014215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36716925354908754038676143 55075388032363131058014215)
            ·
              refine ⟨82613082048544696587021323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55075388032363131058014215 82613082048544696587021323)
              ·
                refine ⟨123919623072817044880531985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82613082048544696587021323 123919623072817044880531985)
                ·
                  refine ⟨92939717304612783660398989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123919623072817044880531985 92939717304612783660398989)
                  ·
                    refine ⟨34852393989229793872649621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92939717304612783660398989 34852393989229793872649621)
                    ·
                      refine ⟨1633705968245146587780451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34852393989229793872649621 1633705968245146587780451)
                      ·
                        rfl

theorem cell23_3181631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3181631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181631 prefixEnd_3181631 := by exact prefixLift 3181631
  have htrace : WordTrace (prefixWord ++ tailWord_3181631) baseStart_3181631 baseEnd_3181631 := by
    simpa [prefixWord, tailWord_3181631, baseEnd_3181631] using wordTrace_append hprefix tailTrace_3181631
  have hstable : (prefixWord ++ tailWord_3181631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181631).length < 2 ^ (prefixWord ++ tailWord_3181631).sum := by decide
  have hdescent : baseEnd_3181631 < baseStart_3181631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181645 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3181645 : Nat := 118140960795 + 3181645 * 2 ^ 59
def prefixEnd_3181645 : Nat := 4983230072969 + 3 ^ 40 * 3181645 * 2
def baseEnd_3181645 : Nat := 544571052324769844335129

theorem tailTrace_3181645 : CollatzResearch.WordTrace tailWord_3181645 prefixEnd_3181645 544571052324769844335129 := by
  unfold tailWord_3181645
  simp only [CollatzResearch.WordTrace]
  refine ⟨116044126558451021550282389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77362751038967347700188259 116044126558451021550282389)
  ·
    refine ⟨5439568432427391635169487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116044126558451021550282389 5439568432427391635169487)
    ·
      refine ⟨8159352648641087452754231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439568432427391635169487 8159352648641087452754231)
      ·
        refine ⟨12239028972961631179131347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159352648641087452754231 12239028972961631179131347)
        ·
          refine ⟨18358543459442446768697021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12239028972961631179131347 18358543459442446768697021)
          ·
            refine ⟨6884453797290917538261383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18358543459442446768697021 6884453797290917538261383)
            ·
              refine ⟨10326680695936376307392075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884453797290917538261383 10326680695936376307392075)
              ·
                refine ⟨15490021043904564461088113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10326680695936376307392075 15490021043904564461088113)
                ·
                  refine ⟨11617515782928423345816085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15490021043904564461088113 11617515782928423345816085)
                  ·
                    refine ⟨544571052324769844335129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11617515782928423345816085 544571052324769844335129)
                    ·
                      rfl

theorem cell23_3181645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3181645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181645 prefixEnd_3181645 := by exact prefixLift 3181645
  have htrace : WordTrace (prefixWord ++ tailWord_3181645) baseStart_3181645 baseEnd_3181645 := by
    simpa [prefixWord, tailWord_3181645, baseEnd_3181645] using wordTrace_append hprefix tailTrace_3181645
  have hstable : (prefixWord ++ tailWord_3181645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181645).length < 2 ^ (prefixWord ++ tailWord_3181645).sum := by decide
  have hdescent : baseEnd_3181645 < baseStart_3181645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181668 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_3181668 : Nat := 118140960795 + 3181668 * 2 ^ 59
def prefixEnd_3181668 : Nat := 4983230072969 + 3 ^ 40 * 3181668 * 2
def baseEnd_3181668 : Nat := 1633724967029362943017781

theorem tailTrace_3181668 : CollatzResearch.WordTrace tailWord_3181668 prefixEnd_3181668 1633724967029362943017781 := by
  unfold tailWord_3181668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58022482718683848239184829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77363310291578464318913105 58022482718683848239184829)
  ·
    refine ⟨21758431019506443089694311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58022482718683848239184829 21758431019506443089694311)
    ·
      refine ⟨32637646529259664634541467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21758431019506443089694311 32637646529259664634541467)
      ·
        refine ⟨48956469793889496951812201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32637646529259664634541467 48956469793889496951812201)
        ·
          refine ⟨36717352345417122713859151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48956469793889496951812201 36717352345417122713859151)
          ·
            refine ⟨55076028518125684070788727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36717352345417122713859151 55076028518125684070788727)
            ·
              refine ⟨82614042777188526106183091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55076028518125684070788727 82614042777188526106183091)
              ·
                refine ⟨123921064165782789159274637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82614042777188526106183091 123921064165782789159274637)
                ·
                  refine ⟨46470399062168545934727989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123921064165782789159274637 46470399062168545934727989)
                  ·
                    refine ⟨4356599912078301181380749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46470399062168545934727989 4356599912078301181380749)
                    ·
                      refine ⟨1633724967029362943017781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356599912078301181380749 1633724967029362943017781)
                      ·
                        rfl

theorem cell23_3181668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_3181668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181668 prefixEnd_3181668 := by exact prefixLift 3181668
  have htrace : WordTrace (prefixWord ++ tailWord_3181668) baseStart_3181668 baseEnd_3181668 := by
    simpa [prefixWord, tailWord_3181668, baseEnd_3181668] using wordTrace_append hprefix tailTrace_3181668
  have hstable : (prefixWord ++ tailWord_3181668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181668).length < 2 ^ (prefixWord ++ tailWord_3181668).sum := by decide
  have hdescent : baseEnd_3181668 < baseStart_3181668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181688 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_3181688 : Nat := 118140960795 + 3181688 * 2 ^ 59
def prefixEnd_3181688 : Nat := 4983230072969 + 3 ^ 40 * 3181688 * 2
def baseEnd_3181688 : Nat := 544578412214150954922563

theorem tailTrace_3181688 : CollatzResearch.WordTrace tailWord_3181688 prefixEnd_3181688 544578412214150954922563 := by
  unfold tailWord_3181688
  simp only [CollatzResearch.WordTrace]
  refine ⟨58022847448647619947048859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77363796598196826596065145 58022847448647619947048859)
  ·
    refine ⟨87034271172971429920573289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58022847448647619947048859 87034271172971429920573289)
    ·
      refine ⟨65275703379728572440429967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87034271172971429920573289 65275703379728572440429967)
      ·
        refine ⟨97913555069592858660644951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65275703379728572440429967 97913555069592858660644951)
        ·
          refine ⟨146870332604389287990967427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97913555069592858660644951 146870332604389287990967427)
          ·
            refine ⟨220305498906583931986451141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146870332604389287990967427 220305498906583931986451141)
            ·
              refine ⟨41307281044984487247459589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220305498906583931986451141 41307281044984487247459589)
              ·
                refine ⟨7745115195934591358898673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41307281044984487247459589 7745115195934591358898673)
                ·
                  refine ⟨5808836396950943519174005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745115195934591358898673 5808836396950943519174005)
                  ·
                    refine ⟨544578412214150954922563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5808836396950943519174005 544578412214150954922563)
                    ·
                      rfl

theorem cell23_3181688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_3181688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181688 prefixEnd_3181688 := by exact prefixLift 3181688
  have htrace : WordTrace (prefixWord ++ tailWord_3181688) baseStart_3181688 baseEnd_3181688 := by
    simpa [prefixWord, tailWord_3181688, baseEnd_3181688] using wordTrace_append hprefix tailTrace_3181688
  have hstable : (prefixWord ++ tailWord_3181688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181688).length < 2 ^ (prefixWord ++ tailWord_3181688).sum := by decide
  have hdescent : baseEnd_3181688 < baseStart_3181688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181725 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3181725 : Nat := 118140960795 + 3181725 * 2 ^ 59
def prefixEnd_3181725 : Nat := 4983230072969 + 3 ^ 40 * 3181725 * 2
def baseEnd_3181725 : Nat := 1633754235426669220005019

theorem tailTrace_3181725 : CollatzResearch.WordTrace tailWord_3181725 prefixEnd_3181725 1633754235426669220005019 := by
  unfold tailWord_3181725
  simp only [CollatzResearch.WordTrace]
  refine ⟨116047044398161195213194629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77364696265440796808796419 116047044398161195213194629)
  ·
    refine ⟨21758820824655224102473993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116047044398161195213194629 21758820824655224102473993)
    ·
      refine ⟨16319115618491418076855495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21758820824655224102473993 16319115618491418076855495)
      ·
        refine ⟨24478673427737127115283243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16319115618491418076855495 24478673427737127115283243)
        ·
          refine ⟨36718010141605690672924865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24478673427737127115283243 36718010141605690672924865)
          ·
            refine ⟨27538507606204268004693649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36718010141605690672924865 27538507606204268004693649)
            ·
              refine ⟨20653880704653201003520237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27538507606204268004693649 20653880704653201003520237)
              ·
                refine ⟨7745205264244950376320089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20653880704653201003520237 7745205264244950376320089)
                ·
                  refine ⟨5808903948183712782240067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7745205264244950376320089 5808903948183712782240067)
                  ·
                    refine ⟨8713355922275569173360101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5808903948183712782240067 8713355922275569173360101)
                    ·
                      refine ⟨1633754235426669220005019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8713355922275569173360101 1633754235426669220005019)
                      ·
                        rfl

theorem cell23_3181725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3181725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181725 prefixEnd_3181725 := by exact prefixLift 3181725
  have htrace : WordTrace (prefixWord ++ tailWord_3181725) baseStart_3181725 baseEnd_3181725 := by
    simpa [prefixWord, tailWord_3181725, baseEnd_3181725] using wordTrace_append hprefix tailTrace_3181725
  have hstable : (prefixWord ++ tailWord_3181725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181725).length < 2 ^ (prefixWord ++ tailWord_3181725).sum := by decide
  have hdescent : baseEnd_3181725 < baseStart_3181725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181768 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3181768 : Nat := 118140960795 + 3181768 * 2 ^ 59
def prefixEnd_3181768 : Nat := 4983230072969 + 3 ^ 40 * 3181768 * 2
def baseEnd_3181768 : Nat := 1633776315094812551767321

theorem tailTrace_3181768 : CollatzResearch.WordTrace tailWord_3181768 prefixEnd_3181768 1633776315094812551767321 := by
  unfold tailWord_3181768
  simp only [CollatzResearch.WordTrace]
  refine ⟨58024306368502706778504979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77365741824670275704673305 58024306368502706778504979)
  ·
    refine ⟨87036459552754060167757469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58024306368502706778504979 87036459552754060167757469)
    ·
      refine ⟨32638672332282772562909051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87036459552754060167757469 32638672332282772562909051)
      ·
        refine ⟨48958008498424158844363577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32638672332282772562909051 48958008498424158844363577)
        ·
          refine ⟨36718506373818119133272683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48958008498424158844363577 36718506373818119133272683)
          ·
            refine ⟨55077759560727178699909025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36718506373818119133272683 55077759560727178699909025)
            ·
              refine ⟨41308319670545384024931769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55077759560727178699909025 41308319670545384024931769)
              ·
                refine ⟨30981239752909038018698827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41308319670545384024931769 30981239752909038018698827)
                ·
                  refine ⟨46471859629363557028048241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30981239752909038018698827 46471859629363557028048241)
                  ·
                    refine ⟨34853894722022667771036181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46471859629363557028048241 34853894722022667771036181)
                    ·
                      refine ⟨1633776315094812551767321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34853894722022667771036181 1633776315094812551767321)
                      ·
                        rfl

theorem cell23_3181768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3181768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181768 prefixEnd_3181768 := by exact prefixLift 3181768
  have htrace : WordTrace (prefixWord ++ tailWord_3181768) baseStart_3181768 baseEnd_3181768 := by
    simpa [prefixWord, tailWord_3181768, baseEnd_3181768] using wordTrace_append hprefix tailTrace_3181768
  have hstable : (prefixWord ++ tailWord_3181768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181768).length < 2 ^ (prefixWord ++ tailWord_3181768).sum := by decide
  have hdescent : baseEnd_3181768 < baseStart_3181768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181825 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3181825 : Nat := 118140960795 + 3181825 * 2 ^ 59
def prefixEnd_3181825 : Nat := 4983230072969 + 3 ^ 40 * 3181825 * 2
def baseEnd_3181825 : Nat := 544601861164039609584853

theorem tailTrace_3181825 : CollatzResearch.WordTrace tailWord_3181825 prefixEnd_3181825 544601861164039609584853 := by
  unfold tailWord_3181825
  simp only [CollatzResearch.WordTrace]
  refine ⟨116050691697798912291834929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77367127798532608194556619 116050691697798912291834929)
  ·
    refine ⟨87038018773349184218876197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116050691697798912291834929 87038018773349184218876197)
    ·
      refine ⟨16319628520002972041039287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87038018773349184218876197 16319628520002972041039287)
      ·
        refine ⟨24479442780004458061558931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16319628520002972041039287 24479442780004458061558931)
        ·
          refine ⟨36719164170006687092338397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24479442780004458061558931 36719164170006687092338397)
          ·
            refine ⟨13769686563752507659626899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36719164170006687092338397 13769686563752507659626899)
            ·
              refine ⟨20654529845628761489440349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769686563752507659626899 20654529845628761489440349)
              ·
                refine ⟨7745448692110785558540131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654529845628761489440349 7745448692110785558540131)
                ·
                  refine ⟨11618173038166178337810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745448692110785558540131 11618173038166178337810197)
                  ·
                    refine ⟨544601861164039609584853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11618173038166178337810197 544601861164039609584853)
                    ·
                      rfl

theorem cell23_3181825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3181825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181825 prefixEnd_3181825 := by exact prefixLift 3181825
  have htrace : WordTrace (prefixWord ++ tailWord_3181825) baseStart_3181825 baseEnd_3181825 := by
    simpa [prefixWord, tailWord_3181825, baseEnd_3181825] using wordTrace_append hprefix tailTrace_3181825
  have hstable : (prefixWord ++ tailWord_3181825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181825).length < 2 ^ (prefixWord ++ tailWord_3181825).sum := by decide
  have hdescent : baseEnd_3181825 < baseStart_3181825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181826 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3181826 : Nat := 118140960795 + 3181826 * 2 ^ 59
def prefixEnd_3181826 : Nat := 4983230072969 + 3 ^ 40 * 3181826 * 2
def baseEnd_3181826 : Nat := 1633806096972773324842055

theorem tailTrace_3181826 : CollatzResearch.WordTrace tailWord_3181826 prefixEnd_3181826 1633806096972773324842055 := by
  unfold tailWord_3181826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012682042698822365655333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77367152113863526308414221 29012682042698822365655333)
  ·
    refine ⟨5439877883006029193560375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29012682042698822365655333 5439877883006029193560375)
    ·
      refine ⟨8159816824509043790340563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439877883006029193560375 8159816824509043790340563)
      ·
        refine ⟨12239725236763565685510845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159816824509043790340563 12239725236763565685510845)
        ·
          refine ⟨4589896963786337132066567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12239725236763565685510845 4589896963786337132066567)
          ·
            refine ⟨6884845445679505698099851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589896963786337132066567 6884845445679505698099851)
            ·
              refine ⟨10327268168519258547149777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884845445679505698099851 10327268168519258547149777)
              ·
                refine ⟨7745451126389443910362333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327268168519258547149777 7745451126389443910362333)
                ·
                  refine ⟨2904544172396041466385875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7745451126389443910362333 2904544172396041466385875)
                  ·
                    refine ⟨4356816258594062199578813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904544172396041466385875 4356816258594062199578813)
                    ·
                      refine ⟨1633806096972773324842055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356816258594062199578813 1633806096972773324842055)
                      ·
                        rfl

theorem cell23_3181826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3181826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181826 prefixEnd_3181826 := by exact prefixLift 3181826
  have htrace : WordTrace (prefixWord ++ tailWord_3181826) baseStart_3181826 baseEnd_3181826 := by
    simpa [prefixWord, tailWord_3181826, baseEnd_3181826] using wordTrace_append hprefix tailTrace_3181826
  have hstable : (prefixWord ++ tailWord_3181826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181826).length < 2 ^ (prefixWord ++ tailWord_3181826).sum := by decide
  have hdescent : baseEnd_3181826 < baseStart_3181826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181855 : List Nat := [1, 1, 2, 4, 4, 1, 10]
def baseStart_3181855 : Nat := 118140960795 + 3181855 * 2 ^ 59
def prefixEnd_3181855 : Nat := 4983230072969 + 3 ^ 40 * 3181855 * 2
def baseEnd_3181855 : Nat := 20170629480392021128141

theorem tailTrace_3181855 : CollatzResearch.WordTrace tailWord_3181855 prefixEnd_3181855 20170629480392021128141 := by
  unfold tailWord_3181855
  simp only [CollatzResearch.WordTrace]
  refine ⟨116051785887690227415427019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77367857258460151610284679 116051785887690227415427019)
  ·
    refine ⟨174077678831535341123140529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116051785887690227415427019 174077678831535341123140529)
    ·
      refine ⟨130558259123651505842355397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174077678831535341123140529 130558259123651505842355397)
      ·
        refine ⟨24479673585684657345441637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130558259123651505842355397 24479673585684657345441637)
        ·
          refine ⟨4589938797315873252270307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24479673585684657345441637 4589938797315873252270307)
          ·
            refine ⟨6884908195973809878405461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589938797315873252270307 6884908195973809878405461)
            ·
              refine ⟨20170629480392021128141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6884908195973809878405461 20170629480392021128141)
              ·
                rfl

theorem cell23_3181855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 10].length) (baseStart_3181855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181855 prefixEnd_3181855 := by exact prefixLift 3181855
  have htrace : WordTrace (prefixWord ++ tailWord_3181855) baseStart_3181855 baseEnd_3181855 := by
    simpa [prefixWord, tailWord_3181855, baseEnd_3181855] using wordTrace_append hprefix tailTrace_3181855
  have hstable : (prefixWord ++ tailWord_3181855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181855).length < 2 ^ (prefixWord ++ tailWord_3181855).sum := by decide
  have hdescent : baseEnd_3181855 < baseStart_3181855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181859 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 2, 4]
def baseStart_3181859 : Nat := 118140960795 + 3181859 * 2 ^ 59
def prefixEnd_3181859 : Nat := 4983230072969 + 3 ^ 40 * 3181859 * 2
def baseEnd_3181859 : Nat := 544607680611457231909801

theorem tailTrace_3181859 : CollatzResearch.WordTrace tailWord_3181859 prefixEnd_3181859 544607680611457231909801 := by
  unfold tailWord_3181859
  simp only [CollatzResearch.WordTrace]
  refine ⟨116051931779675736098572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77367954519783824065715087 116051931779675736098572631)
  ·
    refine ⟨174077897669513604147858947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116051931779675736098572631 174077897669513604147858947)
    ·
      refine ⟨261116846504270406221788421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174077897669513604147858947 261116846504270406221788421)
      ·
        refine ⟨48959408719550701166585329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261116846504270406221788421 48959408719550701166585329)
        ·
          refine ⟨36719556539663025874938997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48959408719550701166585329 36719556539663025874938997)
          ·
            refine ⟨3442458425593408675775531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36719556539663025874938997 3442458425593408675775531)
            ·
              refine ⟨5163687638390113013663297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442458425593408675775531 5163687638390113013663297)
              ·
                refine ⟨3872765728792584760247473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163687638390113013663297 3872765728792584760247473)
                ·
                  refine ⟨2904574296594438570185605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872765728792584760247473 2904574296594438570185605)
                  ·
                    refine ⟨544607680611457231909801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2904574296594438570185605 544607680611457231909801)
                    ·
                      rfl

theorem cell23_3181859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 4].length) (baseStart_3181859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181859 prefixEnd_3181859 := by exact prefixLift 3181859
  have htrace : WordTrace (prefixWord ++ tailWord_3181859) baseStart_3181859 baseEnd_3181859 := by
    simpa [prefixWord, tailWord_3181859, baseEnd_3181859] using wordTrace_append hprefix tailTrace_3181859
  have hstable : (prefixWord ++ tailWord_3181859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181859).length < 2 ^ (prefixWord ++ tailWord_3181859).sum := by decide
  have hdescent : baseEnd_3181859 < baseStart_3181859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181866 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3181866 : Nat := 118140960795 + 3181866 * 2 ^ 59
def prefixEnd_3181866 : Nat := 4983230072969 + 3 ^ 40 * 3181866 * 2
def baseEnd_3181866 : Nat := 1633826636198953168341871

theorem tailTrace_3181866 : CollatzResearch.WordTrace tailWord_3181866 prefixEnd_3181866 1633826636198953168341871 := by
  unfold tailWord_3181866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013046772662594073519363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77368124727100250862718301 29013046772662594073519363)
  ·
    refine ⟨43519570158993891110279045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29013046772662594073519363 43519570158993891110279045)
    ·
      refine ⟨8159919404811354583177321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43519570158993891110279045 8159919404811354583177321)
      ·
        refine ⟨6119939553608515937382991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8159919404811354583177321 6119939553608515937382991)
        ·
          refine ⟨9179909330412773906074487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119939553608515937382991 9179909330412773906074487)
          ·
            refine ⟨13769863995619160859111731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179909330412773906074487 13769863995619160859111731)
            ·
              refine ⟨20654795993428741288667597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769863995619160859111731 20654795993428741288667597)
              ·
                refine ⟨7745548497535777983250349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20654795993428741288667597 7745548497535777983250349)
                ·
                  refine ⟨2904580686575916743718881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7745548497535777983250349 2904580686575916743718881)
                  ·
                    refine ⟨2178435514931937557789161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2904580686575916743718881 2178435514931937557789161)
                    ·
                      refine ⟨1633826636198953168341871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178435514931937557789161 1633826636198953168341871)
                      ·
                        rfl

theorem cell23_3181866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3181866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181866 prefixEnd_3181866 := by exact prefixLift 3181866
  have htrace : WordTrace (prefixWord ++ tailWord_3181866) baseStart_3181866 baseEnd_3181866 := by
    simpa [prefixWord, tailWord_3181866, baseEnd_3181866] using wordTrace_append hprefix tailTrace_3181866
  have hstable : (prefixWord ++ tailWord_3181866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181866).length < 2 ^ (prefixWord ++ tailWord_3181866).sum := by decide
  have hdescent : baseEnd_3181866 < baseStart_3181866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181869 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3181869 : Nat := 118140960795 + 3181869 * 2 ^ 59
def prefixEnd_3181869 : Nat := 4983230072969 + 3 ^ 40 * 3181869 * 2
def baseEnd_3181869 : Nat := 1633828176640916656604357

theorem tailTrace_3181869 : CollatzResearch.WordTrace tailWord_3181869 prefixEnd_3181869 1633828176640916656604357 := by
  unfold tailWord_3181869
  simp only [CollatzResearch.WordTrace]
  refine ⟨116052296509639507806436661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77368197673093005204291107 116052296509639507806436661)
  ·
    refine ⟨10879902797778703856853437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116052296509639507806436661 10879902797778703856853437)
    ·
      refine ⟨4079963549167013946320039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10879902797778703856853437 4079963549167013946320039)
      ·
        refine ⟨6119945323750520919480059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079963549167013946320039 6119945323750520919480059)
        ·
          refine ⟨9179917985625781379220089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119945323750520919480059 9179917985625781379220089)
          ·
            refine ⟨6884938489219336034415067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9179917985625781379220089 6884938489219336034415067)
            ·
              refine ⟨10327407733829004051622601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884938489219336034415067 10327407733829004051622601)
              ·
                refine ⟨7745555800371753038716951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10327407733829004051622601 7745555800371753038716951)
                ·
                  refine ⟨11618333700557629558075427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745555800371753038716951 11618333700557629558075427)
                  ·
                    refine ⟨17427500550836444337113141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11618333700557629558075427 17427500550836444337113141)
                    ·
                      refine ⟨1633828176640916656604357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17427500550836444337113141 1633828176640916656604357)
                      ·
                        rfl

theorem cell23_3181869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3181869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181869 prefixEnd_3181869 := by exact prefixLift 3181869
  have htrace : WordTrace (prefixWord ++ tailWord_3181869) baseStart_3181869 baseEnd_3181869 := by
    simpa [prefixWord, tailWord_3181869, baseEnd_3181869] using wordTrace_append hprefix tailTrace_3181869
  have hstable : (prefixWord ++ tailWord_3181869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181869).length < 2 ^ (prefixWord ++ tailWord_3181869).sum := by decide
  have hdescent : baseEnd_3181869 < baseStart_3181869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181876 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_3181876 : Nat := 118140960795 + 3181876 * 2 ^ 59
def prefixEnd_3181876 : Nat := 4983230072969 + 3 ^ 40 * 3181876 * 2
def baseEnd_3181876 : Nat := 544610590335166043072275

theorem tailTrace_3181876 : CollatzResearch.WordTrace tailWord_3181876 prefixEnd_3181876 544610590335166043072275 := by
  unfold tailWord_3181876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58026275910307074000970741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77368367880409432001294321 58026275910307074000970741)
  ·
    refine ⟨5439963366591288187591007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58026275910307074000970741 5439963366591288187591007)
    ·
      refine ⟨8159945049886932281386511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439963366591288187591007 8159945049886932281386511)
      ·
        refine ⟨12239917574830398422079767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159945049886932281386511 12239917574830398422079767)
        ·
          refine ⟨18359876362245597633119651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12239917574830398422079767 18359876362245597633119651)
          ·
            refine ⟨27539814543368396449679477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18359876362245597633119651 27539814543368396449679477)
            ·
              refine ⟨2581857613440787167157451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27539814543368396449679477 2581857613440787167157451)
              ·
                refine ⟨3872786420161180750736177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581857613440787167157451 3872786420161180750736177)
                ·
                  refine ⟨2904589815120885563052133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872786420161180750736177 2904589815120885563052133)
                  ·
                    refine ⟨544610590335166043072275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2904589815120885563052133 544610590335166043072275)
                    ·
                      rfl

theorem cell23_3181876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_3181876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181876 prefixEnd_3181876 := by exact prefixLift 3181876
  have htrace : WordTrace (prefixWord ++ tailWord_3181876) baseStart_3181876 baseEnd_3181876 := by
    simpa [prefixWord, tailWord_3181876, baseEnd_3181876] using wordTrace_append hprefix tailTrace_3181876
  have hstable : (prefixWord ++ tailWord_3181876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181876).length < 2 ^ (prefixWord ++ tailWord_3181876).sum := by decide
  have hdescent : baseEnd_3181876 < baseStart_3181876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181889 : List Nat := [1, 2, 5, 2, 1, 3, 2, 7]
def baseStart_3181889 : Nat := 118140960795 + 3181889 * 2 ^ 59
def prefixEnd_3181889 : Nat := 4983230072969 + 3 ^ 40 * 3181889 * 2
def baseEnd_3181889 : Nat := 60512535046444688087195

theorem tailTrace_3181889 : CollatzResearch.WordTrace tailWord_3181889 prefixEnd_3181889 60512535046444688087195 := by
  unfold tailWord_3181889
  simp only [CollatzResearch.WordTrace]
  refine ⟨116053025969567051222164721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77368683979711367481443147 116053025969567051222164721)
  ·
    refine ⟨87039769477175288416623541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116053025969567051222164721 87039769477175288416623541)
    ·
      refine ⟨8159978388485183289058457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87039769477175288416623541 8159978388485183289058457)
      ·
        refine ⟨6119983791363887466793843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8159978388485183289058457 6119983791363887466793843)
        ·
          refine ⟨9179975687045831200190765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119983791363887466793843 9179975687045831200190765)
          ·
            refine ⟨3442490882642186700071537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9179975687045831200190765 3442490882642186700071537)
            ·
              refine ⟨2581868161981640025053653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442490882642186700071537 2581868161981640025053653)
              ·
                refine ⟨60512535046444688087195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2581868161981640025053653 60512535046444688087195)
                ·
                  rfl

theorem cell23_3181889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 7].length) (baseStart_3181889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181889 prefixEnd_3181889 := by exact prefixLift 3181889
  have htrace : WordTrace (prefixWord ++ tailWord_3181889) baseStart_3181889 baseEnd_3181889 := by
    simpa [prefixWord, tailWord_3181889, baseEnd_3181889] using wordTrace_append hprefix tailTrace_3181889
  have hstable : (prefixWord ++ tailWord_3181889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181889).length < 2 ^ (prefixWord ++ tailWord_3181889).sum := by decide
  have hdescent : baseEnd_3181889 < baseStart_3181889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181894 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3181894 : Nat := 118140960795 + 3181894 * 2 ^ 59
def prefixEnd_3181894 : Nat := 4983230072969 + 3 ^ 40 * 3181894 * 2
def baseEnd_3181894 : Nat := 1633841013657279058791743

theorem tailTrace_3181894 : CollatzResearch.WordTrace tailWord_3181894 prefixEnd_3181894 1633841013657279058791743 := by
  unfold tailWord_3181894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626662760454654283628023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77368805556365958050731157 3626662760454654283628023)
  ·
    refine ⟨5439994140681981425442035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3626662760454654283628023 5439994140681981425442035)
    ·
      refine ⟨8159991211022972138163053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439994140681981425442035 8159991211022972138163053)
      ·
        refine ⟨3059996704133614551811145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8159991211022972138163053 3059996704133614551811145)
        ·
          refine ⟨2294997528100210913858359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3059996704133614551811145 2294997528100210913858359)
          ·
            refine ⟨3442496292150316370787539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294997528100210913858359 3442496292150316370787539)
            ·
              refine ⟨5163744438225474556181309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442496292150316370787539 5163744438225474556181309)
              ·
                refine ⟨1936404164334552958567991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5163744438225474556181309 1936404164334552958567991)
                ·
                  refine ⟨2904606246501829437851987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936404164334552958567991 2904606246501829437851987)
                  ·
                    refine ⟨4356909369752744156777981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904606246501829437851987 4356909369752744156777981)
                    ·
                      refine ⟨1633841013657279058791743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356909369752744156777981 1633841013657279058791743)
                      ·
                        rfl

theorem cell23_3181894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3181894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181894 prefixEnd_3181894 := by exact prefixLift 3181894
  have htrace : WordTrace (prefixWord ++ tailWord_3181894) baseStart_3181894 baseEnd_3181894 := by
    simpa [prefixWord, tailWord_3181894, baseEnd_3181894] using wordTrace_append hprefix tailTrace_3181894
  have hstable : (prefixWord ++ tailWord_3181894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181894).length < 2 ^ (prefixWord ++ tailWord_3181894).sum := by decide
  have hdescent : baseEnd_3181894 < baseStart_3181894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181895 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3181895 : Nat := 118140960795 + 3181895 * 2 ^ 59
def prefixEnd_3181895 : Nat := 4983230072969 + 3 ^ 40 * 3181895 * 2
def baseEnd_3181895 : Nat := 1633841527137933554879237

theorem tailTrace_3181895 : CollatzResearch.WordTrace tailWord_3181895 prefixEnd_3181895 1633841527137933554879237 := by
  unfold tailWord_3181895
  simp only [CollatzResearch.WordTrace]
  refine ⟨116053244807545314246883139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77368829871696876164588759 116053244807545314246883139)
  ·
    refine ⟨174079867211317971370324709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116053244807545314246883139 174079867211317971370324709)
    ·
      refine ⟨32639975102122119631935883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174079867211317971370324709 32639975102122119631935883)
      ·
        refine ⟨48959962653183179447903825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32639975102122119631935883 48959962653183179447903825)
        ·
          refine ⟨36719971989887384585927869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48959962653183179447903825 36719971989887384585927869)
          ·
            refine ⟨13769989496207769219722951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36719971989887384585927869 13769989496207769219722951)
            ·
              refine ⟨20654984244311653829584427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769989496207769219722951 20654984244311653829584427)
              ·
                refine ⟨30982476366467480744376641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20654984244311653829584427 30982476366467480744376641)
                ·
                  refine ⟨23236857274850610558282481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30982476366467480744376641 23236857274850610558282481)
                  ·
                    refine ⟨17427642956137957918711861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23236857274850610558282481 17427642956137957918711861)
                    ·
                      refine ⟨1633841527137933554879237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17427642956137957918711861 1633841527137933554879237)
                      ·
                        rfl

theorem cell23_3181895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3181895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181895 prefixEnd_3181895 := by exact prefixLift 3181895
  have htrace : WordTrace (prefixWord ++ tailWord_3181895) baseStart_3181895 baseEnd_3181895 := by
    simpa [prefixWord, tailWord_3181895, baseEnd_3181895] using wordTrace_append hprefix tailTrace_3181895
  have hstable : (prefixWord ++ tailWord_3181895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181895).length < 2 ^ (prefixWord ++ tailWord_3181895).sum := by decide
  have hdescent : baseEnd_3181895 < baseStart_3181895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181917 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3181917 : Nat := 118140960795 + 3181917 * 2 ^ 59
def prefixEnd_3181917 : Nat := 4983230072969 + 3 ^ 40 * 3181917 * 2
def baseEnd_3181917 : Nat := 1633852823712332468804137

theorem tailTrace_3181917 : CollatzResearch.WordTrace tailWord_3181917 prefixEnd_3181917 1633852823712332468804137 := by
  unfold tailWord_3181917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054047213465612004184005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77369364808977074669456003 116054047213465612004184005)
  ·
    refine ⟨21760133852524802250784501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116054047213465612004184005 21760133852524802250784501)
    ·
      refine ⟨2040012548674200211011047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21760133852524802250784501 2040012548674200211011047)
      ·
        refine ⟨3060018823011300316516571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040012548674200211011047 3060018823011300316516571)
        ·
          refine ⟨4590028234516950474774857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060018823011300316516571 4590028234516950474774857)
          ·
            refine ⟨3442521175887712856081143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590028234516950474774857 3442521175887712856081143)
            ·
              refine ⟨5163781763831569284121715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442521175887712856081143 5163781763831569284121715)
              ·
                refine ⟨7745672645747353926182573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163781763831569284121715 7745672645747353926182573)
                ·
                  refine ⟨2904627242155257722318465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7745672645747353926182573 2904627242155257722318465)
                  ·
                    refine ⟨2178470431616443291738849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2904627242155257722318465 2178470431616443291738849)
                    ·
                      refine ⟨1633852823712332468804137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178470431616443291738849 1633852823712332468804137)
                      ·
                        rfl

theorem cell23_3181917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3181917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181917 prefixEnd_3181917 := by exact prefixLift 3181917
  have htrace : WordTrace (prefixWord ++ tailWord_3181917) baseStart_3181917 baseEnd_3181917 := by
    simpa [prefixWord, tailWord_3181917, baseEnd_3181917] using wordTrace_append hprefix tailTrace_3181917
  have hstable : (prefixWord ++ tailWord_3181917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181917).length < 2 ^ (prefixWord ++ tailWord_3181917).sum := by decide
  have hdescent : baseEnd_3181917 < baseStart_3181917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181922 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3181922 : Nat := 118140960795 + 3181922 * 2 ^ 59
def prefixEnd_3181922 : Nat := 4983230072969 + 3 ^ 40 * 3181922 * 2
def baseEnd_3181922 : Nat := 1633855391115604949241613

theorem tailTrace_3181922 : CollatzResearch.WordTrace tailWord_3181922 prefixEnd_3181922 1633855391115604949241613 := by
  unfold tailWord_3181922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013557394611874464529005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77369486385631665238744013 29013557394611874464529005)
  ·
    refine ⟨10880084022979452924198377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29013557394611874464529005 10880084022979452924198377)
    ·
      refine ⟨8160063017234589693148783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10880084022979452924198377 8160063017234589693148783)
      ·
        refine ⟨12240094525851884539723175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160063017234589693148783 12240094525851884539723175)
        ·
          refine ⟨18360141788777826809584763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240094525851884539723175 18360141788777826809584763)
          ·
            refine ⟨27540212683166740214377145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18360141788777826809584763 27540212683166740214377145)
            ·
              refine ⟨20655159512375055160782859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27540212683166740214377145 20655159512375055160782859)
              ·
                refine ⟨30982739268562582741174289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20655159512375055160782859 30982739268562582741174289)
                ·
                  refine ⟨23237054451421937055880717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30982739268562582741174289 23237054451421937055880717)
                  ·
                    refine ⟨8713895419283226395955269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23237054451421937055880717 8713895419283226395955269)
                    ·
                      refine ⟨1633855391115604949241613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8713895419283226395955269 1633855391115604949241613)
                      ·
                        rfl

theorem cell23_3181922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3181922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181922 prefixEnd_3181922 := by exact prefixLift 3181922
  have htrace : WordTrace (prefixWord ++ tailWord_3181922) baseStart_3181922 baseEnd_3181922 := by
    simpa [prefixWord, tailWord_3181922, baseEnd_3181922] using wordTrace_append hprefix tailTrace_3181922
  have hstable : (prefixWord ++ tailWord_3181922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181922).length < 2 ^ (prefixWord ++ tailWord_3181922).sum := by decide
  have hdescent : baseEnd_3181922 < baseStart_3181922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181925 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3181925 : Nat := 118140960795 + 3181925 * 2 ^ 59
def prefixEnd_3181925 : Nat := 4983230072969 + 3 ^ 40 * 3181925 * 2
def baseEnd_3181925 : Nat := 1633856931557568437504099

theorem tailTrace_3181925 : CollatzResearch.WordTrace tailWord_3181925 prefixEnd_3181925 1633856931557568437504099 := by
  unfold tailWord_3181925
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054338997436629370475229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77369559331624419580316819 116054338997436629370475229)
  ·
    refine ⟨43520377124038736013928211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116054338997436629370475229 43520377124038736013928211)
    ·
      refine ⟨65280565686058104020892317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43520377124038736013928211 65280565686058104020892317)
      ·
        refine ⟨24480212132271789007834619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65280565686058104020892317 24480212132271789007834619)
        ·
          refine ⟨36720318198407683511751929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24480212132271789007834619 36720318198407683511751929)
          ·
            refine ⟨27540238648805762633813947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36720318198407683511751929 27540238648805762633813947)
            ·
              refine ⟨41310357973208643950720921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27540238648805762633813947 41310357973208643950720921)
              ·
                refine ⟨30982768479906482963040691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41310357973208643950720921 30982768479906482963040691)
                ·
                  refine ⟨46474152719859724444561037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30982768479906482963040691 46474152719859724444561037)
                  ·
                    refine ⟨17427807269947396666710389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46474152719859724444561037 17427807269947396666710389)
                    ·
                      refine ⟨1633856931557568437504099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17427807269947396666710389 1633856931557568437504099)
                      ·
                        rfl

theorem cell23_3181925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3181925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181925 prefixEnd_3181925 := by exact prefixLift 3181925
  have htrace : WordTrace (prefixWord ++ tailWord_3181925) baseStart_3181925 baseEnd_3181925 := by
    simpa [prefixWord, tailWord_3181925, baseEnd_3181925] using wordTrace_append hprefix tailTrace_3181925
  have hstable : (prefixWord ++ tailWord_3181925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181925).length < 2 ^ (prefixWord ++ tailWord_3181925).sum := by decide
  have hdescent : baseEnd_3181925 < baseStart_3181925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181933 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3181933 : Nat := 118140960795 + 3181933 * 2 ^ 59
def prefixEnd_3181933 : Nat := 4983230072969 + 3 ^ 40 * 3181933 * 2
def baseEnd_3181933 : Nat := 1633861039402804406204063

theorem tailTrace_3181933 : CollatzResearch.WordTrace tailWord_3181933 prefixEnd_3181933 1633861039402804406204063 := by
  unfold tailWord_3181933
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054630781407646736766453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77369753854271764491177635 116054630781407646736766453)
  ·
    refine ⟨10880121635756966881571855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116054630781407646736766453 10880121635756966881571855)
    ·
      refine ⟨16320182453635450322357783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880121635756966881571855 16320182453635450322357783)
      ·
        refine ⟨24480273680453175483536675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16320182453635450322357783 24480273680453175483536675)
        ·
          refine ⟨36720410520679763225305013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24480273680453175483536675 36720410520679763225305013)
          ·
            refine ⟨3442538486313727802372345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36720410520679763225305013 3442538486313727802372345)
            ·
              refine ⟨2581903864735295851779259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442538486313727802372345 2581903864735295851779259)
              ·
                refine ⟨3872855797102943777668889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581903864735295851779259 3872855797102943777668889)
                ·
                  refine ⟨2904641847827207833251667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872855797102943777668889 2904641847827207833251667)
                  ·
                    refine ⟨4356962771740811749877501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904641847827207833251667 4356962771740811749877501)
                    ·
                      refine ⟨1633861039402804406204063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4356962771740811749877501 1633861039402804406204063)
                      ·
                        rfl

theorem cell23_3181933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3181933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181933 prefixEnd_3181933 := by exact prefixLift 3181933
  have htrace : WordTrace (prefixWord ++ tailWord_3181933) baseStart_3181933 baseEnd_3181933 := by
    simpa [prefixWord, tailWord_3181933, baseEnd_3181933] using wordTrace_append hprefix tailTrace_3181933
  have hstable : (prefixWord ++ tailWord_3181933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181933).length < 2 ^ (prefixWord ++ tailWord_3181933).sum := by decide
  have hdescent : baseEnd_3181933 < baseStart_3181933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181935 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_3181935 : Nat := 118140960795 + 3181935 * 2 ^ 59
def prefixEnd_3181935 : Nat := 4983230072969 + 3 ^ 40 * 3181935 * 2
def baseEnd_3181935 : Nat := 1633862066364113398379053

theorem tailTrace_3181935 : CollatzResearch.WordTrace tailWord_3181935 prefixEnd_3181935 1633862066364113398379053 := by
  unfold tailWord_3181935
  simp only [CollatzResearch.WordTrace]
  refine ⟨116054703727400401078339259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77369802484933600718892839 116054703727400401078339259)
  ·
    refine ⟨174082055591100601617508889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116054703727400401078339259 174082055591100601617508889)
    ·
      refine ⟨130561541693325451213131667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174082055591100601617508889 130561541693325451213131667)
      ·
        refine ⟨195842312539988176819697501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130561541693325451213131667 195842312539988176819697501)
        ·
          refine ⟨73440867202495566307386563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195842312539988176819697501 73440867202495566307386563)
          ·
            refine ⟨110161300803743349461079845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73440867202495566307386563 110161300803743349461079845)
            ·
              refine ⟨20655243900701878023952471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110161300803743349461079845 20655243900701878023952471)
              ·
                refine ⟨30982865851052817035928707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20655243900701878023952471 30982865851052817035928707)
                ·
                  refine ⟨46474298776579225553893061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30982865851052817035928707 46474298776579225553893061)
                  ·
                    refine ⟨8713931020608604791354949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46474298776579225553893061 8713931020608604791354949)
                    ·
                      refine ⟨1633862066364113398379053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8713931020608604791354949 1633862066364113398379053)
                      ·
                        rfl

theorem cell23_3181935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_3181935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181935 prefixEnd_3181935 := by exact prefixLift 3181935
  have htrace : WordTrace (prefixWord ++ tailWord_3181935) baseStart_3181935 baseEnd_3181935 := by
    simpa [prefixWord, tailWord_3181935, baseEnd_3181935] using wordTrace_append hprefix tailTrace_3181935
  have hstable : (prefixWord ++ tailWord_3181935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181935).length < 2 ^ (prefixWord ++ tailWord_3181935).sum := by decide
  have hdescent : baseEnd_3181935 < baseStart_3181935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181945 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 7]
def baseStart_3181945 : Nat := 118140960795 + 3181945 * 2 ^ 59
def prefixEnd_3181945 : Nat := 4983230072969 + 3 ^ 40 * 3181945 * 2
def baseEnd_3181945 : Nat := 181540800130073151028223

theorem tailTrace_3181945 : CollatzResearch.WordTrace tailWord_3181945 prefixEnd_3181945 181540800130073151028223 := by
  unfold tailWord_3181945
  simp only [CollatzResearch.WordTrace]
  refine ⟨116055068457364172786203289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77370045638242781857468859 116055068457364172786203289)
  ·
    refine ⟨87041301343023129589652467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116055068457364172786203289 87041301343023129589652467)
    ·
      refine ⟨130561952014534694384478701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87041301343023129589652467 130561952014534694384478701)
      ·
        refine ⟨48960732005450510394179513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130561952014534694384478701 48960732005450510394179513)
        ·
          refine ⟨36720549004087882795634635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48960732005450510394179513 36720549004087882795634635)
          ·
            refine ⟨55080823506131824193451953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36720549004087882795634635 55080823506131824193451953)
            ·
              refine ⟨41310617629598868145088965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55080823506131824193451953 41310617629598868145088965)
              ·
                refine ⟨7745740805549787777204181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41310617629598868145088965 7745740805549787777204181)
                ·
                  refine ⟨181540800130073151028223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7745740805549787777204181 181540800130073151028223)
                  ·
                    rfl

theorem cell23_3181945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_3181945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181945 prefixEnd_3181945 := by exact prefixLift 3181945
  have htrace : WordTrace (prefixWord ++ tailWord_3181945) baseStart_3181945 baseEnd_3181945 := by
    simpa [prefixWord, tailWord_3181945, baseEnd_3181945] using wordTrace_append hprefix tailTrace_3181945
  have hstable : (prefixWord ++ tailWord_3181945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181945).length < 2 ^ (prefixWord ++ tailWord_3181945).sum := by decide
  have hdescent : baseEnd_3181945 < baseStart_3181945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181975 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 7]
def baseStart_3181975 : Nat := 118140960795 + 3181975 * 2 ^ 59
def prefixEnd_3181975 : Nat := 4983230072969 + 3 ^ 40 * 3181975 * 2
def baseEnd_3181975 : Nat := 544627535196764413959623

theorem tailTrace_3181975 : CollatzResearch.WordTrace tailWord_3181975 prefixEnd_3181975 544627535196764413959623 := by
  unfold tailWord_3181975
  simp only [CollatzResearch.WordTrace]
  refine ⟨116056162647255487909795379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77370775098170325273196919 116056162647255487909795379)
  ·
    refine ⟨174084243970883231864693069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116056162647255487909795379 174084243970883231864693069)
    ·
      refine ⟨65281591489081211949259901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174084243970883231864693069 65281591489081211949259901)
      ·
        refine ⟨24480596808405454480972463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65281591489081211949259901 24480596808405454480972463)
        ·
          refine ⟨36720895212608181721458695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24480596808405454480972463 36720895212608181721458695)
          ·
            refine ⟨55081342818912272582188043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36720895212608181721458695 55081342818912272582188043)
            ·
              refine ⟨82622014228368408873282065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55081342818912272582188043 82622014228368408873282065)
              ·
                refine ⟨61966510671276306654961549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82622014228368408873282065 61966510671276306654961549)
                ·
                  refine ⟨23237441501728614995610581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61966510671276306654961549 23237441501728614995610581)
                  ·
                    refine ⟨544627535196764413959623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23237441501728614995610581 544627535196764413959623)
                    ·
                      rfl

theorem cell23_3181975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_3181975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181975 prefixEnd_3181975 := by exact prefixLift 3181975
  have htrace : WordTrace (prefixWord ++ tailWord_3181975) baseStart_3181975 baseEnd_3181975 := by
    simpa [prefixWord, tailWord_3181975, baseEnd_3181975] using wordTrace_append hprefix tailTrace_3181975
  have hstable : (prefixWord ++ tailWord_3181975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181975).length < 2 ^ (prefixWord ++ tailWord_3181975).sum := by decide
  have hdescent : baseEnd_3181975 < baseStart_3181975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3181995 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_3181995 : Nat := 118140960795 + 3181995 * 2 ^ 59
def prefixEnd_3181995 : Nat := 4983230072969 + 3 ^ 40 * 3181995 * 2
def baseEnd_3181995 : Nat := 1633892875203383163628777

theorem tailTrace_3181995 : CollatzResearch.WordTrace tailWord_3181995 prefixEnd_3181995 1633892875203383163628777 := by
  unfold tailWord_3181995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116056892107183031325523439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77371261404788687550348959 116056892107183031325523439)
  ·
    refine ⟨174085338160774546988285159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116056892107183031325523439 174085338160774546988285159)
    ·
      refine ⟨261128007241161820482427739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174085338160774546988285159 261128007241161820482427739)
      ·
        refine ⟨391692010861742730723641609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261128007241161820482427739 391692010861742730723641609)
        ·
          refine ⟨293769008146307048042731207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391692010861742730723641609 293769008146307048042731207)
          ·
            refine ⟨440653512219460572064096811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293769008146307048042731207 440653512219460572064096811)
            ·
              refine ⟨660980268329190858096145217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440653512219460572064096811 660980268329190858096145217)
              ·
                refine ⟨495735201246893143572108913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660980268329190858096145217 495735201246893143572108913)
                ·
                  refine ⟨371801400935169857679081685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495735201246893143572108913 371801400935169857679081685)
                  ·
                    refine ⟨8714095334418043539353477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 371801400935169857679081685 8714095334418043539353477)
                    ·
                      refine ⟨1633892875203383163628777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8714095334418043539353477 1633892875203383163628777)
                      ·
                        rfl

theorem cell23_3181995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_3181995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3181995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3181995 prefixEnd_3181995 := by exact prefixLift 3181995
  have htrace : WordTrace (prefixWord ++ tailWord_3181995) baseStart_3181995 baseEnd_3181995 := by
    simpa [prefixWord, tailWord_3181995, baseEnd_3181995] using wordTrace_append hprefix tailTrace_3181995
  have hstable : (prefixWord ++ tailWord_3181995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3181995).length < 2 ^ (prefixWord ++ tailWord_3181995).sum := by decide
  have hdescent : baseEnd_3181995 < baseStart_3181995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3181995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182052 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 6]
def baseStart_3182052 : Nat := 118140960795 + 3182052 * 2 ^ 59
def prefixEnd_3182052 : Nat := 4983230072969 + 3 ^ 40 * 3182052 * 2
def baseEnd_3182052 : Nat := 181546904844521048957335

theorem tailTrace_3182052 : CollatzResearch.WordTrace tailWord_3182052 prefixEnd_3182052 181546904844521048957335 := by
  unfold tailWord_3182052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58029485533988265030174205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77372647378651020040232273 58029485533988265030174205)
  ·
    refine ⟨21761057075245599386315327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58029485533988265030174205 21761057075245599386315327)
    ·
      refine ⟨32641585612868399079472991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21761057075245599386315327 32641585612868399079472991)
      ·
        refine ⟨48962378419302598619209487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32641585612868399079472991 48962378419302598619209487)
        ·
          refine ⟨73443567628953897928814231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48962378419302598619209487 73443567628953897928814231)
          ·
            refine ⟨110165351443430846893221347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73443567628953897928814231 110165351443430846893221347)
            ·
              refine ⟨165248027165146270339832021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110165351443430846893221347 165248027165146270339832021)
              ·
                refine ⟨3873000636683115711089813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165248027165146270339832021 3873000636683115711089813)
                ·
                  refine ⟨181546904844521048957335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3873000636683115711089813 181546904844521048957335)
                  ·
                    rfl

theorem cell23_3182052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_3182052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182052 prefixEnd_3182052 := by exact prefixLift 3182052
  have htrace : WordTrace (prefixWord ++ tailWord_3182052) baseStart_3182052 baseEnd_3182052 := by
    simpa [prefixWord, tailWord_3182052, baseEnd_3182052] using wordTrace_append hprefix tailTrace_3182052
  have hstable : (prefixWord ++ tailWord_3182052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182052).length < 2 ^ (prefixWord ++ tailWord_3182052).sum := by decide
  have hdescent : baseEnd_3182052 < baseStart_3182052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182069 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 8]
def baseStart_3182069 : Nat := 118140960795 + 3182069 * 2 ^ 59
def prefixEnd_3182069 : Nat := 4983230072969 + 3 ^ 40 * 3182069 * 2
def baseEnd_3182069 : Nat := 181547874752423986011493

theorem tailTrace_3182069 : CollatzResearch.WordTrace tailWord_3182069 prefixEnd_3182069 181547874752423986011493 := by
  unfold tailWord_3182069
  simp only [CollatzResearch.WordTrace]
  refine ⟨116059591108914941963717261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77373060739276627975811507 116059591108914941963717261)
  ·
    refine ⟨43522346665843103236393973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116059591108914941963717261 43522346665843103236393973)
    ·
      refine ⟨4080219999922790928411935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43522346665843103236393973 4080219999922790928411935)
      ·
        refine ⟨6120329999884186392617903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080219999922790928411935 6120329999884186392617903)
        ·
          refine ⟨9180494999826279588926855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6120329999884186392617903 9180494999826279588926855)
          ·
            refine ⟨13770742499739419383390283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9180494999826279588926855 13770742499739419383390283)
            ·
              refine ⟨20656113749609129075085425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13770742499739419383390283 20656113749609129075085425)
              ·
                refine ⟨15492085312206846806314069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20656113749609129075085425 15492085312206846806314069)
                ·
                  refine ⟨181547874752423986011493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15492085312206846806314069 181547874752423986011493)
                  ·
                    rfl

theorem cell23_3182069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_3182069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182069 prefixEnd_3182069 := by exact prefixLift 3182069
  have htrace : WordTrace (prefixWord ++ tailWord_3182069) baseStart_3182069 baseEnd_3182069 := by
    simpa [prefixWord, tailWord_3182069, baseEnd_3182069] using wordTrace_append hprefix tailTrace_3182069
  have hstable : (prefixWord ++ tailWord_3182069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182069).length < 2 ^ (prefixWord ++ tailWord_3182069).sum := by decide
  have hdescent : baseEnd_3182069 < baseStart_3182069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182142 : List Nat := [4, 2, 1, 16]
def baseStart_3182142 : Nat := 118140960795 + 3182142 * 2 ^ 59
def prefixEnd_3182142 : Nat := 4983230072969 + 3 ^ 40 * 3182142 * 2
def baseEnd_3182142 : Nat := 747127735189572056923

theorem tailTrace_3182142 : CollatzResearch.WordTrace tailWord_3182142 prefixEnd_3182142 747127735189572056923 := by
  unfold tailWord_3182142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14507781704706309428890585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77374835758433650287416453 14507781704706309428890585)
  ·
    refine ⟨10880836278529732071667939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14507781704706309428890585 10880836278529732071667939)
    ·
      refine ⟨16321254417794598107501909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880836278529732071667939 16321254417794598107501909)
      ·
        refine ⟨747127735189572056923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 16321254417794598107501909 747127735189572056923)
        ·
          rfl

theorem cell23_3182142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 16].length) (baseStart_3182142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182142 prefixEnd_3182142 := by exact prefixLift 3182142
  have htrace : WordTrace (prefixWord ++ tailWord_3182142) baseStart_3182142 baseEnd_3182142 := by
    simpa [prefixWord, tailWord_3182142, baseEnd_3182142] using wordTrace_append hprefix tailTrace_3182142
  have hstable : (prefixWord ++ tailWord_3182142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182142).length < 2 ^ (prefixWord ++ tailWord_3182142).sum := by decide
  have hdescent : baseEnd_3182142 < baseStart_3182142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182186 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3182186 : Nat := 118140960795 + 3182186 * 2 ^ 59
def prefixEnd_3182186 : Nat := 4983230072969 + 3 ^ 40 * 3182186 * 2
def baseEnd_3182186 : Nat := 1633990950008391916340399

theorem tailTrace_3182186 : CollatzResearch.WordTrace tailWord_3182186 prefixEnd_3182186 1633990950008391916340399 := by
  unfold tailWord_3182186
  simp only [CollatzResearch.WordTrace]
  refine ⟨29015964612372767736431603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77375905632994047297150941 29015964612372767736431603)
  ·
    refine ⟨43523946918559151604647405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29015964612372767736431603 43523946918559151604647405)
    ·
      refine ⟨16321480094459681851742777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43523946918559151604647405 16321480094459681851742777)
      ·
        refine ⟨12241110070844761388807083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16321480094459681851742777 12241110070844761388807083)
        ·
          refine ⟨18361665106267142083210625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241110070844761388807083 18361665106267142083210625)
          ·
            refine ⟨13771248829700356562407969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18361665106267142083210625 13771248829700356562407969)
            ·
              refine ⟨10328436622275267421805977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13771248829700356562407969 10328436622275267421805977)
              ·
                refine ⟨7746327466706450566354483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10328436622275267421805977 7746327466706450566354483)
                ·
                  refine ⟨11619491200059675849531725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746327466706450566354483 11619491200059675849531725)
                  ·
                    refine ⟨4357309200022378443574397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11619491200059675849531725 4357309200022378443574397)
                    ·
                      refine ⟨1633990950008391916340399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357309200022378443574397 1633990950008391916340399)
                      ·
                        rfl

theorem cell23_3182186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3182186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182186 prefixEnd_3182186 := by exact prefixLift 3182186
  have htrace : WordTrace (prefixWord ++ tailWord_3182186) baseStart_3182186 baseEnd_3182186 := by
    simpa [prefixWord, tailWord_3182186, baseEnd_3182186] using wordTrace_append hprefix tailTrace_3182186
  have hstable : (prefixWord ++ tailWord_3182186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182186).length < 2 ^ (prefixWord ++ tailWord_3182186).sum := by decide
  have hdescent : baseEnd_3182186 < baseStart_3182186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182229 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_3182229 : Nat := 118140960795 + 3182229 * 2 ^ 59
def prefixEnd_3182229 : Nat := 4983230072969 + 3 ^ 40 * 3182229 * 2
def baseEnd_3182229 : Nat := 1634013029676535248102701

theorem tailTrace_3182229 : CollatzResearch.WordTrace tailWord_3182229 prefixEnd_3182229 1634013029676535248102701 := by
  unfold tailWord_3182229
  simp only [CollatzResearch.WordTrace]
  refine ⟨116065426788335289289541741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77376951192223526193027827 116065426788335289289541741)
  ·
    refine ⟨43524535045625733483578153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116065426788335289289541741 43524535045625733483578153)
    ·
      refine ⟨32643401284219300112683615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43524535045625733483578153 32643401284219300112683615)
      ·
        refine ⟨48965101926328950169025423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32643401284219300112683615 48965101926328950169025423)
        ·
          refine ⟨73447652889493425253538135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48965101926328950169025423 73447652889493425253538135)
          ·
            refine ⟨110171479334240137880307203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73447652889493425253538135 110171479334240137880307203)
            ·
              refine ⟨165257219001360206820460805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110171479334240137880307203 165257219001360206820460805)
              ·
                refine ⟨30985728562755038778836401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165257219001360206820460805 30985728562755038778836401)
                ·
                  refine ⟨23239296422066279084127301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30985728562755038778836401 23239296422066279084127301)
                  ·
                    refine ⟨4357368079137427328273869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23239296422066279084127301 4357368079137427328273869)
                    ·
                      refine ⟨1634013029676535248102701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357368079137427328273869 1634013029676535248102701)
                      ·
                        rfl

theorem cell23_3182229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_3182229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182229 prefixEnd_3182229 := by exact prefixLift 3182229
  have htrace : WordTrace (prefixWord ++ tailWord_3182229) baseStart_3182229 baseEnd_3182229 := by
    simpa [prefixWord, tailWord_3182229, baseEnd_3182229] using wordTrace_append hprefix tailTrace_3182229
  have hstable : (prefixWord ++ tailWord_3182229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182229).length < 2 ^ (prefixWord ++ tailWord_3182229).sum := by decide
  have hdescent : baseEnd_3182229 < baseStart_3182229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182266 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_3182266 : Nat := 118140960795 + 3182266 * 2 ^ 59
def prefixEnd_3182266 : Nat := 4983230072969 + 3 ^ 40 * 3182266 * 2
def baseEnd_3182266 : Nat := 181559114273416844815559

theorem tailTrace_3182266 : CollatzResearch.WordTrace tailWord_3182266 prefixEnd_3182266 181559114273416844815559 := by
  unfold tailWord_3182266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29016694072300311152159663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77377850859467496405759101 29016694072300311152159663)
  ·
    refine ⟨43525041108450466728239495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29016694072300311152159663 43525041108450466728239495)
    ·
      refine ⟨65287561662675700092359243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43525041108450466728239495 65287561662675700092359243)
      ·
        refine ⟨97931342494013550138538865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65287561662675700092359243 97931342494013550138538865)
        ·
          refine ⟨73448506870510162603904149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97931342494013550138538865 73448506870510162603904149)
          ·
            refine ⟨3442898759555163872058007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73448506870510162603904149 3442898759555163872058007)
            ·
              refine ⟨5164348139332745808087011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442898759555163872058007 5164348139332745808087011)
              ·
                refine ⟨7746522208999118712130517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164348139332745808087011 7746522208999118712130517)
                ·
                  refine ⟨181559114273416844815559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7746522208999118712130517 181559114273416844815559)
                  ·
                    rfl

theorem cell23_3182266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_3182266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182266 prefixEnd_3182266 := by exact prefixLift 3182266
  have htrace : WordTrace (prefixWord ++ tailWord_3182266) baseStart_3182266 baseEnd_3182266 := by
    simpa [prefixWord, tailWord_3182266, baseEnd_3182266] using wordTrace_append hprefix tailTrace_3182266
  have hstable : (prefixWord ++ tailWord_3182266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182266).length < 2 ^ (prefixWord ++ tailWord_3182266).sum := by decide
  have hdescent : baseEnd_3182266 < baseStart_3182266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182276 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3182276 : Nat := 118140960795 + 3182276 * 2 ^ 59
def prefixEnd_3182276 : Nat := 4983230072969 + 3 ^ 40 * 3182276 * 2
def baseEnd_3182276 : Nat := 1634037163267296564214985

theorem tailTrace_3182276 : CollatzResearch.WordTrace tailWord_3182276 prefixEnd_3182276 1634037163267296564214985 := by
  unfold tailWord_3182276
  simp only [CollatzResearch.WordTrace]
  refine ⟨58033570509582508158251341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77378094012776677544335121 58033570509582508158251341)
  ·
    refine ⟨21762588941093440559344253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58033570509582508158251341 21762588941093440559344253)
    ·
      refine ⟨8160970852910040209754095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21762588941093440559344253 8160970852910040209754095)
      ·
        refine ⟨12241456279365060314631143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8160970852910040209754095 12241456279365060314631143)
        ·
          refine ⟨18362184419047590471946715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241456279365060314631143 18362184419047590471946715)
          ·
            refine ⟨27543276628571385707920073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18362184419047590471946715 27543276628571385707920073)
            ·
              refine ⟨20657457471428539280940055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27543276628571385707920073 20657457471428539280940055)
              ·
                refine ⟨30986186207142808921410083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20657457471428539280940055 30986186207142808921410083)
                ·
                  refine ⟨46479279310714213382115125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30986186207142808921410083 46479279310714213382115125)
                  ·
                    refine ⟨4357432435379457504573293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46479279310714213382115125 4357432435379457504573293)
                    ·
                      refine ⟨1634037163267296564214985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357432435379457504573293 1634037163267296564214985)
                      ·
                        rfl

theorem cell23_3182276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3182276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182276 prefixEnd_3182276 := by exact prefixLift 3182276
  have htrace : WordTrace (prefixWord ++ tailWord_3182276) baseStart_3182276 baseEnd_3182276 := by
    simpa [prefixWord, tailWord_3182276, baseEnd_3182276] using wordTrace_append hprefix tailTrace_3182276
  have hstable : (prefixWord ++ tailWord_3182276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182276).length < 2 ^ (prefixWord ++ tailWord_3182276).sum := by decide
  have hdescent : baseEnd_3182276 < baseStart_3182276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182279 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3182279 : Nat := 118140960795 + 3182279 * 2 ^ 59
def prefixEnd_3182279 : Nat := 4983230072969 + 3 ^ 40 * 3182279 * 2
def baseEnd_3182279 : Nat := 544679567903086684159157

theorem tailTrace_3182279 : CollatzResearch.WordTrace tailWord_3182279 prefixEnd_3182279 544679567903086684159157 := by
  unfold tailWord_3182279
  simp only [CollatzResearch.WordTrace]
  refine ⟨116067250438154147828861891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77378166958769431885907927 116067250438154147828861891)
  ·
    refine ⟨174100875657231221743292837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116067250438154147828861891 174100875657231221743292837)
    ·
      refine ⟨32643914185730854076867407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174100875657231221743292837 32643914185730854076867407)
      ·
        refine ⟨48965871278596281115301111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32643914185730854076867407 48965871278596281115301111)
        ·
          refine ⟨73448806917894421672951667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48965871278596281115301111 73448806917894421672951667)
          ·
            refine ⟨110173210376841632509427501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73448806917894421672951667 110173210376841632509427501)
            ·
              refine ⟨41314953891315612191035313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110173210376841632509427501 41314953891315612191035313)
              ·
                refine ⟨30986215418486709143276485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41314953891315612191035313 30986215418486709143276485)
                ·
                  refine ⟨5809915390966257964364341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30986215418486709143276485 5809915390966257964364341)
                  ·
                    refine ⟨544679567903086684159157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5809915390966257964364341 544679567903086684159157)
                    ·
                      rfl

theorem cell23_3182279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3182279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182279 prefixEnd_3182279 := by exact prefixLift 3182279
  have htrace : WordTrace (prefixWord ++ tailWord_3182279) baseStart_3182279 baseEnd_3182279 := by
    simpa [prefixWord, tailWord_3182279, baseEnd_3182279] using wordTrace_append hprefix tailTrace_3182279
  have hstable : (prefixWord ++ tailWord_3182279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182279).length < 2 ^ (prefixWord ++ tailWord_3182279).sum := by decide
  have hdescent : baseEnd_3182279 < baseStart_3182279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182296 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_3182296 : Nat := 118140960795 + 3182296 * 2 ^ 59
def prefixEnd_3182296 : Nat := 4983230072969 + 3 ^ 40 * 3182296 * 2
def baseEnd_3182296 : Nat := 544682477626795495321631

theorem tailTrace_3182296 : CollatzResearch.WordTrace tailWord_3182296 prefixEnd_3182296 544682477626795495321631 := by
  unfold tailWord_3182296
  simp only [CollatzResearch.WordTrace]
  refine ⟨58033935239546279866115371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77378580319395039821487161 58033935239546279866115371)
  ·
    refine ⟨87050902859319419799173057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58033935239546279866115371 87050902859319419799173057)
    ·
      refine ⟨65288177144489564849379793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87050902859319419799173057 65288177144489564849379793)
      ·
        refine ⟨48966132858367173637034845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65288177144489564849379793 48966132858367173637034845)
        ·
          refine ⟨18362299821887690113888067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48966132858367173637034845 18362299821887690113888067)
          ·
            refine ⟨27543449732831535170832101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18362299821887690113888067 27543449732831535170832101)
            ·
              refine ⟨5164396824905912844531019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27543449732831535170832101 5164396824905912844531019)
              ·
                refine ⟨7746595237358869266796529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164396824905912844531019 7746595237358869266796529)
                ·
                  refine ⟨5809946428019151950097397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746595237358869266796529 5809946428019151950097397)
                  ·
                    refine ⟨544682477626795495321631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5809946428019151950097397 544682477626795495321631)
                    ·
                      rfl

theorem cell23_3182296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_3182296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182296 prefixEnd_3182296 := by exact prefixLift 3182296
  have htrace : WordTrace (prefixWord ++ tailWord_3182296) baseStart_3182296 baseEnd_3182296 := by
    simpa [prefixWord, tailWord_3182296, baseEnd_3182296] using wordTrace_append hprefix tailTrace_3182296
  have hstable : (prefixWord ++ tailWord_3182296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182296).length < 2 ^ (prefixWord ++ tailWord_3182296).sum := by decide
  have hdescent : baseEnd_3182296 < baseStart_3182296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182316 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3182316 : Nat := 118140960795 + 3182316 * 2 ^ 59
def prefixEnd_3182316 : Nat := 4983230072969 + 3 ^ 40 * 3182316 * 2
def baseEnd_3182316 : Nat := 1634057702493476407714801

theorem tailTrace_3182316 : CollatzResearch.WordTrace tailWord_3182316 prefixEnd_3182316 1634057702493476407714801 := by
  unfold tailWord_3182316
  simp only [CollatzResearch.WordTrace]
  refine ⟨58034299969510051573979401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77379066626013402098639201 58034299969510051573979401)
  ·
    refine ⟨43525724977132538680484551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58034299969510051573979401 43525724977132538680484551)
    ·
      refine ⟨65288587465698808020726827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43525724977132538680484551 65288587465698808020726827)
      ·
        refine ⟨97932881198548212031090241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65288587465698808020726827 97932881198548212031090241)
        ·
          refine ⟨73449660898911159023317681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97932881198548212031090241 73449660898911159023317681)
          ·
            refine ⟨55087245674183369267488261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73449660898911159023317681 55087245674183369267488261)
            ·
              refine ⟨10328858563909381737654049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55087245674183369267488261 10328858563909381737654049)
              ·
                refine ⟨7746643922932036303240537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10328858563909381737654049 7746643922932036303240537)
                ·
                  refine ⟨5809982942199027227430403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7746643922932036303240537 5809982942199027227430403)
                  ·
                    refine ⟨8714974413298540841145605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5809982942199027227430403 8714974413298540841145605)
                    ·
                      refine ⟨1634057702493476407714801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8714974413298540841145605 1634057702493476407714801)
                      ·
                        rfl

theorem cell23_3182316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3182316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182316 prefixEnd_3182316 := by exact prefixLift 3182316
  have htrace : WordTrace (prefixWord ++ tailWord_3182316) baseStart_3182316 baseEnd_3182316 := by
    simpa [prefixWord, tailWord_3182316, baseEnd_3182316] using wordTrace_append hprefix tailTrace_3182316
  have hstable : (prefixWord ++ tailWord_3182316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182316).length < 2 ^ (prefixWord ++ tailWord_3182316).sum := by decide
  have hdescent : baseEnd_3182316 < baseStart_3182316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182319 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_3182319 : Nat := 118140960795 + 3182319 * 2 ^ 59
def prefixEnd_3182319 : Nat := 4983230072969 + 3 ^ 40 * 3182319 * 2
def baseEnd_3182319 : Nat := 1634059242935439895977287

theorem tailTrace_3182319 : CollatzResearch.WordTrace tailWord_3182319 prefixEnd_3182319 1634059242935439895977287 := by
  unfold tailWord_3182319
  simp only [CollatzResearch.WordTrace]
  refine ⟨116068709358009234660318011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77379139572006156440212007 116068709358009234660318011)
  ·
    refine ⟨174103064037013851990477017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116068709358009234660318011 174103064037013851990477017)
    ·
      refine ⟨130577298027760388992857763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174103064037013851990477017 130577298027760388992857763)
      ·
        refine ⟨195865947041640583489286645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130577298027760388992857763 195865947041640583489286645)
        ·
          refine ⟨18362432535153804702120623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195865947041640583489286645 18362432535153804702120623)
          ·
            refine ⟨27543648802730707053180935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18362432535153804702120623 27543648802730707053180935)
            ·
              refine ⟨41315473204096060579771403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27543648802730707053180935 41315473204096060579771403)
              ·
                refine ⟨61973209806144090869657105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41315473204096060579771403 61973209806144090869657105)
                ·
                  refine ⟨46479907354608068152242829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61973209806144090869657105 46479907354608068152242829)
                  ·
                    refine ⟨17429965257978025557091061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46479907354608068152242829 17429965257978025557091061)
                    ·
                      refine ⟨1634059242935439895977287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17429965257978025557091061 1634059242935439895977287)
                      ·
                        rfl

theorem cell23_3182319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_3182319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182319 prefixEnd_3182319 := by exact prefixLift 3182319
  have htrace : WordTrace (prefixWord ++ tailWord_3182319) baseStart_3182319 baseEnd_3182319 := by
    simpa [prefixWord, tailWord_3182319, baseEnd_3182319] using wordTrace_append hprefix tailTrace_3182319
  have hstable : (prefixWord ++ tailWord_3182319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182319).length < 2 ^ (prefixWord ++ tailWord_3182319).sum := by decide
  have hdescent : baseEnd_3182319 < baseStart_3182319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182329 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3182329 : Nat := 118140960795 + 3182329 * 2 ^ 59
def prefixEnd_3182329 : Nat := 4983230072969 + 3 ^ 40 * 3182329 * 2
def baseEnd_3182329 : Nat := 1634064377741984856852241

theorem tailTrace_3182329 : CollatzResearch.WordTrace tailWord_3182329 prefixEnd_3182329 1634064377741984856852241 := by
  unfold tailWord_3182329
  simp only [CollatzResearch.WordTrace]
  refine ⟨116069074087973006368182041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77379382725315337578788027 116069074087973006368182041)
  ·
    refine ⟨87051805565979754776136531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116069074087973006368182041 87051805565979754776136531)
    ·
      refine ⟨130577708348969632164204797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87051805565979754776136531 130577708348969632164204797)
      ·
        refine ⟨48966640630863612061576799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130577708348969632164204797 48966640630863612061576799)
        ·
          refine ⟨73449960946295418092365199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48966640630863612061576799 73449960946295418092365199)
          ·
            refine ⟨110174941419443127138547799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73449960946295418092365199 110174941419443127138547799)
            ·
              refine ⟨165262412129164690707821699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110174941419443127138547799 165262412129164690707821699)
              ·
                refine ⟨247893618193747036061732549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165262412129164690707821699 247893618193747036061732549)
                ·
                  refine ⟨46480053411327569261574853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247893618193747036061732549 46480053411327569261574853)
                  ·
                    refine ⟨8715010014623919236545285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46480053411327569261574853 8715010014623919236545285)
                    ·
                      refine ⟨1634064377741984856852241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8715010014623919236545285 1634064377741984856852241)
                      ·
                        rfl

theorem cell23_3182329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3182329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182329 prefixEnd_3182329 := by exact prefixLift 3182329
  have htrace : WordTrace (prefixWord ++ tailWord_3182329) baseStart_3182329 baseEnd_3182329 := by
    simpa [prefixWord, tailWord_3182329, baseEnd_3182329] using wordTrace_append hprefix tailTrace_3182329
  have hstable : (prefixWord ++ tailWord_3182329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182329).length < 2 ^ (prefixWord ++ tailWord_3182329).sum := by decide
  have hdescent : baseEnd_3182329 < baseStart_3182329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182373 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 6]
def baseStart_3182373 : Nat := 118140960795 + 3182373 * 2 ^ 59
def prefixEnd_3182373 : Nat := 4983230072969 + 3 ^ 40 * 3182373 * 2
def baseEnd_3182373 : Nat := 181565218987864742744671

theorem tailTrace_3182373 : CollatzResearch.WordTrace tailWord_3182373 prefixEnd_3182373 181565218987864742744671 := by
  unfold tailWord_3182373
  simp only [CollatzResearch.WordTrace]
  refine ⟨116070678899813601882783773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77380452599875734588522515 116070678899813601882783773)
  ·
    refine ⟨43526504587430100706043915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116070678899813601882783773 43526504587430100706043915)
    ·
      refine ⟨65289756881145151059065873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43526504587430100706043915 65289756881145151059065873)
      ·
        refine ⟨48967317660858863294299405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65289756881145151059065873 48967317660858863294299405)
        ·
          refine ⟨18362744122822073735362277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48967317660858863294299405 18362744122822073735362277)
          ·
            refine ⟨3443014523029138825380427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18362744122822073735362277 3443014523029138825380427)
            ·
              refine ⟨5164521784543708238070641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443014523029138825380427 5164521784543708238070641)
              ·
                refine ⟨3873391338407781178552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164521784543708238070641 3873391338407781178552981)
                ·
                  refine ⟨181565218987864742744671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3873391338407781178552981 181565218987864742744671)
                  ·
                    rfl

theorem cell23_3182373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_3182373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182373 prefixEnd_3182373 := by exact prefixLift 3182373
  have htrace : WordTrace (prefixWord ++ tailWord_3182373) baseStart_3182373 baseEnd_3182373 := by
    simpa [prefixWord, tailWord_3182373, baseEnd_3182373] using wordTrace_append hprefix tailTrace_3182373
  have hstable : (prefixWord ++ tailWord_3182373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182373).length < 2 ^ (prefixWord ++ tailWord_3182373).sum := by decide
  have hdescent : baseEnd_3182373 < baseStart_3182373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182376 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3182376 : Nat := 118140960795 + 3182376 * 2 ^ 59
def prefixEnd_3182376 : Nat := 4983230072969 + 3 ^ 40 * 3182376 * 2
def baseEnd_3182376 : Nat := 1634088511332746172964525

theorem tailTrace_3182376 : CollatzResearch.WordTrace tailWord_3182376 prefixEnd_3182376 1634088511332746172964525 := by
  unfold tailWord_3182376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58035394159401366697571491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77380525545868488930095321 58035394159401366697571491)
  ·
    refine ⟨87053091239102050046357237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58035394159401366697571491 87053091239102050046357237)
    ·
      refine ⟨8161227303665817191845991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87053091239102050046357237 8161227303665817191845991)
      ·
        refine ⟨12241840955498725787768987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161227303665817191845991 12241840955498725787768987)
        ·
          refine ⟨18362761433248088681653481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241840955498725787768987 18362761433248088681653481)
          ·
            refine ⟨13772071074936066511240111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18362761433248088681653481 13772071074936066511240111)
            ·
              refine ⟨20658106612404099766860167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772071074936066511240111 20658106612404099766860167)
              ·
                refine ⟨30987159918606149650290251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20658106612404099766860167 30987159918606149650290251)
                ·
                  refine ⟨46480739877909224475435377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30987159918606149650290251 46480739877909224475435377)
                  ·
                    refine ⟨34860554908431918356576533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46480739877909224475435377 34860554908431918356576533)
                    ·
                      refine ⟨1634088511332746172964525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34860554908431918356576533 1634088511332746172964525)
                      ·
                        rfl

theorem cell23_3182376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3182376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182376 prefixEnd_3182376 := by exact prefixLift 3182376
  have htrace : WordTrace (prefixWord ++ tailWord_3182376) baseStart_3182376 baseEnd_3182376 := by
    simpa [prefixWord, tailWord_3182376, baseEnd_3182376] using wordTrace_append hprefix tailTrace_3182376
  have hstable : (prefixWord ++ tailWord_3182376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182376).length < 2 ^ (prefixWord ++ tailWord_3182376).sum := by decide
  have hdescent : baseEnd_3182376 < baseStart_3182376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182403 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 1, 5]
def baseStart_3182403 : Nat := 118140960795 + 3182403 * 2 ^ 59
def prefixEnd_3182403 : Nat := 4983230072969 + 3 ^ 40 * 3182403 * 2
def baseEnd_3182403 : Nat := 544700791770139189108967

theorem tailTrace_3182403 : CollatzResearch.WordTrace tailWord_3182403 prefixEnd_3182403 544700791770139189108967 := by
  unfold tailWord_3182403
  simp only [CollatzResearch.WordTrace]
  refine ⟨116071773089704917006375863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77381182059803278004250575 116071773089704917006375863)
  ·
    refine ⟨174107659634557375509563795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116071773089704917006375863 174107659634557375509563795)
    ·
      refine ⟨261161489451836063264345693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174107659634557375509563795 261161489451836063264345693)
      ·
        refine ⟨97935558544438523724129635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261161489451836063264345693 97935558544438523724129635)
        ·
          refine ⟨146903337816657785586194453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97935558544438523724129635 146903337816657785586194453)
          ·
            refine ⟨6886093960155833699352865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146903337816657785586194453 6886093960155833699352865)
            ·
              refine ⟨5164570470116875274514649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6886093960155833699352865 5164570470116875274514649)
              ·
                refine ⟨3873427852587656455885987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164570470116875274514649 3873427852587656455885987)
                ·
                  refine ⟨5810141778881484683828981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873427852587656455885987 5810141778881484683828981)
                  ·
                    refine ⟨544700791770139189108967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5810141778881484683828981 544700791770139189108967)
                    ·
                      rfl

theorem cell23_3182403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 5].length) (baseStart_3182403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182403 prefixEnd_3182403 := by exact prefixLift 3182403
  have htrace : WordTrace (prefixWord ++ tailWord_3182403) baseStart_3182403 baseEnd_3182403 := by
    simpa [prefixWord, tailWord_3182403, baseEnd_3182403] using wordTrace_append hprefix tailTrace_3182403
  have hstable : (prefixWord ++ tailWord_3182403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182403).length < 2 ^ (prefixWord ++ tailWord_3182403).sum := by decide
  have hdescent : baseEnd_3182403 < baseStart_3182403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182417 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_3182417 : Nat := 118140960795 + 3182417 * 2 ^ 59
def prefixEnd_3182417 : Nat := 4983230072969 + 3 ^ 40 * 3182417 * 2
def baseEnd_3182417 : Nat := 1634109564039580512551837

theorem tailTrace_3182417 : CollatzResearch.WordTrace tailWord_3182417 prefixEnd_3182417 1634109564039580512551837 := by
  unfold tailWord_3182417
  simp only [CollatzResearch.WordTrace]
  refine ⟨116072283711654197397385505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77381522474436131598257003 116072283711654197397385505)
  ·
    refine ⟨87054212783740648048039129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116072283711654197397385505 87054212783740648048039129)
    ·
      refine ⟨65290659587805486036029347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87054212783740648048039129 65290659587805486036029347)
      ·
        refine ⟨97935989381708229054044021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65290659587805486036029347 97935989381708229054044021)
        ·
          refine ⟨9181499004535146473816627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97935989381708229054044021 9181499004535146473816627)
          ·
            refine ⟨13772248506802719710724941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181499004535146473816627 13772248506802719710724941)
            ·
              refine ⟨5164593190051019891521853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13772248506802719710724941 5164593190051019891521853)
              ·
                refine ⟨1936722446269132459320695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5164593190051019891521853 1936722446269132459320695)
                ·
                  refine ⟨2905083669403698688981043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936722446269132459320695 2905083669403698688981043)
                  ·
                    refine ⟨4357625504105548033471565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905083669403698688981043 4357625504105548033471565)
                    ·
                      refine ⟨1634109564039580512551837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357625504105548033471565 1634109564039580512551837)
                      ·
                        rfl

theorem cell23_3182417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_3182417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182417 prefixEnd_3182417 := by exact prefixLift 3182417
  have htrace : WordTrace (prefixWord ++ tailWord_3182417) baseStart_3182417 baseEnd_3182417 := by
    simpa [prefixWord, tailWord_3182417, baseEnd_3182417] using wordTrace_append hprefix tailTrace_3182417
  have hstable : (prefixWord ++ tailWord_3182417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182417).length < 2 ^ (prefixWord ++ tailWord_3182417).sum := by decide
  have hdescent : baseEnd_3182417 < baseStart_3182417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182433 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3182433 : Nat := 118140960795 + 3182433 * 2 ^ 59
def prefixEnd_3182433 : Nat := 4983230072969 + 3 ^ 40 * 3182433 * 2
def baseEnd_3182433 : Nat := 544705926576684149983921

theorem tailTrace_3182433 : CollatzResearch.WordTrace tailWord_3182433 prefixEnd_3182433 544705926576684149983921 := by
  unfold tailWord_3182433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116072867279596232129967953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77381911519730821419978635 116072867279596232129967953)
  ·
    refine ⟨87054650459697174097475965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116072867279596232129967953 87054650459697174097475965)
    ·
      refine ⟨32645493922386440286553487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87054650459697174097475965 32645493922386440286553487)
      ·
        refine ⟨48968240883579660429830231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32645493922386440286553487 48968240883579660429830231)
        ·
          refine ⟨73452361325369490644745347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48968240883579660429830231 73452361325369490644745347)
          ·
            refine ⟨110178541988054235967118021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73452361325369490644745347 110178541988054235967118021)
            ·
              refine ⟨20658476622760169243834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110178541988054235967118021 20658476622760169243834629)
              ·
                refine ⟨3873464366767531733218993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20658476622760169243834629 3873464366767531733218993)
                ·
                  refine ⟨2905098275075648799914245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873464366767531733218993 2905098275075648799914245)
                  ·
                    refine ⟨544705926576684149983921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905098275075648799914245 544705926576684149983921)
                    ·
                      rfl

theorem cell23_3182433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3182433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182433 prefixEnd_3182433 := by exact prefixLift 3182433
  have htrace : WordTrace (prefixWord ++ tailWord_3182433) baseStart_3182433 baseEnd_3182433 := by
    simpa [prefixWord, tailWord_3182433, baseEnd_3182433] using wordTrace_append hprefix tailTrace_3182433
  have hstable : (prefixWord ++ tailWord_3182433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182433).length < 2 ^ (prefixWord ++ tailWord_3182433).sum := by decide
  have hdescent : baseEnd_3182433 < baseStart_3182433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182453 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3182453 : Nat := 118140960795 + 3182453 * 2 ^ 59
def prefixEnd_3182453 : Nat := 4983230072969 + 3 ^ 40 * 3182453 * 2
def baseEnd_3182453 : Nat := 1634128049343142371701671

theorem tailTrace_3182453 : CollatzResearch.WordTrace tailWord_3182453 prefixEnd_3182453 1634128049343142371701671 := by
  unfold tailWord_3182453
  simp only [CollatzResearch.WordTrace]
  refine ⟨116073596739523775545696013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77382397826349183697130675 116073596739523775545696013)
  ·
    refine ⟨43527598777321415829636005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116073596739523775545696013 43527598777321415829636005)
    ·
      refine ⟨8161424770747765468056751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43527598777321415829636005 8161424770747765468056751)
      ·
        refine ⟨12242137156121648202085127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161424770747765468056751 12242137156121648202085127)
        ·
          refine ⟨18363205734182472303127691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12242137156121648202085127 18363205734182472303127691)
          ·
            refine ⟨27544808601273708454691537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363205734182472303127691 27544808601273708454691537)
            ·
              refine ⟨20658606450955281341018653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27544808601273708454691537 20658606450955281341018653)
              ·
                refine ⟨7746977419108230502881995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20658606450955281341018653 7746977419108230502881995)
                ·
                  refine ⟨11620466128662345754322993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746977419108230502881995 11620466128662345754322993)
                  ·
                    refine ⟨8715349596496759315742245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11620466128662345754322993 8715349596496759315742245)
                    ·
                      refine ⟨1634128049343142371701671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8715349596496759315742245 1634128049343142371701671)
                      ·
                        rfl

theorem cell23_3182453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3182453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182453 prefixEnd_3182453 := by exact prefixLift 3182453
  have htrace : WordTrace (prefixWord ++ tailWord_3182453) baseStart_3182453 baseEnd_3182453 := by
    simpa [prefixWord, tailWord_3182453, baseEnd_3182453] using wordTrace_append hprefix tailTrace_3182453
  have hstable : (prefixWord ++ tailWord_3182453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182453).length < 2 ^ (prefixWord ++ tailWord_3182453).sum := by decide
  have hdescent : baseEnd_3182453 < baseStart_3182453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182454 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_3182454 : Nat := 118140960795 + 3182454 * 2 ^ 59
def prefixEnd_3182454 : Nat := 4983230072969 + 3 ^ 40 * 3182454 * 2
def baseEnd_3182454 : Nat := 544709520941265622596389

theorem tailTrace_3182454 : CollatzResearch.WordTrace tailWord_3182454 prefixEnd_3182454 544709520941265622596389 := by
  unfold tailWord_3182454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254602075782509544780151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77382422141680101810988277 7254602075782509544780151)
  ·
    refine ⟨10881903113673764317170227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254602075782509544780151 10881903113673764317170227)
    ·
      refine ⟨16322854670510646475755341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10881903113673764317170227 16322854670510646475755341)
      ·
        refine ⟨6121070501441492428408253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16322854670510646475755341 6121070501441492428408253)
        ·
          refine ⟨2295401438040559660653095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6121070501441492428408253 2295401438040559660653095)
          ·
            refine ⟨3443102157060839490979643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295401438040559660653095 3443102157060839490979643)
            ·
              refine ⟨5164653235591259236469465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443102157060839490979643 5164653235591259236469465)
              ·
                refine ⟨3873489926693444427352099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5164653235591259236469465 3873489926693444427352099)
                ·
                  refine ⟨5810234890040166641028149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873489926693444427352099 5810234890040166641028149)
                  ·
                    refine ⟨544709520941265622596389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5810234890040166641028149 544709520941265622596389)
                    ·
                      rfl

theorem cell23_3182454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_3182454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182454 prefixEnd_3182454 := by exact prefixLift 3182454
  have htrace : WordTrace (prefixWord ++ tailWord_3182454) baseStart_3182454 baseEnd_3182454 := by
    simpa [prefixWord, tailWord_3182454, baseEnd_3182454] using wordTrace_append hprefix tailTrace_3182454
  have hstable : (prefixWord ++ tailWord_3182454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182454).length < 2 ^ (prefixWord ++ tailWord_3182454).sum := by decide
  have hdescent : baseEnd_3182454 < baseStart_3182454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182473 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_3182473 : Nat := 118140960795 + 3182473 * 2 ^ 59
def prefixEnd_3182473 : Nat := 4983230072969 + 3 ^ 40 * 3182473 * 2
def baseEnd_3182473 : Nat := 1634138318956232293451579

theorem tailTrace_3182473 : CollatzResearch.WordTrace tailWord_3182473 prefixEnd_3182473 1634138318956232293451579 := by
  unfold tailWord_3182473
  simp only [CollatzResearch.WordTrace]
  refine ⟨116074326199451318961424073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77382884132967545974282715 116074326199451318961424073)
  ·
    refine ⟨87055744649588489221068055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116074326199451318961424073 87055744649588489221068055)
    ·
      refine ⟨130583616974382733831602083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87055744649588489221068055 130583616974382733831602083)
      ·
        refine ⟨195875425461574100747403125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130583616974382733831602083 195875425461574100747403125)
        ·
          refine ⟨18363321137022571945069043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195875425461574100747403125 18363321137022571945069043)
          ·
            refine ⟨27544981705533857917603565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363321137022571945069043 27544981705533857917603565)
            ·
              refine ⟨10329368139575196719101337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27544981705533857917603565 10329368139575196719101337)
              ·
                refine ⟨7747026104681397539326003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10329368139575196719101337 7747026104681397539326003)
                ·
                  refine ⟨11620539157022096308989005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747026104681397539326003 11620539157022096308989005)
                  ·
                    refine ⟨4357702183883286115870877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11620539157022096308989005 4357702183883286115870877)
                    ·
                      refine ⟨1634138318956232293451579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357702183883286115870877 1634138318956232293451579)
                      ·
                        rfl

theorem cell23_3182473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_3182473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182473 prefixEnd_3182473 := by exact prefixLift 3182473
  have htrace : WordTrace (prefixWord ++ tailWord_3182473) baseStart_3182473 baseEnd_3182473 := by
    simpa [prefixWord, tailWord_3182473, baseEnd_3182473] using wordTrace_append hprefix tailTrace_3182473
  have hstable : (prefixWord ++ tailWord_3182473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182473).length < 2 ^ (prefixWord ++ tailWord_3182473).sum := by decide
  have hdescent : baseEnd_3182473 < baseStart_3182473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182500 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_3182500 : Nat := 118140960795 + 3182500 * 2 ^ 59
def prefixEnd_3182500 : Nat := 4983230072969 + 3 ^ 40 * 3182500 * 2
def baseEnd_3182500 : Nat := 1634152182933903687813955

theorem tailTrace_3182500 : CollatzResearch.WordTrace tailWord_3182500 prefixEnd_3182500 1634152182933903687813955 := by
  unfold tailWord_3182500
  simp only [CollatzResearch.WordTrace]
  refine ⟨58037655485176751286328477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77383540646902335048437969 58037655485176751286328477)
  ·
    refine ⟨21764120806941281732373179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58037655485176751286328477 21764120806941281732373179)
    ·
      refine ⟨32646181210411922598559769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21764120806941281732373179 32646181210411922598559769)
      ·
        refine ⟨24484635907808941948919827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32646181210411922598559769 24484635907808941948919827)
        ·
          refine ⟨36726953861713412923379741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24484635907808941948919827 36726953861713412923379741)
          ·
            refine ⟨13772607698142529846267403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36726953861713412923379741 13772607698142529846267403)
            ·
              refine ⟨20658911547213794769401105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772607698142529846267403 20658911547213794769401105)
              ·
                refine ⟨15494183660410346077050829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20658911547213794769401105 15494183660410346077050829)
                ·
                  refine ⟨5810318872653879778894061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15494183660410346077050829 5810318872653879778894061)
                  ·
                    refine ⟨2178869577245204917085273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5810318872653879778894061 2178869577245204917085273)
                    ·
                      refine ⟨1634152182933903687813955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178869577245204917085273 1634152182933903687813955)
                      ·
                        rfl

theorem cell23_3182500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_3182500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182500 prefixEnd_3182500 := by exact prefixLift 3182500
  have htrace : WordTrace (prefixWord ++ tailWord_3182500) baseStart_3182500 baseEnd_3182500 := by
    simpa [prefixWord, tailWord_3182500, baseEnd_3182500] using wordTrace_append hprefix tailTrace_3182500
  have hstable : (prefixWord ++ tailWord_3182500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182500).length < 2 ^ (prefixWord ++ tailWord_3182500).sum := by decide
  have hdescent : baseEnd_3182500 < baseStart_3182500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182564 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_3182564 : Nat := 118140960795 + 3182564 * 2 ^ 59
def prefixEnd_3182564 : Nat := 4983230072969 + 3 ^ 40 * 3182564 * 2
def baseEnd_3182564 : Nat := 1634185045695791437413661

theorem tailTrace_3182564 : CollatzResearch.WordTrace tailWord_3182564 prefixEnd_3182564 1634185045695791437413661 := by
  unfold tailWord_3182564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038822621060820751493373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77385096828081094335324497 58038822621060820751493373)
  ·
    refine ⟨21764558482897807781810015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58038822621060820751493373 21764558482897807781810015)
    ·
      refine ⟨32646837724346711672715023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21764558482897807781810015 32646837724346711672715023)
      ·
        refine ⟨48970256586520067509072535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32646837724346711672715023 48970256586520067509072535)
        ·
          refine ⟨73455384879780101263608803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48970256586520067509072535 73455384879780101263608803)
          ·
            refine ⟨110183077319670151895413205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73455384879780101263608803 110183077319670151895413205)
            ·
              refine ⟨2582415874679769185048747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110183077319670151895413205 2582415874679769185048747)
              ·
                refine ⟨3873623812019653777573121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582415874679769185048747 3873623812019653777573121)
                ·
                  refine ⟨2905217859014740333179841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873623812019653777573121 2905217859014740333179841)
                  ·
                    refine ⟨2178913394261055249884881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905217859014740333179841 2178913394261055249884881)
                    ·
                      refine ⟨1634185045695791437413661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2178913394261055249884881 1634185045695791437413661)
                      ·
                        rfl

theorem cell23_3182564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_3182564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182564 prefixEnd_3182564 := by exact prefixLift 3182564
  have htrace : WordTrace (prefixWord ++ tailWord_3182564) baseStart_3182564 baseEnd_3182564 := by
    simpa [prefixWord, tailWord_3182564, baseEnd_3182564] using wordTrace_append hprefix tailTrace_3182564
  have hstable : (prefixWord ++ tailWord_3182564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182564).length < 2 ^ (prefixWord ++ tailWord_3182564).sum := by decide
  have hdescent : baseEnd_3182564 < baseStart_3182564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182593 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3182593 : Nat := 118140960795 + 3182593 * 2 ^ 59
def prefixEnd_3182593 : Nat := 4983230072969 + 3 ^ 40 * 3182593 * 2
def baseEnd_3182593 : Nat := 1634199936634771823951027

theorem tailTrace_3182593 : CollatzResearch.WordTrace tailWord_3182593 prefixEnd_3182593 1634199936634771823951027 := by
  unfold tailWord_3182593
  simp only [CollatzResearch.WordTrace]
  refine ⟨116078702959016579455792433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77385801972677719637194955 116078702959016579455792433)
  ·
    refine ⟨87059027219262434591844325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116078702959016579455792433 87059027219262434591844325)
    ·
      refine ⟨16323567603611706485970811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87059027219262434591844325 16323567603611706485970811)
      ·
        refine ⟨24485351405417559728956217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16323567603611706485970811 24485351405417559728956217)
        ·
          refine ⟨18364013554063169796717163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24485351405417559728956217 18364013554063169796717163)
          ·
            refine ⟨27546020331094754695075745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18364013554063169796717163 27546020331094754695075745)
            ·
              refine ⟨20659515248321066021306809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27546020331094754695075745 20659515248321066021306809)
              ·
                refine ⟨15494636436240799515980107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20659515248321066021306809 15494636436240799515980107)
                ·
                  refine ⟨23241954654361199273970161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15494636436240799515980107 23241954654361199273970161)
                  ·
                    refine ⟨17431465990770899455477621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23241954654361199273970161 17431465990770899455477621)
                    ·
                      refine ⟨1634199936634771823951027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17431465990770899455477621 1634199936634771823951027)
                      ·
                        rfl

theorem cell23_3182593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3182593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182593 prefixEnd_3182593 := by exact prefixLift 3182593
  have htrace : WordTrace (prefixWord ++ tailWord_3182593) baseStart_3182593 baseEnd_3182593 := by
    simpa [prefixWord, tailWord_3182593, baseEnd_3182593] using wordTrace_append hprefix tailTrace_3182593
  have hstable : (prefixWord ++ tailWord_3182593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182593).length < 2 ^ (prefixWord ++ tailWord_3182593).sum := by decide
  have hdescent : baseEnd_3182593 < baseStart_3182593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182640 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_3182640 : Nat := 118140960795 + 3182640 * 2 ^ 59
def prefixEnd_3182640 : Nat := 4983230072969 + 3 ^ 40 * 3182640 * 2
def baseEnd_3182640 : Nat := 1634224070225533140063311

theorem tailTrace_3182640 : CollatzResearch.WordTrace tailWord_3182640 prefixEnd_3182640 1634224070225533140063311 := by
  unfold tailWord_3182640
  simp only [CollatzResearch.WordTrace]
  refine ⟨58040208594923153241376687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77386944793230870988502249 58040208594923153241376687)
  ·
    refine ⟨87060312892384729862065031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58040208594923153241376687 87060312892384729862065031)
    ·
      refine ⟨130590469338577094793097547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87060312892384729862065031 130590469338577094793097547)
      ·
        refine ⟨195885704007865642189646321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130590469338577094793097547 195885704007865642189646321)
        ·
          refine ⟨146914278005899231642234741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195885704007865642189646321 146914278005899231642234741)
          ·
            refine ⟨13773213563053052966459507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146914278005899231642234741 13773213563053052966459507)
            ·
              refine ⟨20659820344579579449689261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773213563053052966459507 20659820344579579449689261)
              ·
                refine ⟨7747432629217342293633473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20659820344579579449689261 7747432629217342293633473)
                ·
                  refine ⟨5810574471913006720225105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7747432629217342293633473 5810574471913006720225105)
                  ·
                    refine ⟨4357930853934755040168829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810574471913006720225105 4357930853934755040168829)
                    ·
                      refine ⟨1634224070225533140063311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357930853934755040168829 1634224070225533140063311)
                      ·
                        rfl

theorem cell23_3182640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_3182640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182640 prefixEnd_3182640 := by exact prefixLift 3182640
  have htrace : WordTrace (prefixWord ++ tailWord_3182640) baseStart_3182640 baseEnd_3182640 := by
    simpa [prefixWord, tailWord_3182640, baseEnd_3182640] using wordTrace_append hprefix tailTrace_3182640
  have hstable : (prefixWord ++ tailWord_3182640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182640).length < 2 ^ (prefixWord ++ tailWord_3182640).sum := by decide
  have hdescent : baseEnd_3182640 < baseStart_3182640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182657 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3182657 : Nat := 118140960795 + 3182657 * 2 ^ 59
def prefixEnd_3182657 : Nat := 4983230072969 + 3 ^ 40 * 3182657 * 2
def baseEnd_3182657 : Nat := 1634232799396659573550733

theorem tailTrace_3182657 : CollatzResearch.WordTrace tailWord_3182657 prefixEnd_3182657 1634232799396659573550733 := by
  unfold tailWord_3182657
  simp only [CollatzResearch.WordTrace]
  refine ⟨116081037230784718386122225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77387358153856478924081483 116081037230784718386122225)
  ·
    refine ⟨87060777923088538789591669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116081037230784718386122225 87060777923088538789591669)
    ·
      refine ⟨8161947930289550511524219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87060777923088538789591669 8161947930289550511524219)
      ·
        refine ⟨12242921895434325767286329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161947930289550511524219 12242921895434325767286329)
        ·
          refine ⟨9182191421575744325464747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12242921895434325767286329 9182191421575744325464747)
          ·
            refine ⟨13773287132363616488197121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9182191421575744325464747 13773287132363616488197121)
            ·
              refine ⟨10329965349272712366147841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13773287132363616488197121 10329965349272712366147841)
              ·
                refine ⟨7747474011954534274610881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10329965349272712366147841 7747474011954534274610881)
                ·
                  refine ⟨5810605508965900705958161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7747474011954534274610881 5810605508965900705958161)
                  ·
                    refine ⟨4357954131724425529468621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5810605508965900705958161 4357954131724425529468621)
                    ·
                      refine ⟨1634232799396659573550733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4357954131724425529468621 1634232799396659573550733)
                      ·
                        rfl

theorem cell23_3182657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3182657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182657 prefixEnd_3182657 := by exact prefixLift 3182657
  have htrace : WordTrace (prefixWord ++ tailWord_3182657) baseStart_3182657 baseEnd_3182657 := by
    simpa [prefixWord, tailWord_3182657, baseEnd_3182657] using wordTrace_append hprefix tailTrace_3182657
  have hstable : (prefixWord ++ tailWord_3182657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182657).length < 2 ^ (prefixWord ++ tailWord_3182657).sum := by decide
  have hdescent : baseEnd_3182657 < baseStart_3182657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182663 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3182663 : Nat := 118140960795 + 3182663 * 2 ^ 59
def prefixEnd_3182663 : Nat := 4983230072969 + 3 ^ 40 * 3182663 * 2
def baseEnd_3182663 : Nat := 1634235880280586550075705

theorem tailTrace_3182663 : CollatzResearch.WordTrace tailWord_3182663 prefixEnd_3182663 1634235880280586550075705 := by
  unfold tailWord_3182663
  simp only [CollatzResearch.WordTrace]
  refine ⟨116081256068762981410840643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77387504045841987607227095 116081256068762981410840643)
  ·
    refine ⟨174121884103144472116260965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116081256068762981410840643 174121884103144472116260965)
    ·
      refine ⟨32647853269339588521798931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174121884103144472116260965 32647853269339588521798931)
      ·
        refine ⟨48971779904009382782698397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32647853269339588521798931 48971779904009382782698397)
        ·
          refine ⟨18364417464003518543511899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48971779904009382782698397 18364417464003518543511899)
          ·
            refine ⟨27546626196005277815267849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18364417464003518543511899 27546626196005277815267849)
            ·
              refine ⟨20659969647003958361450887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27546626196005277815267849 20659969647003958361450887)
              ·
                refine ⟨30989954470505937542176331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20659969647003958361450887 30989954470505937542176331)
                ·
                  refine ⟨46484931705758906313264497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30989954470505937542176331 46484931705758906313264497)
                  ·
                    refine ⟨34863698779319179734948373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46484931705758906313264497 34863698779319179734948373)
                    ·
                      refine ⟨1634235880280586550075705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34863698779319179734948373 1634235880280586550075705)
                      ·
                        rfl

theorem cell23_3182663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3182663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182663 prefixEnd_3182663 := by exact prefixLift 3182663
  have htrace : WordTrace (prefixWord ++ tailWord_3182663) baseStart_3182663 baseEnd_3182663 := by
    simpa [prefixWord, tailWord_3182663, baseEnd_3182663] using wordTrace_append hprefix tailTrace_3182663
  have hstable : (prefixWord ++ tailWord_3182663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182663).length < 2 ^ (prefixWord ++ tailWord_3182663).sum := by decide
  have hdescent : baseEnd_3182663 < baseStart_3182663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182704 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 1, 1, 3]
def baseStart_3182704 : Nat := 118140960795 + 3182704 * 2 ^ 59
def prefixEnd_3182704 : Nat := 4983230072969 + 3 ^ 40 * 3182704 * 2
def baseEnd_3182704 : Nat := 1634256932987420889663017

theorem tailTrace_3182704 : CollatzResearch.WordTrace tailWord_3182704 prefixEnd_3182704 1634256932987420889663017 := by
  unfold tailWord_3182704
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041375730807222706541583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77388500974409630275388777 58041375730807222706541583)
  ·
    refine ⟨87062063596210834059812375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58041375730807222706541583 87062063596210834059812375)
    ·
      refine ⟨130593095394316251089718563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87062063596210834059812375 130593095394316251089718563)
      ·
        refine ⟨195889643091474376634577845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130593095394316251089718563 195889643091474376634577845)
        ·
          refine ⟨18364654039825722809491673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195889643091474376634577845 18364654039825722809491673)
          ·
            refine ⟨13773490529869292107118755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18364654039825722809491673 13773490529869292107118755)
            ·
              refine ⟨20660235794803938160678133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773490529869292107118755 20660235794803938160678133)
              ·
                refine ⟨1936897105762869202563575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20660235794803938160678133 1936897105762869202563575)
                ·
                  refine ⟨2905345658644303803845363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1936897105762869202563575 2905345658644303803845363)
                  ·
                    refine ⟨4358018487966455705768045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905345658644303803845363 4358018487966455705768045)
                    ·
                      refine ⟨1634256932987420889663017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358018487966455705768045 1634256932987420889663017)
                      ·
                        rfl

theorem cell23_3182704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 1, 3].length) (baseStart_3182704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182704 prefixEnd_3182704 := by exact prefixLift 3182704
  have htrace : WordTrace (prefixWord ++ tailWord_3182704) baseStart_3182704 baseEnd_3182704 := by
    simpa [prefixWord, tailWord_3182704, baseEnd_3182704] using wordTrace_append hprefix tailTrace_3182704
  have hstable : (prefixWord ++ tailWord_3182704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182704).length < 2 ^ (prefixWord ++ tailWord_3182704).sum := by decide
  have hdescent : baseEnd_3182704 < baseStart_3182704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182730 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3182730 : Nat := 118140960795 + 3182730 * 2 ^ 59
def prefixEnd_3182730 : Nat := 4983230072969 + 3 ^ 40 * 3182730 * 2
def baseEnd_3182730 : Nat := 1634270283484437787937897

theorem tailTrace_3182730 : CollatzResearch.WordTrace tailWord_3182730 prefixEnd_3182730 1634270283484437787937897 := by
  unfold tailWord_3182730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29020924939880062963382411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77389133173013501235686429 29020924939880062963382411)
  ·
    refine ⟨43531387409820094445073617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29020924939880062963382411 43531387409820094445073617)
    ·
      refine ⟨32648540557365070833805213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43531387409820094445073617 32648540557365070833805213)
      ·
        refine ⟨12243202709011901562676955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32648540557365070833805213 12243202709011901562676955)
        ·
          refine ⟨18364804063517852344015433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12243202709011901562676955 18364804063517852344015433)
          ·
            refine ⟨13773603047638389258011575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18364804063517852344015433 13773603047638389258011575)
            ·
              refine ⟨20660404571457583887017363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13773603047638389258011575 20660404571457583887017363)
              ·
                refine ⟨30990606857186375830526045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20660404571457583887017363 30990606857186375830526045)
                ·
                  refine ⟨11621477571444890936447267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30990606857186375830526045 11621477571444890936447267)
                  ·
                    refine ⟨17432216357167336404670901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11621477571444890936447267 17432216357167336404670901)
                    ·
                      refine ⟨1634270283484437787937897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17432216357167336404670901 1634270283484437787937897)
                      ·
                        rfl

theorem cell23_3182730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3182730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182730 prefixEnd_3182730 := by exact prefixLift 3182730
  have htrace : WordTrace (prefixWord ++ tailWord_3182730) baseStart_3182730 baseEnd_3182730 := by
    simpa [prefixWord, tailWord_3182730, baseEnd_3182730] using wordTrace_append hprefix tailTrace_3182730
  have hstable : (prefixWord ++ tailWord_3182730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182730).length < 2 ^ (prefixWord ++ tailWord_3182730).sum := by decide
  have hdescent : baseEnd_3182730 < baseStart_3182730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182744 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3182744 : Nat := 118140960795 + 3182744 * 2 ^ 59
def prefixEnd_3182744 : Nat := 4983230072969 + 3 ^ 40 * 3182744 * 2
def baseEnd_3182744 : Nat := 1634277472213600733162833

theorem tailTrace_3182744 : CollatzResearch.WordTrace tailWord_3182744 prefixEnd_3182744 1634277472213600733162833 := by
  unfold tailWord_3182744
  simp only [CollatzResearch.WordTrace]
  refine ⟨58042105190734766122269643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77389473587646354829692857 58042105190734766122269643)
  ·
    refine ⟨87063157786102149183404465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58042105190734766122269643 87063157786102149183404465)
    ·
      refine ⟨65297368339576611887553349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87063157786102149183404465 65297368339576611887553349)
      ·
        refine ⟨12243256563670614728916253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65297368339576611887553349 12243256563670614728916253)
        ·
          refine ⟨4591221211376480523343595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12243256563670614728916253 4591221211376480523343595)
          ·
            refine ⟨6886831817064720785015393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591221211376480523343595 6886831817064720785015393)
            ·
              refine ⟨5165123862798540588761545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6886831817064720785015393 5165123862798540588761545)
              ·
                refine ⟨3873842897098905441571159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5165123862798540588761545 3873842897098905441571159)
                ·
                  refine ⟨5810764345648358162356739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873842897098905441571159 5810764345648358162356739)
                  ·
                    refine ⟨8716146518472537243535109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5810764345648358162356739 8716146518472537243535109)
                    ·
                      refine ⟨1634277472213600733162833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8716146518472537243535109 1634277472213600733162833)
                      ·
                        rfl

theorem cell23_3182744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3182744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182744 prefixEnd_3182744 := by exact prefixLift 3182744
  have htrace : WordTrace (prefixWord ++ tailWord_3182744) baseStart_3182744 baseEnd_3182744 := by
    simpa [prefixWord, tailWord_3182744, baseEnd_3182744] using wordTrace_append hprefix tailTrace_3182744
  have hstable : (prefixWord ++ tailWord_3182744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182744).length < 2 ^ (prefixWord ++ tailWord_3182744).sum := by decide
  have hdescent : baseEnd_3182744 < baseStart_3182744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182772 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3182772 : Nat := 118140960795 + 3182772 * 2 ^ 59
def prefixEnd_3182772 : Nat := 4983230072969 + 3 ^ 40 * 3182772 * 2
def baseEnd_3182772 : Nat := 1634291849671926623612705

theorem tailTrace_3182772 : CollatzResearch.WordTrace tailWord_3182772 prefixEnd_3182772 1634291849671926623612705 := by
  unfold tailWord_3182772
  simp only [CollatzResearch.WordTrace]
  refine ⟨58042615812684046513279285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77390154416912062017705713 58042615812684046513279285)
  ·
    refine ⟨5441495232439129360619933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58042615812684046513279285 5441495232439129360619933)
    ·
      refine ⟨2040560712164673510232475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5441495232439129360619933 2040560712164673510232475)
      ·
        refine ⟨3060841068247010265348713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040560712164673510232475 3060841068247010265348713)
        ·
          refine ⟨2295630801185257699011535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060841068247010265348713 2295630801185257699011535)
          ·
            refine ⟨3443446201777886548517303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295630801185257699011535 3443446201777886548517303)
            ·
              refine ⟨5165169302666829822775955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443446201777886548517303 5165169302666829822775955)
              ·
                refine ⟨7747753954000244734163933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165169302666829822775955 7747753954000244734163933)
                ·
                  refine ⟨2905407732750091775311475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7747753954000244734163933 2905407732750091775311475)
                  ·
                    refine ⟨4358111599125137662967213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905407732750091775311475 4358111599125137662967213)
                    ·
                      refine ⟨1634291849671926623612705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358111599125137662967213 1634291849671926623612705)
                      ·
                        rfl

theorem cell23_3182772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3182772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182772 prefixEnd_3182772 := by exact prefixLift 3182772
  have htrace : WordTrace (prefixWord ++ tailWord_3182772) baseStart_3182772 baseEnd_3182772 := by
    simpa [prefixWord, tailWord_3182772, baseEnd_3182772] using wordTrace_append hprefix tailTrace_3182772
  have hstable : (prefixWord ++ tailWord_3182772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182772).length < 2 ^ (prefixWord ++ tailWord_3182772).sum := by decide
  have hdescent : baseEnd_3182772 < baseStart_3182772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182777 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3182777 : Nat := 118140960795 + 3182777 * 2 ^ 59
def prefixEnd_3182777 : Nat := 4983230072969 + 3 ^ 40 * 3182777 * 2
def baseEnd_3182777 : Nat := 1634294417075199104050181

theorem tailTrace_3182777 : CollatzResearch.WordTrace tailWord_3182777 prefixEnd_3182777 1634294417075199104050181 := by
  unfold tailWord_3182777
  simp only [CollatzResearch.WordTrace]
  refine ⟨116085413990349978880490585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77390275993566652586993723 116085413990349978880490585)
  ·
    refine ⟨87064060492762484160367939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116085413990349978880490585 87064060492762484160367939)
    ·
      refine ⟨130596090739143726240551909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87064060492762484160367939 130596090739143726240551909)
      ·
        refine ⟨24486767013589448670103483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130596090739143726240551909 24486767013589448670103483)
        ·
          refine ⟨36730150520384173005155225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24486767013589448670103483 36730150520384173005155225)
          ·
            refine ⟨27547612890288129753866419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36730150520384173005155225 27547612890288129753866419)
            ·
              refine ⟨41321419335432194630799629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27547612890288129753866419 41321419335432194630799629)
              ·
                refine ⟨15495532250787072986549861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41321419335432194630799629 15495532250787072986549861)
                ·
                  refine ⟨2905412297022576184978099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15495532250787072986549861 2905412297022576184978099)
                  ·
                    refine ⟨4358118445533864277467149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905412297022576184978099 4358118445533864277467149)
                    ·
                      refine ⟨1634294417075199104050181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358118445533864277467149 1634294417075199104050181)
                      ·
                        rfl

theorem cell23_3182777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3182777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182777 prefixEnd_3182777 := by exact prefixLift 3182777
  have htrace : WordTrace (prefixWord ++ tailWord_3182777) baseStart_3182777 baseEnd_3182777 := by
    simpa [prefixWord, tailWord_3182777, baseEnd_3182777] using wordTrace_append hprefix tailTrace_3182777
  have hstable : (prefixWord ++ tailWord_3182777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182777).length < 2 ^ (prefixWord ++ tailWord_3182777).sum := by decide
  have hdescent : baseEnd_3182777 < baseStart_3182777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182794 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3182794 : Nat := 118140960795 + 3182794 * 2 ^ 59
def prefixEnd_3182794 : Nat := 4983230072969 + 3 ^ 40 * 3182794 * 2
def baseEnd_3182794 : Nat := 1634303146246325537537603

theorem tailTrace_3182794 : CollatzResearch.WordTrace tailWord_3182794 prefixEnd_3182794 1634303146246325537537603 := by
  unfold tailWord_3182794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021508507822097695964859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77390689354192260522572957 29021508507822097695964859)
  ·
    refine ⟨43532262761733146543947289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29021508507822097695964859 43532262761733146543947289)
    ·
      refine ⟨32649197071299859907960467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43532262761733146543947289 32649197071299859907960467)
      ·
        refine ⟨48973795606949789861940701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32649197071299859907960467 48973795606949789861940701)
        ·
          refine ⟨18365173352606171198227763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48973795606949789861940701 18365173352606171198227763)
          ·
            refine ⟨27547760028909256797341645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18365173352606171198227763 27547760028909256797341645)
            ·
              refine ⟨10330410010840971299003117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27547760028909256797341645 10330410010840971299003117)
              ·
                refine ⟨3873903754065364237126169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10330410010840971299003117 3873903754065364237126169)
                ·
                  refine ⟨2905427815549023177844627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873903754065364237126169 2905427815549023177844627)
                  ·
                    refine ⟨4358141723323534766766941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905427815549023177844627 4358141723323534766766941)
                    ·
                      refine ⟨1634303146246325537537603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358141723323534766766941 1634303146246325537537603)
                      ·
                        rfl

theorem cell23_3182794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3182794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182794 prefixEnd_3182794 := by exact prefixLift 3182794
  have htrace : WordTrace (prefixWord ++ tailWord_3182794) baseStart_3182794 baseEnd_3182794 := by
    simpa [prefixWord, tailWord_3182794, baseEnd_3182794] using wordTrace_append hprefix tailTrace_3182794
  have hstable : (prefixWord ++ tailWord_3182794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182794).length < 2 ^ (prefixWord ++ tailWord_3182794).sum := by decide
  have hdescent : baseEnd_3182794 < baseStart_3182794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182830 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3182830 : Nat := 118140960795 + 3182830 * 2 ^ 59
def prefixEnd_3182830 : Nat := 4983230072969 + 3 ^ 40 * 3182830 * 2
def baseEnd_3182830 : Nat := 1634321631549887396687437

theorem tailTrace_3182830 : CollatzResearch.WordTrace tailWord_3182830 prefixEnd_3182830 1634321631549887396687437 := by
  unfold tailWord_3182830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14510918382394746116521243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77391564706105312621446629 14510918382394746116521243)
  ·
    refine ⟨21766377573592119174781865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14510918382394746116521243 21766377573592119174781865)
    ·
      refine ⟨16324783180194089381086399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21766377573592119174781865 16324783180194089381086399)
      ·
        refine ⟨24487174770291134071629599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16324783180194089381086399 24487174770291134071629599)
        ·
          refine ⟨36730762155436701107444399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24487174770291134071629599 36730762155436701107444399)
          ·
            refine ⟨55096143233155051661166599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36730762155436701107444399 55096143233155051661166599)
            ·
              refine ⟨82644214849732577491749899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55096143233155051661166599 82644214849732577491749899)
              ·
                refine ⟨123966322274598866237624849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82644214849732577491749899 123966322274598866237624849)
                ·
                  refine ⟨92974741705949149678218637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123966322274598866237624849 92974741705949149678218637)
                  ·
                    refine ⟨34865528139730931129331989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92974741705949149678218637 34865528139730931129331989)
                    ·
                      refine ⟨1634321631549887396687437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34865528139730931129331989 1634321631549887396687437)
                      ·
                        rfl

theorem cell23_3182830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3182830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182830 prefixEnd_3182830 := by exact prefixLift 3182830
  have htrace : WordTrace (prefixWord ++ tailWord_3182830) baseStart_3182830 baseEnd_3182830 := by
    simpa [prefixWord, tailWord_3182830, baseEnd_3182830] using wordTrace_append hprefix tailTrace_3182830
  have hstable : (prefixWord ++ tailWord_3182830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182830).length < 2 ^ (prefixWord ++ tailWord_3182830).sum := by decide
  have hdescent : baseEnd_3182830 < baseStart_3182830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182885 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 2, 2, 2]
def baseStart_3182885 : Nat := 118140960795 + 3182885 * 2 ^ 59
def prefixEnd_3182885 : Nat := 4983230072969 + 3 ^ 40 * 3182885 * 2
def baseEnd_3182885 : Nat := 1634349872985884681499685

theorem tailTrace_3182885 : CollatzResearch.WordTrace tailWord_3182885 prefixEnd_3182885 1634349872985884681499685 := by
  unfold tailWord_3182885
  simp only [CollatzResearch.WordTrace]
  refine ⟨116089353073958713325422109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77392902049305808883614739 116089353073958713325422109)
  ·
    refine ⟨43533507402734517497033291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116089353073958713325422109 43533507402734517497033291)
    ·
      refine ⟨65300261104101776245549937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43533507402734517497033291 65300261104101776245549937)
      ·
        refine ⟨48975195828076332184162453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65300261104101776245549937 48975195828076332184162453)
        ·
          refine ⟨2295712304441078071132615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48975195828076332184162453 2295712304441078071132615)
          ·
            refine ⟨3443568456661617106698923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295712304441078071132615 3443568456661617106698923)
            ·
              refine ⟨5165352684992425660048385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443568456661617106698923 5165352684992425660048385)
              ·
                refine ⟨3874014513744319245036289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5165352684992425660048385 3874014513744319245036289)
                ·
                  refine ⟨2905510885308239433777217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3874014513744319245036289 2905510885308239433777217)
                  ·
                    refine ⟨2179133163981179575332913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905510885308239433777217 2179133163981179575332913)
                    ·
                      refine ⟨1634349872985884681499685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179133163981179575332913 1634349872985884681499685)
                      ·
                        rfl

theorem cell23_3182885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_3182885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182885 prefixEnd_3182885 := by exact prefixLift 3182885
  have htrace : WordTrace (prefixWord ++ tailWord_3182885) baseStart_3182885 baseEnd_3182885 := by
    simpa [prefixWord, tailWord_3182885, baseEnd_3182885] using wordTrace_append hprefix tailTrace_3182885
  have hstable : (prefixWord ++ tailWord_3182885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182885).length < 2 ^ (prefixWord ++ tailWord_3182885).sum := by decide
  have hdescent : baseEnd_3182885 < baseStart_3182885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182942 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3182942 : Nat := 118140960795 + 3182942 * 2 ^ 59
def prefixEnd_3182942 : Nat := 4983230072969 + 3 ^ 40 * 3182942 * 2
def baseEnd_3182942 : Nat := 181597682375910106498547

theorem tailTrace_3182942 : CollatzResearch.WordTrace tailWord_3182942 prefixEnd_3182942 181597682375910106498547 := by
  unfold tailWord_3182942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511429004344026507530885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77394288023168141373498053 14511429004344026507530885)
  ·
    refine ⟨2720892938314504970162041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14511429004344026507530885 2720892938314504970162041)
    ·
      refine ⟨2040669703735878727621531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2720892938314504970162041 2040669703735878727621531)
      ·
        refine ⟨3061004555603818091432297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040669703735878727621531 3061004555603818091432297)
        ·
          refine ⟨2295753416702863568574223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061004555603818091432297 2295753416702863568574223)
          ·
            refine ⟨3443630125054295352861335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295753416702863568574223 3443630125054295352861335)
            ·
              refine ⟨5165445187581443029292003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443630125054295352861335 5165445187581443029292003)
              ·
                refine ⟨7748167781372164543938005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165445187581443029292003 7748167781372164543938005)
                ·
                  refine ⟨181597682375910106498547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7748167781372164543938005 181597682375910106498547)
                  ·
                    rfl

theorem cell23_3182942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3182942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182942 prefixEnd_3182942 := by exact prefixLift 3182942
  have htrace : WordTrace (prefixWord ++ tailWord_3182942) baseStart_3182942 baseEnd_3182942 := by
    simpa [prefixWord, tailWord_3182942, baseEnd_3182942] using wordTrace_append hprefix tailTrace_3182942
  have hstable : (prefixWord ++ tailWord_3182942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182942).length < 2 ^ (prefixWord ++ tailWord_3182942).sum := by decide
  have hdescent : baseEnd_3182942 < baseStart_3182942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182947 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 6]
def baseStart_3182947 : Nat := 118140960795 + 3182947 * 2 ^ 59
def prefixEnd_3182947 : Nat := 4983230072969 + 3 ^ 40 * 3182947 * 2
def baseEnd_3182947 : Nat := 181597967642940382102711

theorem tailTrace_3182947 : CollatzResearch.WordTrace tailWord_3182947 prefixEnd_3182947 181597967642940382102711 := by
  unfold tailWord_3182947
  simp only [CollatzResearch.WordTrace]
  refine ⟨116091614399734097914179095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77394409599822731942786063 116091614399734097914179095)
  ·
    refine ⟨174137421599601146871268643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116091614399734097914179095 174137421599601146871268643)
    ·
      refine ⟨261206132399401720306902965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174137421599601146871268643 261206132399401720306902965)
      ·
        refine ⟨24488074912443911278772153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261206132399401720306902965 24488074912443911278772153)
        ·
          refine ⟨18366056184332933459079115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24488074912443911278772153 18366056184332933459079115)
          ·
            refine ⟨27549084276499400188618673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366056184332933459079115 27549084276499400188618673)
            ·
              refine ⟨20661813207374550141464005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27549084276499400188618673 20661813207374550141464005)
              ·
                refine ⟨3874089976382728151524501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20661813207374550141464005 3874089976382728151524501)
                ·
                  refine ⟨181597967642940382102711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3874089976382728151524501 181597967642940382102711)
                  ·
                    rfl

theorem cell23_3182947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 6].length) (baseStart_3182947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182947 prefixEnd_3182947 := by exact prefixLift 3182947
  have htrace : WordTrace (prefixWord ++ tailWord_3182947) baseStart_3182947 baseEnd_3182947 := by
    simpa [prefixWord, tailWord_3182947, baseEnd_3182947] using wordTrace_append hprefix tailTrace_3182947
  have hstable : (prefixWord ++ tailWord_3182947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182947).length < 2 ^ (prefixWord ++ tailWord_3182947).sum := by decide
  have hdescent : baseEnd_3182947 < baseStart_3182947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3182951 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3182951 : Nat := 118140960795 + 3182951 * 2 ^ 59
def prefixEnd_3182951 : Nat := 4983230072969 + 3 ^ 40 * 3182951 * 2
def baseEnd_3182951 : Nat := 544794587569693807758127

theorem tailTrace_3182951 : CollatzResearch.WordTrace tailWord_3182951 prefixEnd_3182951 544794587569693807758127 := by
  unfold tailWord_3182951
  simp only [CollatzResearch.WordTrace]
  refine ⟨116091760291719606597324707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77394506861146404398216471 116091760291719606597324707)
  ·
    refine ⟨174137640437579409895987061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116091760291719606597324707 174137640437579409895987061)
    ·
      refine ⟨16325403791023069677748787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174137640437579409895987061 16325403791023069677748787)
      ·
        refine ⟨24488105686534604516623181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16325403791023069677748787 24488105686534604516623181)
        ·
          refine ⟨9183039632450476693733693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24488105686534604516623181 9183039632450476693733693)
          ·
            refine ⟨3443639862168928760150135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9183039632450476693733693 3443639862168928760150135)
            ·
              refine ⟨5165459793253393140225203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443639862168928760150135 5165459793253393140225203)
              ·
                refine ⟨7748189689880089710337805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5165459793253393140225203 7748189689880089710337805)
                ·
                  refine ⟨2905571133705033641376677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7748189689880089710337805 2905571133705033641376677)
                  ·
                    refine ⟨544794587569693807758127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905571133705033641376677 544794587569693807758127)
                    ·
                      rfl

theorem cell23_3182951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3182951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3182951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3182951 prefixEnd_3182951 := by exact prefixLift 3182951
  have htrace : WordTrace (prefixWord ++ tailWord_3182951) baseStart_3182951 baseEnd_3182951 := by
    simpa [prefixWord, tailWord_3182951, baseEnd_3182951] using wordTrace_append hprefix tailTrace_3182951
  have hstable : (prefixWord ++ tailWord_3182951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3182951).length < 2 ^ (prefixWord ++ tailWord_3182951).sum := by decide
  have hdescent : baseEnd_3182951 < baseStart_3182951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3182951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183007 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 6]
def baseStart_3183007 : Nat := 118140960795 + 3183007 * 2 ^ 59
def prefixEnd_3183007 : Nat := 4983230072969 + 3 ^ 40 * 3183007 * 2
def baseEnd_3183007 : Nat := 544804172541911068058041

theorem tailTrace_3183007 : CollatzResearch.WordTrace tailWord_3183007 prefixEnd_3183007 544804172541911068058041 := by
  unfold tailWord_3183007
  simp only [CollatzResearch.WordTrace]
  refine ⟨116093802779516728161363275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77395868519677818774242183 116093802779516728161363275)
  ·
    refine ⟨174140704169275092242044913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116093802779516728161363275 174140704169275092242044913)
    ·
      refine ⟨130605528126956319181533685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174140704169275092242044913 130605528126956319181533685)
      ·
        refine ⟨12244268261902154923268783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130605528126956319181533685 12244268261902154923268783)
        ·
          refine ⟨18366402392853232384903175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244268261902154923268783 18366402392853232384903175)
          ·
            refine ⟨27549603589279848577354763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366402392853232384903175 27549603589279848577354763)
            ·
              refine ⟨41324405383919772866032145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27549603589279848577354763 41324405383919772866032145)
              ·
                refine ⟨30993304037939829649524109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41324405383919772866032145 30993304037939829649524109)
                ·
                  refine ⟨11622489014227436118571541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30993304037939829649524109 11622489014227436118571541)
                  ·
                    refine ⟨544804172541911068058041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11622489014227436118571541 544804172541911068058041)
                    ·
                      rfl

theorem cell23_3183007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_3183007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183007 prefixEnd_3183007 := by exact prefixLift 3183007
  have htrace : WordTrace (prefixWord ++ tailWord_3183007) baseStart_3183007 baseEnd_3183007 := by
    simpa [prefixWord, tailWord_3183007, baseEnd_3183007] using wordTrace_append hprefix tailTrace_3183007
  have hstable : (prefixWord ++ tailWord_3183007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183007).length < 2 ^ (prefixWord ++ tailWord_3183007).sum := by decide
  have hdescent : baseEnd_3183007 < baseStart_3183007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183008 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 1, 1, 3]
def baseStart_3183008 : Nat := 118140960795 + 3183008 * 2 ^ 59
def prefixEnd_3183008 : Nat := 4983230072969 + 3 ^ 40 * 3183008 * 2
def baseEnd_3183008 : Nat := 1634413031106387700261619

theorem tailTrace_3183008 : CollatzResearch.WordTrace tailWord_3183008 prefixEnd_3183008 1634413031106387700261619 := by
  unfold tailWord_3183008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58046919626256552666074839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77395892835008736888099785 58046919626256552666074839)
  ·
    refine ⟨87070379439384828999112259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58046919626256552666074839 87070379439384828999112259)
    ·
      refine ⟨130605569159077243498668389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87070379439384828999112259 130605569159077243498668389)
      ·
        refine ⟨24488544217326983156000323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130605569159077243498668389 24488544217326983156000323)
        ·
          refine ⟨36732816325990474734000485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24488544217326983156000323 36732816325990474734000485)
          ·
            refine ⟨6887403061123214012625091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36732816325990474734000485 6887403061123214012625091)
            ·
              refine ⟨10331104591684821018937637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887403061123214012625091 10331104591684821018937637)
              ·
                refine ⟨1937082110940903941050807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10331104591684821018937637 1937082110940903941050807)
                ·
                  refine ⟨2905623166411355911576211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937082110940903941050807 2905623166411355911576211)
                  ·
                    refine ⟨4358434749617033867364317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905623166411355911576211 4358434749617033867364317)
                    ·
                      refine ⟨1634413031106387700261619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358434749617033867364317 1634413031106387700261619)
                      ·
                        rfl

theorem cell23_3183008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_3183008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183008 prefixEnd_3183008 := by exact prefixLift 3183008
  have htrace : WordTrace (prefixWord ++ tailWord_3183008) baseStart_3183008 baseEnd_3183008 := by
    simpa [prefixWord, tailWord_3183008, baseEnd_3183008] using wordTrace_append hprefix tailTrace_3183008
  have hstable : (prefixWord ++ tailWord_3183008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183008).length < 2 ^ (prefixWord ++ tailWord_3183008).sum := by decide
  have hdescent : baseEnd_3183008 < baseStart_3183008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_3183017 : Nat := 118140960795 + 3183017 * 2 ^ 59
def prefixEnd_3183017 : Nat := 4983230072969 + 3 ^ 40 * 3183017 * 2
def baseEnd_3183017 : Nat := 1634417652432278165049077

theorem tailTrace_3183017 : CollatzResearch.WordTrace tailWord_3183017 prefixEnd_3183017 1634417652432278165049077 := by
  unfold tailWord_3183017
  simp only [CollatzResearch.WordTrace]
  refine ⟨116094167509480499869227305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77396111672986999912818203 116094167509480499869227305)
  ·
    refine ⟨87070625632110374901920479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116094167509480499869227305 87070625632110374901920479)
    ·
      refine ⟨130605938448165562352880719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87070625632110374901920479 130605938448165562352880719)
      ·
        refine ⟨195908907672248343529321079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130605938448165562352880719 195908907672248343529321079)
        ·
          refine ⟨293863361508372515293981619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195908907672248343529321079 293863361508372515293981619)
          ·
            refine ⟨440795042262558772940972429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293863361508372515293981619 440795042262558772940972429)
            ·
              refine ⟨165298140848459539852864661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440795042262558772940972429 165298140848459539852864661)
              ·
                refine ⟨7748350352271540930603031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165298140848459539852864661 7748350352271540930603031)
                ·
                  refine ⟨11622525528407311395904547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7748350352271540930603031 11622525528407311395904547)
                  ·
                    refine ⟨17433788292610967093856821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11622525528407311395904547 17433788292610967093856821)
                    ·
                      refine ⟨1634417652432278165049077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17433788292610967093856821 1634417652432278165049077)
                      ·
                        rfl

theorem cell23_3183017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_3183017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183017 prefixEnd_3183017 := by exact prefixLift 3183017
  have htrace : WordTrace (prefixWord ++ tailWord_3183017) baseStart_3183017 baseEnd_3183017 := by
    simpa [prefixWord, tailWord_3183017, baseEnd_3183017] using wordTrace_append hprefix tailTrace_3183017
  have hstable : (prefixWord ++ tailWord_3183017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183017).length < 2 ^ (prefixWord ++ tailWord_3183017).sum := by decide
  have hdescent : baseEnd_3183017 < baseStart_3183017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183031 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 5, 2, 2]
def baseStart_3183031 : Nat := 118140960795 + 3183031 * 2 ^ 59
def prefixEnd_3183031 : Nat := 4983230072969 + 3 ^ 40 * 3183031 * 2
def baseEnd_3183031 : Nat := 1634424841161441110274013

theorem tailTrace_3183031 : CollatzResearch.WordTrace tailWord_3183031 prefixEnd_3183031 1634424841161441110274013 := by
  unfold tailWord_3183031
  simp only [CollatzResearch.WordTrace]
  refine ⟨116094678131429780260236947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77396452087619853506824631 116094678131429780260236947)
  ·
    refine ⟨174142017197144670390355421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116094678131429780260236947 174142017197144670390355421)
    ·
      refine ⟨65303256448929251396383283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174142017197144670390355421 65303256448929251396383283)
      ·
        refine ⟨97954884673393877094574925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65303256448929251396383283 97954884673393877094574925)
        ·
          refine ⟨36733081752522703910465597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97954884673393877094574925 36733081752522703910465597)
          ·
            refine ⟨13774905657196013966424599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36733081752522703910465597 13774905657196013966424599)
            ·
              refine ⟨20662358485794020949636899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13774905657196013966424599 20662358485794020949636899)
              ·
                refine ⟨30993537728691031424455349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20662358485794020949636899 30993537728691031424455349)
                ·
                  refine ⟨2905644162064784196042689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30993537728691031424455349 2905644162064784196042689)
                  ·
                    refine ⟨2179233121548588147032017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905644162064784196042689 2179233121548588147032017)
                    ·
                      refine ⟨1634424841161441110274013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179233121548588147032017 1634424841161441110274013)
                      ·
                        rfl

theorem cell23_3183031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 2, 2].length) (baseStart_3183031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183031 prefixEnd_3183031 := by exact prefixLift 3183031
  have htrace : WordTrace (prefixWord ++ tailWord_3183031) baseStart_3183031 baseEnd_3183031 := by
    simpa [prefixWord, tailWord_3183031, baseEnd_3183031] using wordTrace_append hprefix tailTrace_3183031
  have hstable : (prefixWord ++ tailWord_3183031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183031).length < 2 ^ (prefixWord ++ tailWord_3183031).sum := by decide
  have hdescent : baseEnd_3183031 < baseStart_3183031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183048 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_3183048 : Nat := 118140960795 + 3183048 * 2 ^ 59
def prefixEnd_3183048 : Nat := 4983230072969 + 3 ^ 40 * 3183048 * 2
def baseEnd_3183048 : Nat := 1634433570332567543761435

theorem tailTrace_3183048 : CollatzResearch.WordTrace tailWord_3183048 prefixEnd_3183048 1634433570332567543761435 := by
  unfold tailWord_3183048
  simp only [CollatzResearch.WordTrace]
  refine ⟨58047649086184096081802899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77396865448245461442403865 58047649086184096081802899)
  ·
    refine ⟨87071473629276144122704349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58047649086184096081802899 87071473629276144122704349)
    ·
      refine ⟨32651802610978554046014131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87071473629276144122704349 32651802610978554046014131)
      ·
        refine ⟨48977703916467831069021197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32651802610978554046014131 48977703916467831069021197)
        ·
          refine ⟨18366638968675436650882949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48977703916467831069021197 18366638968675436650882949)
          ·
            refine ⟨3443744806626644372040553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18366638968675436650882949 3443744806626644372040553)
            ·
              refine ⟨2582808604969983279030415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443744806626644372040553 2582808604969983279030415)
              ·
                refine ⟨3874212907454974918545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582808604969983279030415 3874212907454974918545623)
                ·
                  refine ⟨5811319361182462377818435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3874212907454974918545623 5811319361182462377818435)
                  ·
                    refine ⟨8716979041773693566727653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5811319361182462377818435 8716979041773693566727653)
                    ·
                      refine ⟨1634433570332567543761435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8716979041773693566727653 1634433570332567543761435)
                      ·
                        rfl

theorem cell23_3183048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_3183048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183048 prefixEnd_3183048 := by exact prefixLift 3183048
  have htrace : WordTrace (prefixWord ++ tailWord_3183048) baseStart_3183048 baseEnd_3183048 := by
    simpa [prefixWord, tailWord_3183048, baseEnd_3183048] using wordTrace_append hprefix tailTrace_3183048
  have hstable : (prefixWord ++ tailWord_3183048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183048).length < 2 ^ (prefixWord ++ tailWord_3183048).sum := by decide
  have hdescent : baseEnd_3183048 < baseStart_3183048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183058 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3183058 : Nat := 118140960795 + 3183058 * 2 ^ 59
def prefixEnd_3183058 : Nat := 4983230072969 + 3 ^ 40 * 3183058 * 2
def baseEnd_3183058 : Nat := 544812901713037501545463

theorem tailTrace_3183058 : CollatzResearch.WordTrace tailWord_3183058 prefixEnd_3183058 544812901713037501545463 := by
  unfold tailWord_3183058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023915725582990967867457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77397108601554642580979885 29023915725582990967867457)
  ·
    refine ⟨21767936794187243225900593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29023915725582990967867457 21767936794187243225900593)
    ·
      refine ⟨16325952595640432419425445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21767936794187243225900593 16325952595640432419425445)
      ·
        refine ⟨3061116111682581078642271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16325952595640432419425445 3061116111682581078642271)
        ·
          refine ⟨4591674167523871617963407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061116111682581078642271 4591674167523871617963407)
          ·
            refine ⟨6887511251285807426945111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591674167523871617963407 6887511251285807426945111)
            ·
              refine ⟨10331266876928711140417667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887511251285807426945111 10331266876928711140417667)
              ·
                refine ⟨15496900315393066710626501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10331266876928711140417667 15496900315393066710626501)
                ·
                  refine ⟨2905668809136200008242469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15496900315393066710626501 2905668809136200008242469)
                  ·
                    refine ⟨544812901713037501545463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2905668809136200008242469 544812901713037501545463)
                    ·
                      rfl

theorem cell23_3183058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3183058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183058 prefixEnd_3183058 := by exact prefixLift 3183058
  have htrace : WordTrace (prefixWord ++ tailWord_3183058) baseStart_3183058 baseEnd_3183058 := by
    simpa [prefixWord, tailWord_3183058, baseEnd_3183058] using wordTrace_append hprefix tailTrace_3183058
  have hstable : (prefixWord ++ tailWord_3183058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183058).length < 2 ^ (prefixWord ++ tailWord_3183058).sum := by decide
  have hdescent : baseEnd_3183058 < baseStart_3183058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183094 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3183094 : Nat := 118140960795 + 3183094 * 2 ^ 59
def prefixEnd_3183094 : Nat := 4983230072969 + 3 ^ 40 * 3183094 * 2
def baseEnd_3183094 : Nat := 1634457190442674363786223

theorem tailTrace_3183094 : CollatzResearch.WordTrace tailWord_3183094 prefixEnd_3183094 1634457190442674363786223 := by
  unfold tailWord_3183094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256060995637596376236271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77397983953467694679853557 7256060995637596376236271)
  ·
    refine ⟨10884091493456394564354407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7256060995637596376236271 10884091493456394564354407)
    ·
      refine ⟨16326137240184591846531611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10884091493456394564354407 16326137240184591846531611)
      ·
        refine ⟨24489205860276887769797417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326137240184591846531611 24489205860276887769797417)
        ·
          refine ⟨18366904395207665827348063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24489205860276887769797417 18366904395207665827348063)
          ·
            refine ⟨27550356592811498741022095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366904395207665827348063 27550356592811498741022095)
            ·
              refine ⟨41325534889217248111533143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27550356592811498741022095 41325534889217248111533143)
              ·
                refine ⟨61988302333825872167299715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41325534889217248111533143 61988302333825872167299715)
                ·
                  refine ⟨92982453500738808250949573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61988302333825872167299715 92982453500738808250949573)
                  ·
                    refine ⟨17434210031388526547053045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92982453500738808250949573 17434210031388526547053045)
                    ·
                      refine ⟨1634457190442674363786223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17434210031388526547053045 1634457190442674363786223)
                      ·
                        rfl

theorem cell23_3183094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3183094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183094 prefixEnd_3183094 := by exact prefixLift 3183094
  have htrace : WordTrace (prefixWord ++ tailWord_3183094) baseStart_3183094 baseEnd_3183094 := by
    simpa [prefixWord, tailWord_3183094, baseEnd_3183094] using wordTrace_append hprefix tailTrace_3183094
  have hstable : (prefixWord ++ tailWord_3183094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183094).length < 2 ^ (prefixWord ++ tailWord_3183094).sum := by decide
  have hdescent : baseEnd_3183094 < baseStart_3183094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183097 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_3183097 : Nat := 118140960795 + 3183097 * 2 ^ 59
def prefixEnd_3183097 : Nat := 4983230072969 + 3 ^ 40 * 3183097 * 2
def baseEnd_3183097 : Nat := 544819576961545950682903

theorem tailTrace_3183097 : CollatzResearch.WordTrace tailWord_3183097 prefixEnd_3183097 544819576961545950682903 := by
  unfold tailWord_3183097
  simp only [CollatzResearch.WordTrace]
  refine ⟨116097085349190673532139545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77398056899460449021426363 116097085349190673532139545)
  ·
    refine ⟨87072814011893005149104659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116097085349190673532139545 87072814011893005149104659)
    ·
      refine ⟨130609221017839507723656989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87072814011893005149104659 130609221017839507723656989)
      ·
        refine ⟨48978457881689815396371371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130609221017839507723656989 48978457881689815396371371)
        ·
          refine ⟨73467686822534723094557057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48978457881689815396371371 73467686822534723094557057)
          ·
            refine ⟨55100765116901042320917793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73467686822534723094557057 55100765116901042320917793)
            ·
              refine ⟨41325573837675781740688345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55100765116901042320917793 41325573837675781740688345)
              ·
                refine ⟨30994180378256836305516259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41325573837675781740688345 30994180378256836305516259)
                ·
                  refine ⟨46491270567385254458274389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30994180378256836305516259 46491270567385254458274389)
                  ·
                    refine ⟨544819576961545950682903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46491270567385254458274389 544819576961545950682903)
                    ·
                      rfl

theorem cell23_3183097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_3183097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183097 prefixEnd_3183097 := by exact prefixLift 3183097
  have htrace : WordTrace (prefixWord ++ tailWord_3183097) baseStart_3183097 baseEnd_3183097 := by
    simpa [prefixWord, tailWord_3183097, baseEnd_3183097] using wordTrace_append hprefix tailTrace_3183097
  have hstable : (prefixWord ++ tailWord_3183097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183097).length < 2 ^ (prefixWord ++ tailWord_3183097).sum := by decide
  have hdescent : baseEnd_3183097 < baseStart_3183097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183147 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_3183147 : Nat := 118140960795 + 3183147 * 2 ^ 59
def prefixEnd_3183147 : Nat := 4983230072969 + 3 ^ 40 * 3183147 * 2
def baseEnd_3183147 : Nat := 1634484404917362656423479

theorem tailTrace_3183147 : CollatzResearch.WordTrace tailWord_3183147 prefixEnd_3183147 1634484404917362656423479 := by
  unfold tailWord_3183147
  simp only [CollatzResearch.WordTrace]
  refine ⟨116098908999009532071459695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77399272666006354714306463 116098908999009532071459695)
  ·
    refine ⟨174148363498514298107189543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116098908999009532071459695 174148363498514298107189543)
    ·
      refine ⟨261222545247771447160784315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174148363498514298107189543 261222545247771447160784315)
      ·
        refine ⟨391833817871657170741176473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261222545247771447160784315 391833817871657170741176473)
        ·
          refine ⟨293875363403742878055882355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391833817871657170741176473 293875363403742878055882355)
          ·
            refine ⟨440813045105614317083823533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293875363403742878055882355 440813045105614317083823533)
            ·
              refine ⟨165304891914605368906433825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440813045105614317083823533 165304891914605368906433825)
              ·
                refine ⟨123978668935954026679825369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165304891914605368906433825 123978668935954026679825369)
                ·
                  refine ⟨92984001701965520009869027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123978668935954026679825369 92984001701965520009869027)
                  ·
                    refine ⟨139476002552948280014803541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92984001701965520009869027 139476002552948280014803541)
                    ·
                      refine ⟨1634484404917362656423479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139476002552948280014803541 1634484404917362656423479)
                      ·
                        rfl

theorem cell23_3183147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_3183147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183147 prefixEnd_3183147 := by exact prefixLift 3183147
  have htrace : WordTrace (prefixWord ++ tailWord_3183147) baseStart_3183147 baseEnd_3183147 := by
    simpa [prefixWord, tailWord_3183147, baseEnd_3183147] using wordTrace_append hprefix tailTrace_3183147
  have hstable : (prefixWord ++ tailWord_3183147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183147).length < 2 ^ (prefixWord ++ tailWord_3183147).sum := by decide
  have hdescent : baseEnd_3183147 < baseStart_3183147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183161 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 5]
def baseStart_3183161 : Nat := 118140960795 + 3183161 * 2 ^ 59
def prefixEnd_3183161 : Nat := 4983230072969 + 3 ^ 40 * 3183161 * 2
def baseEnd_3183161 : Nat := 181610177071836177960935

theorem tailTrace_3183161 : CollatzResearch.WordTrace tailWord_3183161 prefixEnd_3183161 181610177071836177960935 := by
  unfold tailWord_3183161
  simp only [CollatzResearch.WordTrace]
  refine ⟨116099419620958812462469337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77399613080639208308312891 116099419620958812462469337)
  ·
    refine ⟨87074564715719109346852003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116099419620958812462469337 87074564715719109346852003)
    ·
      refine ⟨130611847073578664020278005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87074564715719109346852003 130611847073578664020278005)
      ·
        refine ⟨12244860663147999751901063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130611847073578664020278005 12244860663147999751901063)
        ·
          refine ⟨18367290994721999627851595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244860663147999751901063 18367290994721999627851595)
          ·
            refine ⟨27550936492082999441777393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18367290994721999627851595 27550936492082999441777393)
            ·
              refine ⟨20663202369062249581333045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27550936492082999441777393 20663202369062249581333045)
              ·
                refine ⟨1937175222099585898249973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20663202369062249581333045 1937175222099585898249973)
                ·
                  refine ⟨181610177071836177960935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937175222099585898249973 181610177071836177960935)
                  ·
                    rfl

theorem cell23_3183161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 5].length) (baseStart_3183161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183161 prefixEnd_3183161 := by exact prefixLift 3183161
  have htrace : WordTrace (prefixWord ++ tailWord_3183161) baseStart_3183161 baseEnd_3183161 := by
    simpa [prefixWord, tailWord_3183161, baseEnd_3183161] using wordTrace_append hprefix tailTrace_3183161
  have hstable : (prefixWord ++ tailWord_3183161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183161).length < 2 ^ (prefixWord ++ tailWord_3183161).sum := by decide
  have hdescent : baseEnd_3183161 < baseStart_3183161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183178 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_3183178 : Nat := 118140960795 + 3183178 * 2 ^ 59
def prefixEnd_3183178 : Nat := 4983230072969 + 3 ^ 40 * 3183178 * 2
def baseEnd_3183178 : Nat := 181611146979739115015093

theorem tailTrace_3183178 : CollatzResearch.WordTrace tailWord_3183178 prefixEnd_3183178 181611146979739115015093 := by
  unfold tailWord_3183178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025009915474306091459547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77400026441264816243892125 29025009915474306091459547)
  ·
    refine ⟨43537514873211459137189321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29025009915474306091459547 43537514873211459137189321)
    ·
      refine ⟨32653136154908594352891991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43537514873211459137189321 32653136154908594352891991)
      ·
        refine ⟨48979704232362891529337987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32653136154908594352891991 48979704232362891529337987)
        ·
          refine ⟨73469556348544337294006981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48979704232362891529337987 73469556348544337294006981)
          ·
            refine ⟨13775541815352063242626309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73469556348544337294006981 13775541815352063242626309)
            ·
              refine ⟨2582914090378511857992433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13775541815352063242626309 2582914090378511857992433)
              ·
                refine ⟨1937185567783883893494325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582914090378511857992433 1937185567783883893494325)
                ·
                  refine ⟨181611146979739115015093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937185567783883893494325 181611146979739115015093)
                  ·
                    rfl

theorem cell23_3183178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_3183178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183178 prefixEnd_3183178 := by exact prefixLift 3183178
  have htrace : WordTrace (prefixWord ++ tailWord_3183178) baseStart_3183178 baseEnd_3183178 := by
    simpa [prefixWord, tailWord_3183178, baseEnd_3183178] using wordTrace_append hprefix tailTrace_3183178
  have hstable : (prefixWord ++ tailWord_3183178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183178).length < 2 ^ (prefixWord ++ tailWord_3183178).sum := by decide
  have hdescent : baseEnd_3183178 < baseStart_3183178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183295 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 3]
def baseStart_3183295 : Nat := 118140960795 + 3183295 * 2 ^ 59
def prefixEnd_3183295 : Nat := 4983230072969 + 3 ^ 40 * 3183295 * 2
def baseEnd_3183295 : Nat := 1634560400054228077372799

theorem tailTrace_3183295 : CollatzResearch.WordTrace tailWord_3183295 prefixEnd_3183295 1634560400054228077372799 := by
  unfold tailWord_3183295
  simp only [CollatzResearch.WordTrace]
  refine ⟨116104307002473353347847339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77402871334982235565231559 116104307002473353347847339)
  ·
    refine ⟨174156460503710030021771009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116104307002473353347847339 174156460503710030021771009)
    ·
      refine ⟨130617345377782522516328257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174156460503710030021771009 130617345377782522516328257)
      ·
        refine ⟨97963009033336891887246193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130617345377782522516328257 97963009033336891887246193)
        ·
          refine ⟨73472256775002668915434645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97963009033336891887246193 73472256775002668915434645)
          ·
            refine ⟨3444012036328250105410999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73472256775002668915434645 3444012036328250105410999)
            ·
              refine ⟨5166018054492375158116499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444012036328250105410999 5166018054492375158116499)
              ·
                refine ⟨7749027081738562737174749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166018054492375158116499 7749027081738562737174749)
                ·
                  refine ⟨2905885155651961026440531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7749027081738562737174749 2905885155651961026440531)
                  ·
                    refine ⟨4358827733477941539660797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905885155651961026440531 4358827733477941539660797)
                    ·
                      refine ⟨1634560400054228077372799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358827733477941539660797 1634560400054228077372799)
                      ·
                        rfl

theorem cell23_3183295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_3183295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183295 prefixEnd_3183295 := by exact prefixLift 3183295
  have htrace : WordTrace (prefixWord ++ tailWord_3183295) baseStart_3183295 baseEnd_3183295 := by
    simpa [prefixWord, tailWord_3183295, baseEnd_3183295] using wordTrace_append hprefix tailTrace_3183295
  have hstable : (prefixWord ++ tailWord_3183295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183295).length < 2 ^ (prefixWord ++ tailWord_3183295).sum := by decide
  have hdescent : baseEnd_3183295 < baseStart_3183295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183302 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3183302 : Nat := 118140960795 + 3183302 * 2 ^ 59
def prefixEnd_3183302 : Nat := 4983230072969 + 3 ^ 40 * 3183302 * 2
def baseEnd_3183302 : Nat := 181618221602089949998363

theorem tailTrace_3183302 : CollatzResearch.WordTrace tailWord_3183302 prefixEnd_3183302 181618221602089949998363 := by
  unfold tailWord_3183302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628267572295249798229755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77403041542298662362234773 3628267572295249798229755)
  ·
    refine ⟨5442401358442874697344633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3628267572295249798229755 5442401358442874697344633)
    ·
      refine ⟨4081801018832156023008475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5442401358442874697344633 4081801018832156023008475)
      ·
        refine ⟨6122701528248234034512713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081801018832156023008475 6122701528248234034512713)
        ·
          refine ⟨4592026146186175525884535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122701528248234034512713 4592026146186175525884535)
          ·
            refine ⟨6888039219279263288826803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592026146186175525884535 6888039219279263288826803)
            ·
              refine ⟨10332058828918894933240205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888039219279263288826803 10332058828918894933240205)
              ·
                refine ⟨3874522060844585599965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10332058828918894933240205 3874522060844585599965077)
                ·
                  refine ⟨181618221602089949998363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3874522060844585599965077 181618221602089949998363)
                  ·
                    rfl

theorem cell23_3183302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3183302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183302 prefixEnd_3183302 := by exact prefixLift 3183302
  have htrace : WordTrace (prefixWord ++ tailWord_3183302) baseStart_3183302 baseEnd_3183302 := by
    simpa [prefixWord, tailWord_3183302, baseEnd_3183302] using wordTrace_append hprefix tailTrace_3183302
  have hstable : (prefixWord ++ tailWord_3183302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183302).length < 2 ^ (prefixWord ++ tailWord_3183302).sum := by decide
  have hdescent : baseEnd_3183302 < baseStart_3183302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183351 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_3183351 : Nat := 118140960795 + 3183351 * 2 ^ 59
def prefixEnd_3183351 : Nat := 4983230072969 + 3 ^ 40 * 3183351 * 2
def baseEnd_3183351 : Nat := 1634589154970879858272541

theorem tailTrace_3183351 : CollatzResearch.WordTrace tailWord_3183351 prefixEnd_3183351 1634589154970879858272541 := by
  unfold tailWord_3183351
  simp only [CollatzResearch.WordTrace]
  refine ⟨116106349490270474911885907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77404232993513649941257271 116106349490270474911885907)
  ·
    refine ⟨174159524235405712367828861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116106349490270474911885907 174159524235405712367828861)
    ·
      refine ⟨65309821588277142137935823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174159524235405712367828861 65309821588277142137935823)
      ·
        refine ⟨97964732382415713206903735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65309821588277142137935823 97964732382415713206903735)
        ·
          refine ⟨146947098573623569810355603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97964732382415713206903735 146947098573623569810355603)
          ·
            refine ⟨220420647860435354715533405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146947098573623569810355603 220420647860435354715533405)
            ·
              refine ⟨82657742947663258018325027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220420647860435354715533405 82657742947663258018325027)
              ·
                refine ⟨123986614421494887027487541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82657742947663258018325027 123986614421494887027487541)
                ·
                  refine ⟨11623745102015145658826957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123986614421494887027487541 11623745102015145658826957)
                  ·
                    refine ⟨4358904413255679622060109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11623745102015145658826957 4358904413255679622060109)
                    ·
                      refine ⟨1634589154970879858272541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358904413255679622060109 1634589154970879858272541)
                      ·
                        rfl

theorem cell23_3183351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_3183351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183351 prefixEnd_3183351 := by exact prefixLift 3183351
  have htrace : WordTrace (prefixWord ++ tailWord_3183351) baseStart_3183351 baseEnd_3183351 := by
    simpa [prefixWord, tailWord_3183351, baseEnd_3183351] using wordTrace_append hprefix tailTrace_3183351
  have hstable : (prefixWord ++ tailWord_3183351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183351).length < 2 ^ (prefixWord ++ tailWord_3183351).sum := by decide
  have hdescent : baseEnd_3183351 < baseStart_3183351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183352 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_3183352 : Nat := 118140960795 + 3183352 * 2 ^ 59
def prefixEnd_3183352 : Nat := 4983230072969 + 3 ^ 40 * 3183352 * 2
def baseEnd_3183352 : Nat := 1634589668451534354360037

theorem tailTrace_3183352 : CollatzResearch.WordTrace tailWord_3183352 prefixEnd_3183352 1634589668451534354360037 := by
  unfold tailWord_3183352
  simp only [CollatzResearch.WordTrace]
  refine ⟨58053192981633426041336155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77404257308844568055114873 58053192981633426041336155)
  ·
    refine ⟨87079789472450139062004233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58053192981633426041336155 87079789472450139062004233)
    ·
      refine ⟨65309842104337604296503175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87079789472450139062004233 65309842104337604296503175)
      ·
        refine ⟨97964763156506406444754763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65309842104337604296503175 97964763156506406444754763)
        ·
          refine ⟨146947144734759609667132145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97964763156506406444754763 146947144734759609667132145)
          ·
            refine ⟨110210358551069707250349109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146947144734759609667132145 110210358551069707250349109)
            ·
              refine ⟨10332221114162785054720229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110210358551069707250349109 10332221114162785054720229)
              ·
                refine ⟨1937291458905522197760043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10332221114162785054720229 1937291458905522197760043)
                ·
                  refine ⟨2905937188358283296640065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937291458905522197760043 2905937188358283296640065)
                  ·
                    refine ⟨2179452891268712472480049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905937188358283296640065 2179452891268712472480049)
                    ·
                      refine ⟨1634589668451534354360037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179452891268712472480049 1634589668451534354360037)
                      ·
                        rfl

theorem cell23_3183352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_3183352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183352 prefixEnd_3183352 := by exact prefixLift 3183352
  have htrace : WordTrace (prefixWord ++ tailWord_3183352) baseStart_3183352 baseEnd_3183352 := by
    simpa [prefixWord, tailWord_3183352, baseEnd_3183352] using wordTrace_append hprefix tailTrace_3183352
  have hstable : (prefixWord ++ tailWord_3183352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183352).length < 2 ^ (prefixWord ++ tailWord_3183352).sum := by decide
  have hdescent : baseEnd_3183352 < baseStart_3183352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183358 : List Nat := [4, 2, 2, 1, 2, 1, 3, 8]
def baseStart_3183358 : Nat := 118140960795 + 3183358 * 2 ^ 59
def prefixEnd_3183358 : Nat := 4983230072969 + 3 ^ 40 * 3183358 * 2
def baseEnd_3183358 : Nat := 60540472197609678921667

theorem tailTrace_3183358 : CollatzResearch.WordTrace tailWord_3183358 prefixEnd_3183358 60540472197609678921667 := by
  unfold tailWord_3183358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513325600155639388423841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77404403200830076738260485 14513325600155639388423841)
  ·
    refine ⟨10884994200116729541317881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14513325600155639388423841 10884994200116729541317881)
    ·
      refine ⟨8163745650087547155988411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10884994200116729541317881 8163745650087547155988411)
      ·
        refine ⟨12245618475131320733982617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163745650087547155988411 12245618475131320733982617)
        ·
          refine ⟨9184213856348490550486963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12245618475131320733982617 9184213856348490550486963)
          ·
            refine ⟨13776320784522735825730445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9184213856348490550486963 13776320784522735825730445)
            ·
              refine ⟨5166120294196025934648917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13776320784522735825730445 5166120294196025934648917)
              ·
                refine ⟨60540472197609678921667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5166120294196025934648917 60540472197609678921667)
                ·
                  rfl

theorem cell23_3183358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_3183358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183358 prefixEnd_3183358 := by exact prefixLift 3183358
  have htrace : WordTrace (prefixWord ++ tailWord_3183358) baseStart_3183358 baseEnd_3183358 := by
    simpa [prefixWord, tailWord_3183358, baseEnd_3183358] using wordTrace_append hprefix tailTrace_3183358
  have hstable : (prefixWord ++ tailWord_3183358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183358).length < 2 ^ (prefixWord ++ tailWord_3183358).sum := by decide
  have hdescent : baseEnd_3183358 < baseStart_3183358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183368 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3183368 : Nat := 118140960795 + 3183368 * 2 ^ 59
def prefixEnd_3183368 : Nat := 4983230072969 + 3 ^ 40 * 3183368 * 2
def baseEnd_3183368 : Nat := 1634597884142006291759963

theorem tailTrace_3183368 : CollatzResearch.WordTrace tailWord_3183368 prefixEnd_3183368 1634597884142006291759963 := by
  unfold tailWord_3183368
  simp only [CollatzResearch.WordTrace]
  refine ⟨58053484765604443407627379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77404646354139257876836505 58053484765604443407627379)
  ·
    refine ⟨87080227148406665111441069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58053484765604443407627379 87080227148406665111441069)
    ·
      refine ⟨32655085180652499416790401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87080227148406665111441069 32655085180652499416790401)
      ·
        refine ⟨24491313885489374562592801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32655085180652499416790401 24491313885489374562592801)
        ·
          refine ⟨18368485414117030921944601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24491313885489374562592801 18368485414117030921944601)
          ·
            refine ⟨13776364060587773191458451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18368485414117030921944601 13776364060587773191458451)
            ·
              refine ⟨20664546090881659787187677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13776364060587773191458451 20664546090881659787187677)
              ·
                refine ⟨7749204784080622420195379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20664546090881659787187677 7749204784080622420195379)
                ·
                  refine ⟨11623807176120933630293069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749204784080622420195379 11623807176120933630293069)
                  ·
                    refine ⟨4358927691045350111359901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11623807176120933630293069 4358927691045350111359901)
                    ·
                      refine ⟨1634597884142006291759963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4358927691045350111359901 1634597884142006291759963)
                      ·
                        rfl

theorem cell23_3183368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3183368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183368 prefixEnd_3183368 := by exact prefixLift 3183368
  have htrace : WordTrace (prefixWord ++ tailWord_3183368) baseStart_3183368 baseEnd_3183368 := by
    simpa [prefixWord, tailWord_3183368, baseEnd_3183368] using wordTrace_append hprefix tailTrace_3183368
  have hstable : (prefixWord ++ tailWord_3183368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183368).length < 2 ^ (prefixWord ++ tailWord_3183368).sum := by decide
  have hdescent : baseEnd_3183368 < baseStart_3183368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183381 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3183381 : Nat := 118140960795 + 3183381 * 2 ^ 59
def prefixEnd_3183381 : Nat := 4983230072969 + 3 ^ 40 * 3183381 * 2
def baseEnd_3183381 : Nat := 1634604559390514740897403

theorem tailTrace_3183381 : CollatzResearch.WordTrace tailWord_3183381 prefixEnd_3183381 1634604559390514740897403 := by
  unfold tailWord_3183381
  simp only [CollatzResearch.WordTrace]
  refine ⟨116107443680161790035477997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77404962453441193356985331 116107443680161790035477997)
  ·
    refine ⟨43540291380060671263304249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116107443680161790035477997 43540291380060671263304249)
    ·
      refine ⟨32655218535045503447478187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43540291380060671263304249 32655218535045503447478187)
      ·
        refine ⟨48982827802568255171217281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32655218535045503447478187 48982827802568255171217281)
        ·
          refine ⟨36737120851926191378412961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48982827802568255171217281 36737120851926191378412961)
          ·
            refine ⟨27552840638944643533809721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36737120851926191378412961 27552840638944643533809721)
            ·
              refine ⟨20664630479208482650357291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27552840638944643533809721 20664630479208482650357291)
              ·
                refine ⟨30996945718812723975535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20664630479208482650357291 30996945718812723975535937)
                ·
                  refine ⟨23247709289109542981651953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30996945718812723975535937 23247709289109542981651953)
                  ·
                    refine ⟨17435781966832157236238965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23247709289109542981651953 17435781966832157236238965)
                    ·
                      refine ⟨1634604559390514740897403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17435781966832157236238965 1634604559390514740897403)
                      ·
                        rfl

theorem cell23_3183381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3183381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183381 prefixEnd_3183381 := by exact prefixLift 3183381
  have htrace : WordTrace (prefixWord ++ tailWord_3183381) baseStart_3183381 baseEnd_3183381 := by
    simpa [prefixWord, tailWord_3183381, baseEnd_3183381] using wordTrace_append hprefix tailTrace_3183381
  have hstable : (prefixWord ++ tailWord_3183381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183381).length < 2 ^ (prefixWord ++ tailWord_3183381).sum := by decide
  have hdescent : baseEnd_3183381 < baseStart_3183381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183408 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2]
def baseStart_3183408 : Nat := 118140960795 + 3183408 * 2 ^ 59
def prefixEnd_3183408 : Nat := 4983230072969 + 3 ^ 40 * 3183408 * 2
def baseEnd_3183408 : Nat := 1634618423368186135259779

theorem tailTrace_3183408 : CollatzResearch.WordTrace tailWord_3183408 prefixEnd_3183408 1634618423368186135259779 := by
  unfold tailWord_3183408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58054214225531986823355439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77405618967375982431140585 58054214225531986823355439)
  ·
    refine ⟨87081321338297980235033159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58054214225531986823355439 87081321338297980235033159)
    ·
      refine ⟨130621982007446970352549739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87081321338297980235033159 130621982007446970352549739)
      ·
        refine ⟨195932973011170455528824609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130621982007446970352549739 195932973011170455528824609)
        ·
          refine ⟨146949729758377841646618457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195932973011170455528824609 146949729758377841646618457)
          ·
            refine ⟨110212297318783381234963843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146949729758377841646618457 110212297318783381234963843)
            ·
              refine ⟨165318445978175071852445765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110212297318783381234963843 165318445978175071852445765)
              ·
                refine ⟨30997208620907825972333581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165318445978175071852445765 30997208620907825972333581)
                ·
                  refine ⟨11623953232840434739625093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30997208620907825972333581 11623953232840434739625093)
                  ·
                    refine ⟨2179491231157581513679705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11623953232840434739625093 2179491231157581513679705)
                    ·
                      refine ⟨1634618423368186135259779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179491231157581513679705 1634618423368186135259779)
                      ·
                        rfl

theorem cell23_3183408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2].length) (baseStart_3183408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183408 prefixEnd_3183408 := by exact prefixLift 3183408
  have htrace : WordTrace (prefixWord ++ tailWord_3183408) baseStart_3183408 baseEnd_3183408 := by
    simpa [prefixWord, tailWord_3183408, baseEnd_3183408] using wordTrace_append hprefix tailTrace_3183408
  have hstable : (prefixWord ++ tailWord_3183408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183408).length < 2 ^ (prefixWord ++ tailWord_3183408).sum := by decide
  have hdescent : baseEnd_3183408 < baseStart_3183408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183495 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3183495 : Nat := 118140960795 + 3183495 * 2 ^ 59
def prefixEnd_3183495 : Nat := 4983230072969 + 3 ^ 40 * 3183495 * 2
def baseEnd_3183495 : Nat := 544887698728375764957293

theorem tailTrace_3183495 : CollatzResearch.WordTrace tailWord_3183495 prefixEnd_3183495 544887698728375764957293 := by
  unfold tailWord_3183495
  simp only [CollatzResearch.WordTrace]
  refine ⟨116111601601748787505127939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77407734401165858336751959 116111601601748787505127939)
  ·
    refine ⟨174167402402623181257691909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116111601601748787505127939 174167402402623181257691909)
    ·
      refine ⟨32656387950491846485817233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174167402402623181257691909 32656387950491846485817233)
      ·
        refine ⟨24492290962868884864362925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32656387950491846485817233 24492290962868884864362925)
        ·
          refine ⟨9184609111075831824136097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24492290962868884864362925 9184609111075831824136097)
          ·
            refine ⟨6888456833306873868102073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9184609111075831824136097 6888456833306873868102073)
            ·
              refine ⟨5166342624980155401076555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888456833306873868102073 5166342624980155401076555)
              ·
                refine ⟨7749513937470233101614833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166342624980155401076555 7749513937470233101614833)
                ·
                  refine ⟨5812135453102674826211125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749513937470233101614833 5812135453102674826211125)
                  ·
                    refine ⟨544887698728375764957293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5812135453102674826211125 544887698728375764957293)
                    ·
                      rfl

theorem cell23_3183495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3183495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183495 prefixEnd_3183495 := by exact prefixLift 3183495
  have htrace : WordTrace (prefixWord ++ tailWord_3183495) baseStart_3183495 baseEnd_3183495 := by
    simpa [prefixWord, tailWord_3183495, baseEnd_3183495] using wordTrace_append hprefix tailTrace_3183495
  have hstable : (prefixWord ++ tailWord_3183495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183495).length < 2 ^ (prefixWord ++ tailWord_3183495).sum := by decide
  have hdescent : baseEnd_3183495 < baseStart_3183495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183516 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 5]
def baseStart_3183516 : Nat := 118140960795 + 3183516 * 2 ^ 59
def prefixEnd_3183516 : Nat := 4983230072969 + 3 ^ 40 * 3183516 * 2
def baseEnd_3183516 : Nat := 181630431030985745856587

theorem tailTrace_3183516 : CollatzResearch.WordTrace tailWord_3183516 prefixEnd_3183516 181630431030985745856587 := by
  unfold tailWord_3183516
  simp only [CollatzResearch.WordTrace]
  refine ⟨58056183767336354045821201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77408245023115138727761601 58056183767336354045821201)
  ·
    refine ⟨43542137825502265534365901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58056183767336354045821201 43542137825502265534365901)
    ·
      refine ⟨16328301684563349575387213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43542137825502265534365901 16328301684563349575387213)
      ·
        refine ⟨6123113131711256090770205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16328301684563349575387213 6123113131711256090770205)
        ·
          refine ⟨2296167424391721034038827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6123113131711256090770205 2296167424391721034038827)
          ·
            refine ⟨3444251136587581551058241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296167424391721034038827 3444251136587581551058241)
            ·
              refine ⟨2583188352440686163293681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444251136587581551058241 2583188352440686163293681)
              ·
                refine ⟨1937391264330514622470261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583188352440686163293681 1937391264330514622470261)
                ·
                  refine ⟨181630431030985745856587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937391264330514622470261 181630431030985745856587)
                  ·
                    rfl

theorem cell23_3183516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_3183516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183516 prefixEnd_3183516 := by exact prefixLift 3183516
  have htrace : WordTrace (prefixWord ++ tailWord_3183516) baseStart_3183516 baseEnd_3183516 := by
    simpa [prefixWord, tailWord_3183516, baseEnd_3183516] using wordTrace_append hprefix tailTrace_3183516
  have hstable : (prefixWord ++ tailWord_3183516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183516).length < 2 ^ (prefixWord ++ tailWord_3183516).sum := by decide
  have hdescent : baseEnd_3183516 < baseStart_3183516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183549 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_3183549 : Nat := 118140960795 + 3183549 * 2 ^ 59
def prefixEnd_3183549 : Nat := 4983230072969 + 3 ^ 40 * 3183549 * 2
def baseEnd_3183549 : Nat := 1634690824140470083596631

theorem tailTrace_3183549 : CollatzResearch.WordTrace tailWord_3183549 prefixEnd_3183549 1634690824140470083596631 := by
  unfold tailWord_3183549
  simp only [CollatzResearch.WordTrace]
  refine ⟨116113571143553154727593701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77409047429035436485062467 116113571143553154727593701)
  ·
    refine ⟨21771294589416216511423819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116113571143553154727593701 21771294589416216511423819)
    ·
      refine ⟨32656941884124324767135729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771294589416216511423819 32656941884124324767135729)
      ·
        refine ⟨24492706413093243575351797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32656941884124324767135729 24492706413093243575351797)
        ·
          refine ⟨2296191226227491585189231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24492706413093243575351797 2296191226227491585189231)
          ·
            refine ⟨3444286839341237377783847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296191226227491585189231 3444286839341237377783847)
            ·
              refine ⟨5166430259011856066675771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444286839341237377783847 5166430259011856066675771)
              ·
                refine ⟨7749645388517784100013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166430259011856066675771 7749645388517784100013657)
                ·
                  refine ⟨5812234041388338075010243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749645388517784100013657 5812234041388338075010243)
                  ·
                    refine ⟨8718351062082507112515365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5812234041388338075010243 8718351062082507112515365)
                    ·
                      refine ⟨1634690824140470083596631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8718351062082507112515365 1634690824140470083596631)
                      ·
                        rfl

theorem cell23_3183549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_3183549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183549 prefixEnd_3183549 := by exact prefixLift 3183549
  have htrace : WordTrace (prefixWord ++ tailWord_3183549) baseStart_3183549 baseEnd_3183549 := by
    simpa [prefixWord, tailWord_3183549, baseEnd_3183549] using wordTrace_append hprefix tailTrace_3183549
  have hstable : (prefixWord ++ tailWord_3183549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183549).length < 2 ^ (prefixWord ++ tailWord_3183549).sum := by decide
  have hdescent : baseEnd_3183549 < baseStart_3183549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183552 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_3183552 : Nat := 118140960795 + 3183552 * 2 ^ 59
def prefixEnd_3183552 : Nat := 4983230072969 + 3 ^ 40 * 3183552 * 2
def baseEnd_3183552 : Nat := 1634692364582433571859117

theorem tailTrace_3183552 : CollatzResearch.WordTrace tailWord_3183552 prefixEnd_3183552 1634692364582433571859117 := by
  unfold tailWord_3183552
  simp only [CollatzResearch.WordTrace]
  refine ⟨58056840281271143119976455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77409120375028190826635273 58056840281271143119976455)
  ·
    refine ⟨87085260421906714679964683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58056840281271143119976455 87085260421906714679964683)
    ·
      refine ⟨130627890632860072019947025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87085260421906714679964683 130627890632860072019947025)
      ·
        refine ⟨97970917974645054014960269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130627890632860072019947025 97970917974645054014960269)
        ·
          refine ⟨36739094240491895255610101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97970917974645054014960269 36739094240491895255610101)
          ·
            refine ⟨3444290085046115180213447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36739094240491895255610101 3444290085046115180213447)
            ·
              refine ⟨5166435127569172770320171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444290085046115180213447 5166435127569172770320171)
              ·
                refine ⟨7749652691353759155480257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166435127569172770320171 7749652691353759155480257)
                ·
                  refine ⟨5812239518515319366610193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7749652691353759155480257 5812239518515319366610193)
                  ·
                    refine ⟨4359179638886489524957645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812239518515319366610193 4359179638886489524957645)
                    ·
                      refine ⟨1634692364582433571859117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359179638886489524957645 1634692364582433571859117)
                      ·
                        rfl

theorem cell23_3183552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_3183552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183552 prefixEnd_3183552 := by exact prefixLift 3183552
  have htrace : WordTrace (prefixWord ++ tailWord_3183552) baseStart_3183552 baseEnd_3183552 := by
    simpa [prefixWord, tailWord_3183552, baseEnd_3183552] using wordTrace_append hprefix tailTrace_3183552
  have hstable : (prefixWord ++ tailWord_3183552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183552).length < 2 ^ (prefixWord ++ tailWord_3183552).sum := by decide
  have hdescent : baseEnd_3183552 < baseStart_3183552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183572 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 6]
def baseStart_3183572 : Nat := 118140960795 + 3183572 * 2 ^ 59
def prefixEnd_3183572 : Nat := 4983230072969 + 3 ^ 40 * 3183572 * 2
def baseEnd_3183572 : Nat := 181633626021724832623225

theorem tailTrace_3183572 : CollatzResearch.WordTrace tailWord_3183572 prefixEnd_3183572 181633626021724832623225 := by
  unfold tailWord_3183572
  simp only [CollatzResearch.WordTrace]
  refine ⟨58057205011234914827840485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77409606681646553103787313 58057205011234914827840485)
  ·
    refine ⟨10885725939606546530220091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58057205011234914827840485 10885725939606546530220091)
    ·
      refine ⟨16328588909409819795330137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885725939606546530220091 16328588909409819795330137)
      ·
        refine ⟨12246441682057364846497603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16328588909409819795330137 12246441682057364846497603)
        ·
          refine ⟨18369662523086047269746405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246441682057364846497603 18369662523086047269746405)
          ·
            refine ⟨3444311723078633863077451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18369662523086047269746405 3444311723078633863077451)
            ·
              refine ⟨5166467584617950794616177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444311723078633863077451 5166467584617950794616177)
              ·
                refine ⟨3874850688463463095962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5166467584617950794616177 3874850688463463095962133)
                ·
                  refine ⟨181633626021724832623225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3874850688463463095962133 181633626021724832623225)
                  ·
                    rfl

theorem cell23_3183572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_3183572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183572 prefixEnd_3183572 := by exact prefixLift 3183572
  have htrace : WordTrace (prefixWord ++ tailWord_3183572) baseStart_3183572 baseEnd_3183572 := by
    simpa [prefixWord, tailWord_3183572, baseEnd_3183572] using wordTrace_append hprefix tailTrace_3183572
  have hstable : (prefixWord ++ tailWord_3183572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183572).length < 2 ^ (prefixWord ++ tailWord_3183572).sum := by decide
  have hdescent : baseEnd_3183572 < baseStart_3183572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183588 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3183588 : Nat := 118140960795 + 3183588 * 2 ^ 59
def prefixEnd_3183588 : Nat := 4983230072969 + 3 ^ 40 * 3183588 * 2
def baseEnd_3183588 : Nat := 1634710849885995431008951

theorem tailTrace_3183588 : CollatzResearch.WordTrace tailWord_3183588 prefixEnd_3183588 1634710849885995431008951 := by
  unfold tailWord_3183588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58057496795205932194131709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77409995726941242925508945 58057496795205932194131709)
  ·
    refine ⟨21771561298202224572799391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58057496795205932194131709 21771561298202224572799391)
    ·
      refine ⟨32657341947303336859199087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771561298202224572799391 32657341947303336859199087)
      ·
        refine ⟨48986012920955005288798631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32657341947303336859199087 48986012920955005288798631)
        ·
          refine ⟨73479019381432507933197947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48986012920955005288798631 73479019381432507933197947)
          ·
            refine ⟨110218529072148761899796921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73479019381432507933197947 110218529072148761899796921)
            ·
              refine ⟨82663896804111571424847691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110218529072148761899796921 82663896804111571424847691)
              ·
                refine ⟨123995845206167357137271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82663896804111571424847691 123995845206167357137271537)
                ·
                  refine ⟨92996883904625517852953653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123995845206167357137271537 92996883904625517852953653)
                  ·
                    refine ⟨8718457866058642298714405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92996883904625517852953653 8718457866058642298714405)
                    ·
                      refine ⟨1634710849885995431008951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8718457866058642298714405 1634710849885995431008951)
                      ·
                        rfl

theorem cell23_3183588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3183588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183588 prefixEnd_3183588 := by exact prefixLift 3183588
  have htrace : WordTrace (prefixWord ++ tailWord_3183588) baseStart_3183588 baseEnd_3183588 := by
    simpa [prefixWord, tailWord_3183588, baseEnd_3183588] using wordTrace_append hprefix tailTrace_3183588
  have hstable : (prefixWord ++ tailWord_3183588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183588).length < 2 ^ (prefixWord ++ tailWord_3183588).sum := by decide
  have hdescent : baseEnd_3183588 < baseStart_3183588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183589 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 6]
def baseStart_3183589 : Nat := 118140960795 + 3183589 * 2 ^ 59
def prefixEnd_3183589 : Nat := 4983230072969 + 3 ^ 40 * 3183589 * 2
def baseEnd_3183589 : Nat := 181634595929627769677383

theorem tailTrace_3183589 : CollatzResearch.WordTrace tailWord_3183589 prefixEnd_3183589 181634595929627769677383 := by
  unfold tailWord_3183589
  simp only [CollatzResearch.WordTrace]
  refine ⟨116115030063408241559049821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77410020042272161039366547 116115030063408241559049821)
  ·
    refine ⟨43543136273778090584643683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116115030063408241559049821 43543136273778090584643683)
    ·
      refine ⟨65314704410667135876965525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43543136273778090584643683 65314704410667135876965525)
      ·
        refine ⟨3061626769250021994232759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65314704410667135876965525 3061626769250021994232759)
        ·
          refine ⟨4592440153875032991349139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061626769250021994232759 4592440153875032991349139)
          ·
            refine ⟨6888660230812549487023709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592440153875032991349139 6888660230812549487023709)
            ·
              refine ⟨2583247586554706057633891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6888660230812549487023709 2583247586554706057633891)
              ·
                refine ⟨3874871379832059086450837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583247586554706057633891 3874871379832059086450837)
                ·
                  refine ⟨181634595929627769677383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3874871379832059086450837 181634595929627769677383)
                  ·
                    rfl

theorem cell23_3183589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_3183589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183589 prefixEnd_3183589 := by exact prefixLift 3183589
  have htrace : WordTrace (prefixWord ++ tailWord_3183589) baseStart_3183589 baseEnd_3183589 := by
    simpa [prefixWord, tailWord_3183589, baseEnd_3183589] using wordTrace_append hprefix tailTrace_3183589
  have hstable : (prefixWord ++ tailWord_3183589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183589).length < 2 ^ (prefixWord ++ tailWord_3183589).sum := by decide
  have hdescent : baseEnd_3183589 < baseStart_3183589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183608 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3183608 : Nat := 118140960795 + 3183608 * 2 ^ 59
def prefixEnd_3183608 : Nat := 4983230072969 + 3 ^ 40 * 3183608 * 2
def baseEnd_3183608 : Nat := 1634721119499085352758859

theorem tailTrace_3183608 : CollatzResearch.WordTrace tailWord_3183608 prefixEnd_3183608 1634721119499085352758859 := by
  unfold tailWord_3183608
  simp only [CollatzResearch.WordTrace]
  refine ⟨58057861525169703901995739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77410482033559605202660985 58057861525169703901995739)
  ·
    refine ⟨87086792287754555852993609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58057861525169703901995739 87086792287754555852993609)
    ·
      refine ⟨65315094215815916889745207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87086792287754555852993609 65315094215815916889745207)
      ·
        refine ⟨97972641323723875334617811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65315094215815916889745207 97972641323723875334617811)
        ·
          refine ⟨146958961985585813001926717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97972641323723875334617811 146958961985585813001926717)
          ·
            refine ⟨55109610744594679875722519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146958961985585813001926717 55109610744594679875722519)
            ·
              refine ⟨82664416116892019813583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55109610744594679875722519 82664416116892019813583779)
              ·
                refine ⟨123996624175338029720375669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82664416116892019813583779 123996624175338029720375669)
                ·
                  refine ⟨11624683516437940286285219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123996624175338029720375669 11624683516437940286285219)
                  ·
                    refine ⟨17437025274656910429427829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11624683516437940286285219 17437025274656910429427829)
                    ·
                      refine ⟨1634721119499085352758859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17437025274656910429427829 1634721119499085352758859)
                      ·
                        rfl

theorem cell23_3183608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3183608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183608 prefixEnd_3183608 := by exact prefixLift 3183608
  have htrace : WordTrace (prefixWord ++ tailWord_3183608) baseStart_3183608 baseEnd_3183608 := by
    simpa [prefixWord, tailWord_3183608, baseEnd_3183608] using wordTrace_append hprefix tailTrace_3183608
  have hstable : (prefixWord ++ tailWord_3183608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183608).length < 2 ^ (prefixWord ++ tailWord_3183608).sum := by decide
  have hdescent : baseEnd_3183608 < baseStart_3183608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183628 : List Nat := [2, 2, 1, 2, 3, 2, 11]
def baseStart_3183628 : Nat := 118140960795 + 3183628 * 2 ^ 59
def prefixEnd_3183628 : Nat := 4983230072969 + 3 ^ 40 * 3183628 * 2
def baseEnd_3183628 : Nat := 20181869001384879932207

theorem tailTrace_3183628 : CollatzResearch.WordTrace tailWord_3183628 prefixEnd_3183628 20181869001384879932207 := by
  unfold tailWord_3183628
  simp only [CollatzResearch.WordTrace]
  refine ⟨58058226255133475609859769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77410968340177967479813025 58058226255133475609859769)
  ·
    refine ⟨43543669691350106707394827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58058226255133475609859769 43543669691350106707394827)
    ·
      refine ⟨65315504537025160061092241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43543669691350106707394827 65315504537025160061092241)
      ·
        refine ⟨48986628402768870045819181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65315504537025160061092241 48986628402768870045819181)
        ·
          refine ⟨18369985651038326267182193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48986628402768870045819181 18369985651038326267182193)
          ·
            refine ⟨13777489238278744700386645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18369985651038326267182193 13777489238278744700386645)
            ·
              refine ⟨20181869001384879932207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13777489238278744700386645 20181869001384879932207)
              ·
                rfl

theorem cell23_3183628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 11].length) (baseStart_3183628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183628 prefixEnd_3183628 := by exact prefixLift 3183628
  have htrace : WordTrace (prefixWord ++ tailWord_3183628) baseStart_3183628 baseEnd_3183628 := by
    simpa [prefixWord, tailWord_3183628, baseEnd_3183628] using wordTrace_append hprefix tailTrace_3183628
  have hstable : (prefixWord ++ tailWord_3183628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183628).length < 2 ^ (prefixWord ++ tailWord_3183628).sum := by decide
  have hdescent : baseEnd_3183628 < baseStart_3183628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183649 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_3183649 : Nat := 118140960795 + 3183649 * 2 ^ 59
def prefixEnd_3183649 : Nat := 4983230072969 + 3 ^ 40 * 3183649 * 2
def baseEnd_3183649 : Nat := 544914057401973230782057

theorem tailTrace_3183649 : CollatzResearch.WordTrace tailWord_3183649 prefixEnd_3183649 544914057401973230782057 := by
  unfold tailWord_3183649
  simp only [CollatzResearch.WordTrace]
  refine ⟨116117218443190871806234001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77411478962127247870822667 116117218443190871806234001)
  ·
    refine ⟨87087913832393153854675501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116117218443190871806234001 87087913832393153854675501)
    ·
      refine ⟨32657967687147432695503313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87087913832393153854675501 32657967687147432695503313)
      ·
        refine ⟨24493475765360574521627485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32657967687147432695503313 24493475765360574521627485)
        ·
          refine ⟨9185053412010215445610307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24493475765360574521627485 9185053412010215445610307)
          ·
            refine ⟨13777580118015323168415461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9185053412010215445610307 13777580118015323168415461)
            ·
              refine ⟨2583296272127873094077899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13777580118015323168415461 2583296272127873094077899)
              ·
                refine ⟨3874944408191809641116849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583296272127873094077899 3874944408191809641116849)
                ·
                  refine ⟨2906208306143857230837637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3874944408191809641116849 2906208306143857230837637)
                  ·
                    refine ⟨544914057401973230782057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906208306143857230837637 544914057401973230782057)
                    ·
                      rfl

theorem cell23_3183649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_3183649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183649 prefixEnd_3183649 := by exact prefixLift 3183649
  have htrace : WordTrace (prefixWord ++ tailWord_3183649) baseStart_3183649 baseEnd_3183649 := by
    simpa [prefixWord, tailWord_3183649, baseEnd_3183649] using wordTrace_append hprefix tailTrace_3183649
  have hstable : (prefixWord ++ tailWord_3183649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183649).length < 2 ^ (prefixWord ++ tailWord_3183649).sum := by decide
  have hdescent : baseEnd_3183649 < baseStart_3183649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183672 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3183672 : Nat := 118140960795 + 3183672 * 2 ^ 59
def prefixEnd_3183672 : Nat := 4983230072969 + 3 ^ 40 * 3183672 * 2
def baseEnd_3183672 : Nat := 1634753982260973102358565

theorem tailTrace_3183672 : CollatzResearch.WordTrace tailWord_3183672 prefixEnd_3183672 1634753982260973102358565 := by
  unfold tailWord_3183672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58059028661053773367160635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77412038214738364489547513 58059028661053773367160635)
  ·
    refine ⟨87088542991580660050740953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58059028661053773367160635 87088542991580660050740953)
    ·
      refine ⟨65316407243685495038055715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87088542991580660050740953 65316407243685495038055715)
      ·
        refine ⟨97974610865528242557083573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65316407243685495038055715 97974610865528242557083573)
        ·
          refine ⟨9185119768643272739726585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97974610865528242557083573 9185119768643272739726585)
          ·
            refine ⟨6888839826482454554794939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185119768643272739726585 6888839826482454554794939)
            ·
              refine ⟨10333259739723681832192409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888839826482454554794939 10333259739723681832192409)
              ·
                refine ⟨7749944804792761374144307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333259739723681832192409 7749944804792761374144307)
                ·
                  refine ⟨11624917207189142061216461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7749944804792761374144307 11624917207189142061216461)
                  ·
                    refine ⟨4359343952695928272956173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11624917207189142061216461 4359343952695928272956173)
                    ·
                      refine ⟨1634753982260973102358565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359343952695928272956173 1634753982260973102358565)
                      ·
                        rfl

theorem cell23_3183672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3183672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183672 prefixEnd_3183672 := by exact prefixLift 3183672
  have htrace : WordTrace (prefixWord ++ tailWord_3183672) baseStart_3183672 baseEnd_3183672 := by
    simpa [prefixWord, tailWord_3183672, baseEnd_3183672] using wordTrace_append hprefix tailTrace_3183672
  have hstable : (prefixWord ++ tailWord_3183672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183672).length < 2 ^ (prefixWord ++ tailWord_3183672).sum := by decide
  have hdescent : baseEnd_3183672 < baseStart_3183672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183715 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3183715 : Nat := 118140960795 + 3183715 * 2 ^ 59
def prefixEnd_3183715 : Nat := 4983230072969 + 3 ^ 40 * 3183715 * 2
def baseEnd_3183715 : Nat := 1634776061929116434120867

theorem tailTrace_3183715 : CollatzResearch.WordTrace tailWord_3183715 prefixEnd_3183715 1634776061929116434120867 := by
  unfold tailWord_3183715
  simp only [CollatzResearch.WordTrace]
  refine ⟨116119625660951765078136599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77413083773967843385424399 116119625660951765078136599)
  ·
    refine ⟨174179438491427647617204899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116119625660951765078136599 174179438491427647617204899)
    ·
      refine ⟨261269157737141471425807349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174179438491427647617204899 261269157737141471425807349)
      ·
        refine ⟨24493983537857012946169439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261269157737141471425807349 24493983537857012946169439)
        ·
          refine ⟨36740975306785519419254159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24493983537857012946169439 36740975306785519419254159)
          ·
            refine ⟨55111462960178279128881239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36740975306785519419254159 55111462960178279128881239)
            ·
              refine ⟨82667194440267418693321859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55111462960178279128881239 82667194440267418693321859)
              ·
                refine ⟨124000791660401128039982789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82667194440267418693321859 124000791660401128039982789)
                ·
                  refine ⟨23250148436325211507496773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124000791660401128039982789 23250148436325211507496773)
                  ·
                    refine ⟨4359402831810977157655645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23250148436325211507496773 4359402831810977157655645)
                    ·
                      refine ⟨1634776061929116434120867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359402831810977157655645 1634776061929116434120867)
                      ·
                        rfl

theorem cell23_3183715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3183715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183715 prefixEnd_3183715 := by exact prefixLift 3183715
  have htrace : WordTrace (prefixWord ++ tailWord_3183715) baseStart_3183715 baseEnd_3183715 := by
    simpa [prefixWord, tailWord_3183715, baseEnd_3183715] using wordTrace_append hprefix tailTrace_3183715
  have hstable : (prefixWord ++ tailWord_3183715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183715).length < 2 ^ (prefixWord ++ tailWord_3183715).sum := by decide
  have hdescent : baseEnd_3183715 < baseStart_3183715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183733 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3183733 : Nat := 118140960795 + 3183733 * 2 ^ 59
def prefixEnd_3183733 : Nat := 4983230072969 + 3 ^ 40 * 3183733 * 2
def baseEnd_3183733 : Nat := 1634785304580897363695785

theorem tailTrace_3183733 : CollatzResearch.WordTrace tailWord_3183733 prefixEnd_3183733 1634785304580897363695785 := by
  unfold tailWord_3183733
  simp only [CollatzResearch.WordTrace]
  refine ⟨116120282174886554152291853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77413521449924369434861235 116120282174886554152291853)
  ·
    refine ⟨43545105815582457807109445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116120282174886554152291853 43545105815582457807109445)
    ·
      refine ⟨8164707340421710838833021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43545105815582457807109445 8164707340421710838833021)
      ·
        refine ⟨3061765252658141564562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8164707340421710838833021 3061765252658141564562383)
        ·
          refine ⟨4592647878987212346843575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061765252658141564562383 4592647878987212346843575)
          ·
            refine ⟨6888971818480818520265363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592647878987212346843575 6888971818480818520265363)
            ·
              refine ⟨10333457727721227780398045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6888971818480818520265363 10333457727721227780398045)
              ·
                refine ⟨3875046647895460417649267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10333457727721227780398045 3875046647895460417649267)
                ·
                  refine ⟨5812569971843190626473901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875046647895460417649267 5812569971843190626473901)
                  ·
                    refine ⟨2179713739441196484927713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5812569971843190626473901 2179713739441196484927713)
                    ·
                      refine ⟨1634785304580897363695785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179713739441196484927713 1634785304580897363695785)
                      ·
                        rfl

theorem cell23_3183733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3183733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183733 prefixEnd_3183733 := by exact prefixLift 3183733
  have htrace : WordTrace (prefixWord ++ tailWord_3183733) baseStart_3183733 baseEnd_3183733 := by
    simpa [prefixWord, tailWord_3183733, baseEnd_3183733] using wordTrace_append hprefix tailTrace_3183733
  have hstable : (prefixWord ++ tailWord_3183733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183733).length < 2 ^ (prefixWord ++ tailWord_3183733).sum := by decide
  have hdescent : baseEnd_3183733 < baseStart_3183733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183765 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_3183765 : Nat := 118140960795 + 3183765 * 2 ^ 59
def prefixEnd_3183765 : Nat := 4983230072969 + 3 ^ 40 * 3183765 * 2
def baseEnd_3183765 : Nat := 544933911987280412831879

theorem tailTrace_3183765 : CollatzResearch.WordTrace tailWord_3183765 prefixEnd_3183765 544933911987280412831879 := by
  unfold tailWord_3183765
  simp only [CollatzResearch.WordTrace]
  refine ⟨116121449310770623617456749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77414299540513749078304499 116121449310770623617456749)
  ·
    refine ⟨43545543491538983856546281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116121449310770623617456749 43545543491538983856546281)
    ·
      refine ⟨32659157618654237892409711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43545543491538983856546281 32659157618654237892409711)
      ·
        refine ⟨48988736427981356838614567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32659157618654237892409711 48988736427981356838614567)
        ·
          refine ⟨73483104641972035257921851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48988736427981356838614567 73483104641972035257921851)
          ·
            refine ⟨110224656962958052886882777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73483104641972035257921851 110224656962958052886882777)
            ·
              refine ⟨82668492722218539665162083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110224656962958052886882777 82668492722218539665162083)
              ·
                refine ⟨124002739083327809497743125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82668492722218539665162083 124002739083327809497743125)
                ·
                  refine ⟨5812628394530991070206709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124002739083327809497743125 5812628394530991070206709)
                  ·
                    refine ⟨544933911987280412831879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5812628394530991070206709 544933911987280412831879)
                    ·
                      rfl

theorem cell23_3183765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_3183765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183765 prefixEnd_3183765 := by exact prefixLift 3183765
  have htrace : WordTrace (prefixWord ++ tailWord_3183765) baseStart_3183765 baseEnd_3183765 := by
    simpa [prefixWord, tailWord_3183765, baseEnd_3183765] using wordTrace_append hprefix tailTrace_3183765
  have hstable : (prefixWord ++ tailWord_3183765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183765).length < 2 ^ (prefixWord ++ tailWord_3183765).sum := by decide
  have hdescent : baseEnd_3183765 < baseStart_3183765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183786 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_3183786 : Nat := 118140960795 + 3183786 * 2 ^ 59
def prefixEnd_3183786 : Nat := 4983230072969 + 3 ^ 40 * 3183786 * 2
def baseEnd_3183786 : Nat := 181645835450620628481449

theorem tailTrace_3183786 : CollatzResearch.WordTrace tailWord_3183786 prefixEnd_3183786 181645835450620628481449 := by
  unfold tailWord_3183786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29030553810923636050992803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77414810162463029469314141 29030553810923636050992803)
  ·
    refine ⟨43545830716385454076489205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29030553810923636050992803 43545830716385454076489205)
    ·
      refine ⟨4082421629661136319670863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43545830716385454076489205 4082421629661136319670863)
      ·
        refine ⟨6123632444491704479506295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082421629661136319670863 6123632444491704479506295)
        ·
          refine ⟨9185448666737556719259443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123632444491704479506295 9185448666737556719259443)
          ·
            refine ⟨13778173000106335078889165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9185448666737556719259443 13778173000106335078889165)
            ·
              refine ⟨5166814875039875654583437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13778173000106335078889165 5166814875039875654583437)
              ·
                refine ⟨1937555578139953370468789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166814875039875654583437 1937555578139953370468789)
                ·
                  refine ⟨181645835450620628481449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937555578139953370468789 181645835450620628481449)
                  ·
                    rfl

theorem cell23_3183786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_3183786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183786 prefixEnd_3183786 := by exact prefixLift 3183786
  have htrace : WordTrace (prefixWord ++ tailWord_3183786) baseStart_3183786 baseEnd_3183786 := by
    simpa [prefixWord, tailWord_3183786, baseEnd_3183786] using wordTrace_append hprefix tailTrace_3183786
  have hstable : (prefixWord ++ tailWord_3183786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183786).length < 2 ^ (prefixWord ++ tailWord_3183786).sum := by decide
  have hdescent : baseEnd_3183786 < baseStart_3183786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183809 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3183809 : Nat := 118140960795 + 3183809 * 2 ^ 59
def prefixEnd_3183809 : Nat := 4983230072969 + 3 ^ 40 * 3183809 * 2
def baseEnd_3183809 : Nat := 1634824329110639066345435

theorem tailTrace_3183809 : CollatzResearch.WordTrace tailWord_3183809 prefixEnd_3183809 1634824329110639066345435 := by
  unfold tailWord_3183809
  simp only [CollatzResearch.WordTrace]
  refine ⟨116123054122611219132058481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77415369415074146088038987 116123054122611219132058481)
  ·
    refine ⟨87092290591958414349043861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116123054122611219132058481 87092290591958414349043861)
    ·
      refine ⟨4082451121498050672611431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87092290591958414349043861 4082451121498050672611431)
      ·
        refine ⟨6123676682247076008917147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4082451121498050672611431 6123676682247076008917147)
        ·
          refine ⟨9185515023370614013375721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123676682247076008917147 9185515023370614013375721)
          ·
            refine ⟨6889136267527960510031791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9185515023370614013375721 6889136267527960510031791)
            ·
              refine ⟨10333704401291940765047687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889136267527960510031791 10333704401291940765047687)
              ·
                refine ⟨15500556601937911147571531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10333704401291940765047687 15500556601937911147571531)
                ·
                  refine ⟨23250834902906866721357297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15500556601937911147571531 23250834902906866721357297)
                  ·
                    refine ⟨17438126177180150041017973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23250834902906866721357297 17438126177180150041017973)
                    ·
                      refine ⟨1634824329110639066345435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17438126177180150041017973 1634824329110639066345435)
                      ·
                        rfl

theorem cell23_3183809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3183809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183809 prefixEnd_3183809 := by exact prefixLift 3183809
  have htrace : WordTrace (prefixWord ++ tailWord_3183809) baseStart_3183809 baseEnd_3183809 := by
    simpa [prefixWord, tailWord_3183809, baseEnd_3183809] using wordTrace_append hprefix tailTrace_3183809
  have hstable : (prefixWord ++ tailWord_3183809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183809).length < 2 ^ (prefixWord ++ tailWord_3183809).sum := by decide
  have hdescent : baseEnd_3183809 < baseStart_3183809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183815 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3183815 : Nat := 118140960795 + 3183815 * 2 ^ 59
def prefixEnd_3183815 : Nat := 4983230072969 + 3 ^ 40 * 3183815 * 2
def baseEnd_3183815 : Nat := 1634827409994566042870407

theorem tailTrace_3183815 : CollatzResearch.WordTrace tailWord_3183815 prefixEnd_3183815 1634827409994566042870407 := by
  unfold tailWord_3183815
  simp only [CollatzResearch.WordTrace]
  refine ⟨116123272960589482156776899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77415515307059654771184599 116123272960589482156776899)
  ·
    refine ⟨174184909440884223235165349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116123272960589482156776899 174184909440884223235165349)
    ·
      refine ⟨32659670520165791856593503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174184909440884223235165349 32659670520165791856593503)
      ·
        refine ⟨48989505780248687784890255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32659670520165791856593503 48989505780248687784890255)
        ·
          refine ⟨73484258670373031677335383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48989505780248687784890255 73484258670373031677335383)
          ·
            refine ⟨110226388005559547516003075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73484258670373031677335383 110226388005559547516003075)
            ·
              refine ⟨165339582008339321274004613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110226388005559547516003075 165339582008339321274004613)
              ·
                refine ⟨31001171626563622738875865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165339582008339321274004613 31001171626563622738875865)
                ·
                  refine ⟨23250878719922717054156899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31001171626563622738875865 23250878719922717054156899)
                  ·
                    refine ⟨34876318079884075581235349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23250878719922717054156899 34876318079884075581235349)
                    ·
                      refine ⟨1634827409994566042870407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34876318079884075581235349 1634827409994566042870407)
                      ·
                        rfl

theorem cell23_3183815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3183815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183815 prefixEnd_3183815 := by exact prefixLift 3183815
  have htrace : WordTrace (prefixWord ++ tailWord_3183815) baseStart_3183815 baseEnd_3183815 := by
    simpa [prefixWord, tailWord_3183815, baseEnd_3183815] using wordTrace_append hprefix tailTrace_3183815
  have hstable : (prefixWord ++ tailWord_3183815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183815).length < 2 ^ (prefixWord ++ tailWord_3183815).sum := by decide
  have hdescent : baseEnd_3183815 < baseStart_3183815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183862 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3183862 : Nat := 118140960795 + 3183862 * 2 ^ 59
def prefixEnd_3183862 : Nat := 4983230072969 + 3 ^ 40 * 3183862 * 2
def baseEnd_3183862 : Nat := 1634851543585327358982691

theorem tailTrace_3183862 : CollatzResearch.WordTrace tailWord_3183862 prefixEnd_3183862 1634851543585327358982691 := by
  unfold tailWord_3183862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257811699463700573983615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77416658127612806122491893 7257811699463700573983615)
  ·
    refine ⟨10886717549195550860975423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257811699463700573983615 10886717549195550860975423)
    ·
      refine ⟨16330076323793326291463135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10886717549195550860975423 16330076323793326291463135)
      ·
        refine ⟨24495114485689989437194703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330076323793326291463135 24495114485689989437194703)
        ·
          refine ⟨36742671728534984155792055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24495114485689989437194703 36742671728534984155792055)
          ·
            refine ⟨55114007592802476233688083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36742671728534984155792055 55114007592802476233688083)
            ·
              refine ⟨82671011389203714350532125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55114007592802476233688083 82671011389203714350532125)
              ·
                refine ⟨31001629270951392881449547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82671011389203714350532125 31001629270951392881449547)
                ·
                  refine ⟨46502443906427089322174321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31001629270951392881449547 46502443906427089322174321)
                  ·
                    refine ⟨34876832929820316991630741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46502443906427089322174321 34876832929820316991630741)
                    ·
                      refine ⟨1634851543585327358982691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34876832929820316991630741 1634851543585327358982691)
                      ·
                        rfl

theorem cell23_3183862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3183862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183862 prefixEnd_3183862 := by exact prefixLift 3183862
  have htrace : WordTrace (prefixWord ++ tailWord_3183862) baseStart_3183862 baseEnd_3183862 := by
    simpa [prefixWord, tailWord_3183862, baseEnd_3183862] using wordTrace_append hprefix tailTrace_3183862
  have hstable : (prefixWord ++ tailWord_3183862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183862).length < 2 ^ (prefixWord ++ tailWord_3183862).sum := by decide
  have hdescent : baseEnd_3183862 < baseStart_3183862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183886 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3183886 : Nat := 118140960795 + 3183886 * 2 ^ 59
def prefixEnd_3183886 : Nat := 4983230072969 + 3 ^ 40 * 3183886 * 2
def baseEnd_3183886 : Nat := 1634863867121035265082581

theorem tailTrace_3183886 : CollatzResearch.WordTrace tailWord_3183886 prefixEnd_3183886 1634863867121035265082581 := by
  unfold tailWord_3183886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515732817916532660326439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77417241695554840855074341 14515732817916532660326439)
  ·
    refine ⟨21773599226874798990489659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14515732817916532660326439 21773599226874798990489659)
    ·
      refine ⟨32660398840312198485734489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21773599226874798990489659 32660398840312198485734489)
      ·
        refine ⟨24495299130234148864300867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32660398840312198485734489 24495299130234148864300867)
        ·
          refine ⟨36742948695351223296451301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24495299130234148864300867 36742948695351223296451301)
          ·
            refine ⟨6889302880378354368084619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36742948695351223296451301 6889302880378354368084619)
            ·
              refine ⟨10333954320567531552126929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889302880378354368084619 10333954320567531552126929)
              ·
                refine ⟨7750465740425648664095197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10333954320567531552126929 7750465740425648664095197)
                ·
                  refine ⟨2906424652659618249035699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7750465740425648664095197 2906424652659618249035699)
                  ·
                    refine ⟨4359636978989427373553549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2906424652659618249035699 4359636978989427373553549)
                    ·
                      refine ⟨1634863867121035265082581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359636978989427373553549 1634863867121035265082581)
                      ·
                        rfl

theorem cell23_3183886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3183886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183886 prefixEnd_3183886 := by exact prefixLift 3183886
  have htrace : WordTrace (prefixWord ++ tailWord_3183886) baseStart_3183886 baseEnd_3183886 := by
    simpa [prefixWord, tailWord_3183886, baseEnd_3183886] using wordTrace_append hprefix tailTrace_3183886
  have hstable : (prefixWord ++ tailWord_3183886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183886).length < 2 ^ (prefixWord ++ tailWord_3183886).sum := by decide
  have hdescent : baseEnd_3183886 < baseStart_3183886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183890 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3183890 : Nat := 118140960795 + 3183890 * 2 ^ 59
def prefixEnd_3183890 : Nat := 4983230072969 + 3 ^ 40 * 3183890 * 2
def baseEnd_3183890 : Nat := 1634865921043653249432563

theorem tailTrace_3183890 : CollatzResearch.WordTrace tailWord_3183890 prefixEnd_3183890 1634865921043653249432563 := by
  unfold tailWord_3183890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29031502108829442491439281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77417338956878513310504749 29031502108829442491439281)
  ·
    refine ⟨21773626581622081868579461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29031502108829442491439281 21773626581622081868579461)
    ·
      refine ⟨4082554984054140350358649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21773626581622081868579461 4082554984054140350358649)
      ·
        refine ⟨3061916238040605262768987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082554984054140350358649 3061916238040605262768987)
        ·
          refine ⟨4592874357060907894153481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061916238040605262768987 4592874357060907894153481)
          ·
            refine ⟨3444655767795680920615111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592874357060907894153481 3444655767795680920615111)
            ·
              refine ⟨5166983651693521380922667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444655767795680920615111 5166983651693521380922667)
              ·
                refine ⟨7750475477540282071384001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166983651693521380922667 7750475477540282071384001)
                ·
                  refine ⟨5812856608155211553538001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750475477540282071384001 5812856608155211553538001)
                  ·
                    refine ⟨4359642456116408665153501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5812856608155211553538001 4359642456116408665153501)
                    ·
                      refine ⟨1634865921043653249432563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359642456116408665153501 1634865921043653249432563)
                      ·
                        rfl

theorem cell23_3183890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3183890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183890 prefixEnd_3183890 := by exact prefixLift 3183890
  have htrace : WordTrace (prefixWord ++ tailWord_3183890) baseStart_3183890 baseEnd_3183890 := by
    simpa [prefixWord, tailWord_3183890, baseEnd_3183890] using wordTrace_append hprefix tailTrace_3183890
  have hstable : (prefixWord ++ tailWord_3183890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183890).length < 2 ^ (prefixWord ++ tailWord_3183890).sum := by decide
  have hdescent : baseEnd_3183890 < baseStart_3183890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183896 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3183896 : Nat := 118140960795 + 3183896 * 2 ^ 59
def prefixEnd_3183896 : Nat := 4983230072969 + 3 ^ 40 * 3183896 * 2
def baseEnd_3183896 : Nat := 1634869001927580225957535

theorem tailTrace_3183896 : CollatzResearch.WordTrace tailWord_3183896 prefixEnd_3183896 1634869001927580225957535 := by
  unfold tailWord_3183896
  simp only [CollatzResearch.WordTrace]
  refine ⟨58063113636648016495237771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77417484848864021993650361 58063113636648016495237771)
  ·
    refine ⟨87094670454972024742856657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58063113636648016495237771 87094670454972024742856657)
    ·
      refine ⟨65321002841229018557142493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87094670454972024742856657 65321002841229018557142493)
      ·
        refine ⟨24495376065460881958928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65321002841229018557142493 24495376065460881958928435)
        ·
          refine ⟨36743064098191322938392653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24495376065460881958928435 36743064098191322938392653)
          ·
            refine ⟨13778649036821746101897245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36743064098191322938392653 13778649036821746101897245)
            ·
              refine ⟨5166993388808154788211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13778649036821746101897245 5166993388808154788211467)
              ·
                refine ⟨7750490083212232182317201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5166993388808154788211467 7750490083212232182317201)
                ·
                  refine ⟨5812867562409174136737901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7750490083212232182317201 5812867562409174136737901)
                  ·
                    refine ⟨2179825335903440301276713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5812867562409174136737901 2179825335903440301276713)
                    ·
                      refine ⟨1634869001927580225957535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179825335903440301276713 1634869001927580225957535)
                      ·
                        rfl

theorem cell23_3183896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3183896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183896 prefixEnd_3183896 := by exact prefixLift 3183896
  have htrace : WordTrace (prefixWord ++ tailWord_3183896) baseStart_3183896 baseEnd_3183896 := by
    simpa [prefixWord, tailWord_3183896, baseEnd_3183896] using wordTrace_append hprefix tailTrace_3183896
  have hstable : (prefixWord ++ tailWord_3183896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183896).length < 2 ^ (prefixWord ++ tailWord_3183896).sum := by decide
  have hdescent : baseEnd_3183896 < baseStart_3183896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183906 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3183906 : Nat := 118140960795 + 3183906 * 2 ^ 59
def prefixEnd_3183906 : Nat := 4983230072969 + 3 ^ 40 * 3183906 * 2
def baseEnd_3183906 : Nat := 544958045578041728944163

theorem tailTrace_3183906 : CollatzResearch.WordTrace tailWord_3183906 prefixEnd_3183906 544958045578041728944163 := by
  unfold tailWord_3183906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29031648000814951174584893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77417728002173203132226381 29031648000814951174584893)
  ·
    refine ⟨10886868000305606690469335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29031648000814951174584893 10886868000305606690469335)
    ·
      refine ⟨16330302000458410035704003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10886868000305606690469335 16330302000458410035704003)
      ·
        refine ⟨24495453000687615053556005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16330302000458410035704003 24495453000687615053556005)
        ·
          refine ⟨4592897437628927822541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24495453000687615053556005 4592897437628927822541751)
          ·
            refine ⟨6889346156443391733812627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592897437628927822541751 6889346156443391733812627)
            ·
              refine ⟨10334019234665087600718941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6889346156443391733812627 10334019234665087600718941)
              ·
                refine ⟨3875257212999407850269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10334019234665087600718941 3875257212999407850269603)
                ·
                  refine ⟨5812885819499111775404405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875257212999407850269603 5812885819499111775404405)
                  ·
                    refine ⟨544958045578041728944163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5812885819499111775404405 544958045578041728944163)
                    ·
                      rfl

theorem cell23_3183906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3183906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183906 prefixEnd_3183906 := by exact prefixLift 3183906
  have htrace : WordTrace (prefixWord ++ tailWord_3183906) baseStart_3183906 baseEnd_3183906 := by
    simpa [prefixWord, tailWord_3183906, baseEnd_3183906] using wordTrace_append hprefix tailTrace_3183906
  have hstable : (prefixWord ++ tailWord_3183906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183906).length < 2 ^ (prefixWord ++ tailWord_3183906).sum := by decide
  have hdescent : baseEnd_3183906 < baseStart_3183906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183936 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_3183936 : Nat := 118140960795 + 3183936 * 2 ^ 59
def prefixEnd_3183936 : Nat := 4983230072969 + 3 ^ 40 * 3183936 * 2
def baseEnd_3183936 : Nat := 544963180384586689819117

theorem tailTrace_3183936 : CollatzResearch.WordTrace tailWord_3183936 prefixEnd_3183936 544963180384586689819117 := by
  unfold tailWord_3183936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58063843096575559910965831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77418457462100746547954441 58063843096575559910965831)
  ·
    refine ⟨87095764644863339866448747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58063843096575559910965831 87095764644863339866448747)
    ·
      refine ⟨130643646967295009799673121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87095764644863339866448747 130643646967295009799673121)
      ·
        refine ⟨97982735225471257349754841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130643646967295009799673121 97982735225471257349754841)
        ·
          refine ⟨73487051419103443012316131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97982735225471257349754841 73487051419103443012316131)
          ·
            refine ⟨110230577128655164518474197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73487051419103443012316131 110230577128655164518474197)
            ·
              refine ⟨2583529151452855418401739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110230577128655164518474197 2583529151452855418401739)
              ·
                refine ⟨3875293727179283127602609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583529151452855418401739 3875293727179283127602609)
                ·
                  refine ⟨2906470295384462345701957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875293727179283127602609 2906470295384462345701957)
                  ·
                    refine ⟨544963180384586689819117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906470295384462345701957 544963180384586689819117)
                    ·
                      rfl

theorem cell23_3183936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_3183936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183936 prefixEnd_3183936 := by exact prefixLift 3183936
  have htrace : WordTrace (prefixWord ++ tailWord_3183936) baseStart_3183936 baseEnd_3183936 := by
    simpa [prefixWord, tailWord_3183936, baseEnd_3183936] using wordTrace_append hprefix tailTrace_3183936
  have hstable : (prefixWord ++ tailWord_3183936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183936).length < 2 ^ (prefixWord ++ tailWord_3183936).sum := by decide
  have hdescent : baseEnd_3183936 < baseStart_3183936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183986 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3183986 : Nat := 118140960795 + 3183986 * 2 ^ 59
def prefixEnd_3183986 : Nat := 4983230072969 + 3 ^ 40 * 3183986 * 2
def baseEnd_3183986 : Nat := 1634915215186484873832121

theorem tailTrace_3183986 : CollatzResearch.WordTrace tailWord_3183986 prefixEnd_3183986 1634915215186484873832121 := by
  unfold tailWord_3183986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29032377460742494590312953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77419673228646652240834541 29032377460742494590312953)
  ·
    refine ⟨21774283095556870942734715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29032377460742494590312953 21774283095556870942734715)
    ·
      refine ⟨32661424643335306414102073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21774283095556870942734715 32661424643335306414102073)
      ·
        refine ⟨24496068482501479810576555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32661424643335306414102073 24496068482501479810576555)
        ·
          refine ⟨36744102723752219715864833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24496068482501479810576555 36744102723752219715864833)
          ·
            refine ⟨27558077042814164786898625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36744102723752219715864833 27558077042814164786898625)
            ·
              refine ⟨20668557782110623590173969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27558077042814164786898625 20668557782110623590173969)
              ·
                refine ⟨15501418336582967692630477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20668557782110623590173969 15501418336582967692630477)
                ·
                  refine ⟨5813031876218612884736429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15501418336582967692630477 5813031876218612884736429)
                  ·
                    refine ⟨2179886953581979831776161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5813031876218612884736429 2179886953581979831776161)
                    ·
                      refine ⟨1634915215186484873832121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179886953581979831776161 1634915215186484873832121)
                      ·
                        rfl

theorem cell23_3183986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3183986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183986 prefixEnd_3183986 := by exact prefixLift 3183986
  have htrace : WordTrace (prefixWord ++ tailWord_3183986) baseStart_3183986 baseEnd_3183986 := by
    simpa [prefixWord, tailWord_3183986, baseEnd_3183986] using wordTrace_append hprefix tailTrace_3183986
  have hstable : (prefixWord ++ tailWord_3183986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183986).length < 2 ^ (prefixWord ++ tailWord_3183986).sum := by decide
  have hdescent : baseEnd_3183986 < baseStart_3183986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3183993 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 2, 1, 3]
def baseStart_3183993 : Nat := 118140960795 + 3183993 * 2 ^ 59
def prefixEnd_3183993 : Nat := 4983230072969 + 3 ^ 40 * 3183993 * 2
def baseEnd_3183993 : Nat := 1634918809551066346444589

theorem tailTrace_3183993 : CollatzResearch.WordTrace tailWord_3183993 prefixEnd_3183993 1634918809551066346444589 := by
  unfold tailWord_3183993
  simp only [CollatzResearch.WordTrace]
  refine ⟨116129765153944618556756633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77419843435963079037837755 116129765153944618556756633)
  ·
    refine ⟨87097323865458463917567475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116129765153944618556756633 87097323865458463917567475)
    ·
      refine ⟨130645985798187695876351213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87097323865458463917567475 130645985798187695876351213)
      ·
        refine ⟨48992244674320385953631705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130645985798187695876351213 48992244674320385953631705)
        ·
          refine ⟨36744183505740289465223779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48992244674320385953631705 36744183505740289465223779)
          ·
            refine ⟨55116275258610434197835669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36744183505740289465223779 55116275258610434197835669)
            ·
              refine ⟨2583575402747364103023547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55116275258610434197835669 2583575402747364103023547)
              ·
                refine ⟨3875363104121046154535321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583575402747364103023547 3875363104121046154535321)
                ·
                  refine ⟨2906522328090784615901491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875363104121046154535321 2906522328090784615901491)
                  ·
                    refine ⟨4359783492136176923852237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2906522328090784615901491 4359783492136176923852237)
                    ·
                      refine ⟨1634918809551066346444589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4359783492136176923852237 1634918809551066346444589)
                      ·
                        rfl

theorem cell23_3183993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_3183993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3183993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3183993 prefixEnd_3183993 := by exact prefixLift 3183993
  have htrace : WordTrace (prefixWord ++ tailWord_3183993) baseStart_3183993 baseEnd_3183993 := by
    simpa [prefixWord, tailWord_3183993, baseEnd_3183993] using wordTrace_append hprefix tailTrace_3183993
  have hstable : (prefixWord ++ tailWord_3183993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3183993).length < 2 ^ (prefixWord ++ tailWord_3183993).sum := by decide
  have hdescent : baseEnd_3183993 < baseStart_3183993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3183993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184003 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 1, 3, 2]
def baseStart_3184003 : Nat := 118140960795 + 3184003 * 2 ^ 59
def prefixEnd_3184003 : Nat := 4983230072969 + 3 ^ 40 * 3184003 * 2
def baseEnd_3184003 : Nat := 1634923944357611307319543

theorem tailTrace_3184003 : CollatzResearch.WordTrace tailWord_3184003 prefixEnd_3184003 1634923944357611307319543 := by
  unfold tailWord_3184003
  simp only [CollatzResearch.WordTrace]
  refine ⟨116130129883908390264620663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77420086589272260176413775 116130129883908390264620663)
  ·
    refine ⟨174195194825862585396930995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116130129883908390264620663 174195194825862585396930995)
    ·
      refine ⟨261292792238793878095396493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174195194825862585396930995 261292792238793878095396493)
      ·
        refine ⟨97984797089547704285773685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261292792238793878095396493 97984797089547704285773685)
        ·
          refine ⟨9186074727145097276791283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97984797089547704285773685 9186074727145097276791283)
          ·
            refine ⟨13779112090717645915186925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186074727145097276791283 13779112090717645915186925)
            ·
              refine ⟨5167167034019117218195097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13779112090717645915186925 5167167034019117218195097)
              ·
                refine ⟨3875375275514337913646323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167167034019117218195097 3875375275514337913646323)
                ·
                  refine ⟨5813062913271506870469485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875375275514337913646323 5813062913271506870469485)
                  ·
                    refine ⟨2179898592476815076426057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5813062913271506870469485 2179898592476815076426057)
                    ·
                      refine ⟨1634923944357611307319543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179898592476815076426057 1634923944357611307319543)
                      ·
                        rfl

theorem cell23_3184003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_3184003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184003 prefixEnd_3184003 := by exact prefixLift 3184003
  have htrace : WordTrace (prefixWord ++ tailWord_3184003) baseStart_3184003 baseEnd_3184003 := by
    simpa [prefixWord, tailWord_3184003, baseEnd_3184003] using wordTrace_append hprefix tailTrace_3184003
  have hstable : (prefixWord ++ tailWord_3184003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184003).length < 2 ^ (prefixWord ++ tailWord_3184003).sum := by decide
  have hdescent : baseEnd_3184003 < baseStart_3184003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184039 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 7]
def baseStart_3184039 : Nat := 118140960795 + 3184039 * 2 ^ 59
def prefixEnd_3184039 : Nat := 4983230072969 + 3 ^ 40 * 3184039 * 2
def baseEnd_3184039 : Nat := 181660269962352574052153

theorem tailTrace_3184039 : CollatzResearch.WordTrace tailWord_3184039 prefixEnd_3184039 181660269962352574052153 := by
  unfold tailWord_3184039
  simp only [CollatzResearch.WordTrace]
  refine ⟨116131442911777968412931171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77420961941185312275287447 116131442911777968412931171)
  ·
    refine ⟨174197164367666952619396757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116131442911777968412931171 174197164367666952619396757)
    ·
      refine ⟨8165492079734388404034223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174197164367666952619396757 8165492079734388404034223)
      ·
        refine ⟨12248238119601582606051335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8165492079734388404034223 12248238119601582606051335)
        ·
          refine ⟨18372357179402373909077003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12248238119601582606051335 18372357179402373909077003)
          ·
            refine ⟨27558535769103560863615505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18372357179402373909077003 27558535769103560863615505)
            ·
              refine ⟨20668901826827670647711629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27558535769103560863615505 20668901826827670647711629)
              ·
                refine ⟨7750838185060376492891861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20668901826827670647711629 7750838185060376492891861)
                ·
                  refine ⟨181660269962352574052153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7750838185060376492891861 181660269962352574052153)
                  ·
                    rfl

theorem cell23_3184039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 7].length) (baseStart_3184039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184039 prefixEnd_3184039 := by exact prefixLift 3184039
  have htrace : WordTrace (prefixWord ++ tailWord_3184039) baseStart_3184039 baseEnd_3184039 := by
    simpa [prefixWord, tailWord_3184039, baseEnd_3184039] using wordTrace_append hprefix tailTrace_3184039
  have hstable : (prefixWord ++ tailWord_3184039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184039).length < 2 ^ (prefixWord ++ tailWord_3184039).sum := by decide
  have hdescent : baseEnd_3184039 < baseStart_3184039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184084 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3184084 : Nat := 118140960795 + 3184084 * 2 ^ 59
def prefixEnd_3184084 : Nat := 4983230072969 + 3 ^ 40 * 3184084 * 2
def baseEnd_3184084 : Nat := 1634965536290625490406671

theorem tailTrace_3184084 : CollatzResearch.WordTrace tailWord_3184084 prefixEnd_3184084 1634965536290625490406671 := by
  unfold tailWord_3184084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58066542098307470549159653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77422056131076627398879537 58066542098307470549159653)
  ·
    refine ⟨10887476643432650727967435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58066542098307470549159653 10887476643432650727967435)
    ·
      refine ⟨16331214965148976091951153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10887476643432650727967435 16331214965148976091951153)
      ·
        refine ⟨12248411223861732068963365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16331214965148976091951153 12248411223861732068963365)
        ·
          refine ⟨2296577104474074762930631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12248411223861732068963365 2296577104474074762930631)
          ·
            refine ⟨3444865656711112144395947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296577104474074762930631 3444865656711112144395947)
            ·
              refine ⟨5167298485066668216593921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444865656711112144395947 5167298485066668216593921)
              ·
                refine ⟨3875473863800001162445441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5167298485066668216593921 3875473863800001162445441)
                ·
                  refine ⟨2906605397850000871834081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875473863800001162445441 2906605397850000871834081)
                  ·
                    refine ⟨2179954048387500653875561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2906605397850000871834081 2179954048387500653875561)
                    ·
                      refine ⟨1634965536290625490406671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2179954048387500653875561 1634965536290625490406671)
                      ·
                        rfl

theorem cell23_3184084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3184084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184084 prefixEnd_3184084 := by exact prefixLift 3184084
  have htrace : WordTrace (prefixWord ++ tailWord_3184084) baseStart_3184084 baseEnd_3184084 := by
    simpa [prefixWord, tailWord_3184084, baseEnd_3184084] using wordTrace_append hprefix tailTrace_3184084
  have hstable : (prefixWord ++ tailWord_3184084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184084).length < 2 ^ (prefixWord ++ tailWord_3184084).sum := by decide
  have hdescent : baseEnd_3184084 < baseStart_3184084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184183 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 2, 3, 2]
def baseStart_3184183 : Nat := 118140960795 + 3184183 * 2 ^ 59
def prefixEnd_3184183 : Nat := 4983230072969 + 3 ^ 40 * 3184183 * 2
def baseEnd_3184183 : Nat := 1635016370875420603068715

theorem tailTrace_3184183 : CollatzResearch.WordTrace tailWord_3184183 prefixEnd_3184183 1635016370875420603068715 := by
  unfold tailWord_3184183
  simp only [CollatzResearch.WordTrace]
  refine ⟨116136695023256281006173203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77424463348837520670782135 116136695023256281006173203)
  ·
    refine ⟨174205042534884421509259805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116136695023256281006173203 174205042534884421509259805)
    ·
      refine ⟨65326890950581658065972427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174205042534884421509259805 65326890950581658065972427)
      ·
        refine ⟨97990336425872487098958641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65326890950581658065972427 97990336425872487098958641)
        ·
          refine ⟨73492752319404365324218981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97990336425872487098958641 73492752319404365324218981)
          ·
            refine ⟨13779891059888318498291059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73492752319404365324218981 13779891059888318498291059)
            ·
              refine ⟨20669836589832477747436589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13779891059888318498291059 20669836589832477747436589)
              ·
                refine ⟨7751188721187179155288721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20669836589832477747436589 7751188721187179155288721)
                ·
                  refine ⟨5813391540890384366466541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751188721187179155288721 5813391540890384366466541)
                  ·
                    refine ⟨2180021827833894137424953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5813391540890384366466541 2180021827833894137424953)
                    ·
                      refine ⟨1635016370875420603068715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180021827833894137424953 1635016370875420603068715)
                      ·
                        rfl

theorem cell23_3184183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3, 2].length) (baseStart_3184183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184183 prefixEnd_3184183 := by exact prefixLift 3184183
  have htrace : WordTrace (prefixWord ++ tailWord_3184183) baseStart_3184183 baseEnd_3184183 := by
    simpa [prefixWord, tailWord_3184183, baseEnd_3184183] using wordTrace_append hprefix tailTrace_3184183
  have hstable : (prefixWord ++ tailWord_3184183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184183).length < 2 ^ (prefixWord ++ tailWord_3184183).sum := by decide
  have hdescent : baseEnd_3184183 < baseStart_3184183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184264 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3184264 : Nat := 118140960795 + 3184264 * 2 ^ 59
def prefixEnd_3184264 : Nat := 4983230072969 + 3 ^ 40 * 3184264 * 2
def baseEnd_3184264 : Nat := 1635057962808434786155843

theorem tailTrace_3184264 : CollatzResearch.WordTrace tailWord_3184264 prefixEnd_3184264 1635057962808434786155843 := by
  unfold tailWord_3184264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58069824667981415919935923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77426432890641887893247897 58069824667981415919935923)
  ·
    refine ⟨87104737001972123879903885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58069824667981415919935923 87104737001972123879903885)
    ·
      refine ⟨32664276375739546454963957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87104737001972123879903885 32664276375739546454963957)
      ·
        refine ⟨3062275910225582480152871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32664276375739546454963957 3062275910225582480152871)
        ·
          refine ⟨4593413865338373720229307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062275910225582480152871 4593413865338373720229307)
          ·
            refine ⟨6890120798007560580343961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593413865338373720229307 6890120798007560580343961)
            ·
              refine ⟨5167590598505670435257971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890120798007560580343961 5167590598505670435257971)
              ·
                refine ⟨7751385897758505652886957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167590598505670435257971 7751385897758505652886957)
                ·
                  refine ⟨2906769711659439619832609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7751385897758505652886957 2906769711659439619832609)
                  ·
                    refine ⟨2180077283744579714874457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2906769711659439619832609 2180077283744579714874457)
                    ·
                      refine ⟨1635057962808434786155843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180077283744579714874457 1635057962808434786155843)
                      ·
                        rfl

theorem cell23_3184264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3184264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184264 prefixEnd_3184264 := by exact prefixLift 3184264
  have htrace : WordTrace (prefixWord ++ tailWord_3184264) baseStart_3184264 baseEnd_3184264 := by
    simpa [prefixWord, tailWord_3184264, baseEnd_3184264] using wordTrace_append hprefix tailTrace_3184264
  have hstable : (prefixWord ++ tailWord_3184264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184264).length < 2 ^ (prefixWord ++ tailWord_3184264).sum := by decide
  have hdescent : baseEnd_3184264 < baseStart_3184264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_3184273 : Nat := 118140960795 + 3184273 * 2 ^ 59
def prefixEnd_3184273 : Nat := 4983230072969 + 3 ^ 40 * 3184273 * 2
def baseEnd_3184273 : Nat := 1635062584134325250943301

theorem tailTrace_3184273 : CollatzResearch.WordTrace tailWord_3184273 prefixEnd_3184273 1635062584134325250943301 := by
  unfold tailWord_3184273
  simp only [CollatzResearch.WordTrace]
  refine ⟨116139977592930226376949473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77426651728620150917966315 116139977592930226376949473)
  ·
    refine ⟨87104983194697669782712105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116139977592930226376949473 87104983194697669782712105)
    ·
      refine ⟨65328737396023252337034079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87104983194697669782712105 65328737396023252337034079)
      ·
        refine ⟨97993106094034878505551119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65328737396023252337034079 97993106094034878505551119)
        ·
          refine ⟨146989659141052317758326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97993106094034878505551119 146989659141052317758326679)
          ·
            refine ⟨220484488711578476637490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146989659141052317758326679 220484488711578476637490019)
            ·
              refine ⟨330726733067367714956235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220484488711578476637490019 330726733067367714956235029)
              ·
                refine ⟨15502815612532861638573517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 330726733067367714956235029 15502815612532861638573517)
                ·
                  refine ⟨5813555854699823114465069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15502815612532861638573517 5813555854699823114465069)
                  ·
                    refine ⟨2180083445512433667924401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5813555854699823114465069 2180083445512433667924401)
                    ·
                      refine ⟨1635062584134325250943301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180083445512433667924401 1635062584134325250943301)
                      ·
                        rfl

theorem cell23_3184273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_3184273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184273 prefixEnd_3184273 := by exact prefixLift 3184273
  have htrace : WordTrace (prefixWord ++ tailWord_3184273) baseStart_3184273 baseEnd_3184273 := by
    simpa [prefixWord, tailWord_3184273, baseEnd_3184273] using wordTrace_append hprefix tailTrace_3184273
  have hstable : (prefixWord ++ tailWord_3184273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184273).length < 2 ^ (prefixWord ++ tailWord_3184273).sum := by decide
  have hdescent : baseEnd_3184273 < baseStart_3184273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184280 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3184280 : Nat := 118140960795 + 3184280 * 2 ^ 59
def prefixEnd_3184280 : Nat := 4983230072969 + 3 ^ 40 * 3184280 * 2
def baseEnd_3184280 : Nat := 1635066178498906723555769

theorem tailTrace_3184280 : CollatzResearch.WordTrace tailWord_3184280 prefixEnd_3184280 1635066178498906723555769 := by
  unfold tailWord_3184280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070116451952433286227147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77426821935936577714969529 58070116451952433286227147)
  ·
    refine ⟨87105174677928649929340721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58070116451952433286227147 87105174677928649929340721)
    ·
      refine ⟨65328881008446487447005541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87105174677928649929340721 65328881008446487447005541)
      ·
        refine ⟨12249165189083716396313539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65328881008446487447005541 12249165189083716396313539)
        ·
          refine ⟨18373747783625574594470309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249165189083716396313539 18373747783625574594470309)
          ·
            refine ⟨3445077709429795236463183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18373747783625574594470309 3445077709429795236463183)
            ·
              refine ⟨5167616564144692854694775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445077709429795236463183 5167616564144692854694775)
              ·
                refine ⟨7751424846217039282042163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167616564144692854694775 7751424846217039282042163)
                ·
                  refine ⟨11627137269325558923063245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7751424846217039282042163 11627137269325558923063245)
                  ·
                    refine ⟨4360176475997084596148717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11627137269325558923063245 4360176475997084596148717)
                    ·
                      refine ⟨1635066178498906723555769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360176475997084596148717 1635066178498906723555769)
                      ·
                        rfl

theorem cell23_3184280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3184280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184280 prefixEnd_3184280 := by exact prefixLift 3184280
  have htrace : WordTrace (prefixWord ++ tailWord_3184280) baseStart_3184280 baseEnd_3184280 := by
    simpa [prefixWord, tailWord_3184280, baseEnd_3184280] using wordTrace_append hprefix tailTrace_3184280
  have hstable : (prefixWord ++ tailWord_3184280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184280).length < 2 ^ (prefixWord ++ tailWord_3184280).sum := by decide
  have hdescent : baseEnd_3184280 < baseStart_3184280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184287 : List Nat := [1, 1, 2, 7, 2, 1, 2, 7]
def baseStart_3184287 : Nat := 118140960795 + 3184287 * 2 ^ 59
def prefixEnd_3184287 : Nat := 4983230072969 + 3 ^ 40 * 3184287 * 2
def baseEnd_3184287 : Nat := 60558139735684748006231

theorem tailTrace_3184287 : CollatzResearch.WordTrace tailWord_3184287 prefixEnd_3184287 60558139735684748006231 := by
  unfold tailWord_3184287
  simp only [CollatzResearch.WordTrace]
  refine ⟨116140488214879506767959115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77426992143253004511972743 116140488214879506767959115)
  ·
    refine ⟨174210732322319260151938673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116140488214879506767959115 174210732322319260151938673)
    ·
      refine ⟨130658049241739445113954005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174210732322319260151938673 130658049241739445113954005)
      ·
        refine ⟨3062298029103268244858297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 130658049241739445113954005 3062298029103268244858297)
        ·
          refine ⟨2296723521827451183643723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062298029103268244858297 2296723521827451183643723)
          ·
            refine ⟨3445085282741176775465585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296723521827451183643723 3445085282741176775465585)
            ·
              refine ⟨2583813962055882581599189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445085282741176775465585 2583813962055882581599189)
              ·
                refine ⟨60558139735684748006231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2583813962055882581599189 60558139735684748006231)
                ·
                  rfl

theorem cell23_3184287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 7].length) (baseStart_3184287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184287 prefixEnd_3184287 := by exact prefixLift 3184287
  have htrace : WordTrace (prefixWord ++ tailWord_3184287) baseStart_3184287 baseEnd_3184287 := by
    simpa [prefixWord, tailWord_3184287, baseEnd_3184287] using wordTrace_append hprefix tailTrace_3184287
  have hstable : (prefixWord ++ tailWord_3184287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184287).length < 2 ^ (prefixWord ++ tailWord_3184287).sum := by decide
  have hdescent : baseEnd_3184287 < baseStart_3184287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184303 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 4, 2]
def baseStart_3184303 : Nat := 118140960795 + 3184303 * 2 ^ 59
def prefixEnd_3184303 : Nat := 4983230072969 + 3 ^ 40 * 3184303 * 2
def baseEnd_3184303 : Nat := 1635077988553960133568163

theorem tailTrace_3184303 : CollatzResearch.WordTrace tailWord_3184303 prefixEnd_3184303 1635077988553960133568163 := by
  unfold tailWord_3184303
  simp only [CollatzResearch.WordTrace]
  refine ⟨116141071782821541500541563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77427381188547694333694375 116141071782821541500541563)
  ·
    refine ⟨174211607674232312250812345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116141071782821541500541563 174211607674232312250812345)
    ·
      refine ⟨130658705755674234188109259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174211607674232312250812345 130658705755674234188109259)
      ·
        refine ⟨195988058633511351282163889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130658705755674234188109259 195988058633511351282163889)
        ·
          refine ⟨146991043975133513461622917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195988058633511351282163889 146991043975133513461622917)
          ·
            refine ⟨27560820745337533774054297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146991043975133513461622917 27560820745337533774054297)
            ·
              refine ⟨20670615559003150330540723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27560820745337533774054297 20670615559003150330540723)
              ·
                refine ⟨31005923338504725495811085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20670615559003150330540723 31005923338504725495811085)
                ·
                  refine ⟨11627221251939272060929157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31005923338504725495811085 11627221251939272060929157)
                  ·
                    refine ⟨2180103984738613511424217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11627221251939272060929157 2180103984738613511424217)
                    ·
                      refine ⟨1635077988553960133568163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180103984738613511424217 1635077988553960133568163)
                      ·
                        rfl

theorem cell23_3184303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4, 2].length) (baseStart_3184303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184303 prefixEnd_3184303 := by exact prefixLift 3184303
  have htrace : WordTrace (prefixWord ++ tailWord_3184303) baseStart_3184303 baseEnd_3184303 := by
    simpa [prefixWord, tailWord_3184303, baseEnd_3184303] using wordTrace_append hprefix tailTrace_3184303
  have hstable : (prefixWord ++ tailWord_3184303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184303).length < 2 ^ (prefixWord ++ tailWord_3184303).sum := by decide
  have hdescent : baseEnd_3184303 < baseStart_3184303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184306 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3184306 : Nat := 118140960795 + 3184306 * 2 ^ 59
def prefixEnd_3184306 : Nat := 4983230072969 + 3 ^ 40 * 3184306 * 2
def baseEnd_3184306 : Nat := 1635079528995923621830649

theorem tailTrace_3184306 : CollatzResearch.WordTrace tailWord_3184306 prefixEnd_3184306 1635079528995923621830649 := by
  unfold tailWord_3184306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29035295300452668253225193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77427454134540448675267181 29035295300452668253225193)
  ·
    refine ⟨21776471475339501189918895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29035295300452668253225193 21776471475339501189918895)
    ·
      refine ⟨32664707213009251784878343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21776471475339501189918895 32664707213009251784878343)
      ·
        refine ⟨48997060819513877677317515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32664707213009251784878343 48997060819513877677317515)
        ·
          refine ⟨73495591229270816515976273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48997060819513877677317515 73495591229270816515976273)
          ·
            refine ⟨55121693421953112386982205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73495591229270816515976273 55121693421953112386982205)
            ·
              refine ⟨20670635033232417145118327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55121693421953112386982205 20670635033232417145118327)
              ·
                refine ⟨31005952549848625717677491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20670635033232417145118327 31005952549848625717677491)
                ·
                  refine ⟨46508928824772938576516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31005952549848625717677491 46508928824772938576516237)
                  ·
                    refine ⟨17440848309289851966193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46508928824772938576516237 17440848309289851966193589)
                    ·
                      refine ⟨1635079528995923621830649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17440848309289851966193589 1635079528995923621830649)
                      ·
                        rfl

theorem cell23_3184306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3184306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184306 prefixEnd_3184306 := by exact prefixLift 3184306
  have htrace : WordTrace (prefixWord ++ tailWord_3184306) baseStart_3184306 baseEnd_3184306 := by
    simpa [prefixWord, tailWord_3184306, baseEnd_3184306] using wordTrace_append hprefix tailTrace_3184306
  have hstable : (prefixWord ++ tailWord_3184306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184306).length < 2 ^ (prefixWord ++ tailWord_3184306).sum := by decide
  have hdescent : baseEnd_3184306 < baseStart_3184306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184320 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2]
def baseStart_3184320 : Nat := 118140960795 + 3184320 * 2 ^ 59
def prefixEnd_3184320 : Nat := 4983230072969 + 3 ^ 40 * 3184320 * 2
def baseEnd_3184320 : Nat := 1635086717725086567055585

theorem tailTrace_3184320 : CollatzResearch.WordTrace tailWord_3184320 prefixEnd_3184320 1635086717725086567055585 := by
  unfold tailWord_3184320
  simp only [CollatzResearch.WordTrace]
  refine ⟨58070845911879976701955207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77427794549173302269273609 58070845911879976701955207)
  ·
    refine ⟨87106268867819965052932811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58070845911879976701955207 87106268867819965052932811)
    ·
      refine ⟨130659403301729947579399217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87106268867819965052932811 130659403301729947579399217)
      ·
        refine ⟨97994552476297460684549413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130659403301729947579399217 97994552476297460684549413)
        ·
          refine ⟨18373978589305773878353015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97994552476297460684549413 18373978589305773878353015)
          ·
            refine ⟨27560967883958660817529523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18373978589305773878353015 27560967883958660817529523)
            ·
              refine ⟨41341451825937991226294285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27560967883958660817529523 41341451825937991226294285)
              ·
                refine ⟨15503044434726746709860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41341451825937991226294285 15503044434726746709860357)
                ·
                  refine ⟨2906820831511265008098817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15503044434726746709860357 2906820831511265008098817)
                  ·
                    refine ⟨2180115623633448756074113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2906820831511265008098817 2180115623633448756074113)
                    ·
                      refine ⟨1635086717725086567055585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180115623633448756074113 1635086717725086567055585)
                      ·
                        rfl

theorem cell23_3184320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_3184320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184320 prefixEnd_3184320 := by exact prefixLift 3184320
  have htrace : WordTrace (prefixWord ++ tailWord_3184320) baseStart_3184320 baseEnd_3184320 := by
    simpa [prefixWord, tailWord_3184320, baseEnd_3184320] using wordTrace_append hprefix tailTrace_3184320
  have hstable : (prefixWord ++ tailWord_3184320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184320).length < 2 ^ (prefixWord ++ tailWord_3184320).sum := by decide
  have hdescent : baseEnd_3184320 < baseStart_3184320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184337 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_3184337 : Nat := 118140960795 + 3184337 * 2 ^ 59
def prefixEnd_3184337 : Nat := 4983230072969 + 3 ^ 40 * 3184337 * 2
def baseEnd_3184337 : Nat := 1635095446896213000543007

theorem tailTrace_3184337 : CollatzResearch.WordTrace tailWord_3184337 prefixEnd_3184337 1635095446896213000543007 := by
  unfold tailWord_3184337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116142311864698365307279265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77428207909798910204852843 116142311864698365307279265)
  ·
    refine ⟨87106733898523773980459449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116142311864698365307279265 87106733898523773980459449)
    ·
      refine ⟨65330050423892830485344587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87106733898523773980459449 65330050423892830485344587)
      ·
        refine ⟨97995075635839245728016881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65330050423892830485344587 97995075635839245728016881)
        ·
          refine ⟨73496306726879434296012661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97995075635839245728016881 73496306726879434296012661)
          ·
            refine ⟨6890278755644946965251187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73496306726879434296012661 6890278755644946965251187)
            ·
              refine ⟨10335418133467420447876781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890278755644946965251187 10335418133467420447876781)
              ·
                refine ⟨3875781800050282667953793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10335418133467420447876781 3875781800050282667953793)
                ·
                  refine ⟨2906836350037712000965345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3875781800050282667953793 2906836350037712000965345)
                  ·
                    refine ⟨2180127262528284000724009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2906836350037712000965345 2180127262528284000724009)
                    ·
                      refine ⟨1635095446896213000543007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180127262528284000724009 1635095446896213000543007)
                      ·
                        rfl

theorem cell23_3184337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_3184337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184337 prefixEnd_3184337 := by exact prefixLift 3184337
  have htrace : WordTrace (prefixWord ++ tailWord_3184337) baseStart_3184337 baseEnd_3184337 := by
    simpa [prefixWord, tailWord_3184337, baseEnd_3184337] using wordTrace_append hprefix tailTrace_3184337
  have hstable : (prefixWord ++ tailWord_3184337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184337).length < 2 ^ (prefixWord ++ tailWord_3184337).sum := by decide
  have hdescent : baseEnd_3184337 < baseStart_3184337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184410 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3184410 : Nat := 118140960795 + 3184410 * 2 ^ 59
def prefixEnd_3184410 : Nat := 4983230072969 + 3 ^ 40 * 3184410 * 2
def baseEnd_3184410 : Nat := 1635132930983991214930171

theorem tailTrace_3184410 : CollatzResearch.WordTrace tailWord_3184410 prefixEnd_3184410 1635132930983991214930171 := by
  unfold tailWord_3184410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29036243598358474693671671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77429982928955932516457789 29036243598358474693671671)
  ·
    refine ⟨43554365397537712040507507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29036243598358474693671671 43554365397537712040507507)
    ·
      refine ⟨65331548096306568060761261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43554365397537712040507507 65331548096306568060761261)
      ·
        refine ⟨24499330536114963022785473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65331548096306568060761261 24499330536114963022785473)
        ·
          refine ⟨18374497902086222267089105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24499330536114963022785473 18374497902086222267089105)
          ·
            refine ⟨13780873426564666700316829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18374497902086222267089105 13780873426564666700316829)
            ·
              refine ⟨5167827534961750012618811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13780873426564666700316829 5167827534961750012618811)
              ·
                refine ⟨7751741302442625018928217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167827534961750012618811 7751741302442625018928217)
                ·
                  refine ⟨5813805976831968764196163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751741302442625018928217 5813805976831968764196163)
                  ·
                    refine ⟨8720708965247953146294245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5813805976831968764196163 8720708965247953146294245)
                    ·
                      refine ⟨1635132930983991214930171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8720708965247953146294245 1635132930983991214930171)
                      ·
                        rfl

theorem cell23_3184410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3184410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184410 prefixEnd_3184410 := by exact prefixLift 3184410
  have htrace : WordTrace (prefixWord ++ tailWord_3184410) baseStart_3184410 baseEnd_3184410 := by
    simpa [prefixWord, tailWord_3184410, baseEnd_3184410] using wordTrace_append hprefix tailTrace_3184410
  have hstable : (prefixWord ++ tailWord_3184410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184410).length < 2 ^ (prefixWord ++ tailWord_3184410).sum := by decide
  have hdescent : baseEnd_3184410 < baseStart_3184410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184433 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 8]
def baseStart_3184433 : Nat := 118140960795 + 3184433 * 2 ^ 59
def prefixEnd_3184433 : Nat := 4983230072969 + 3 ^ 40 * 3184433 * 2
def baseEnd_3184433 : Nat := 181682749004338291660285

theorem tailTrace_3184433 : CollatzResearch.WordTrace tailWord_3184433 prefixEnd_3184433 181682749004338291660285 := by
  unfold tailWord_3184433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116145813272350573702773953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77430542181567049135182635 116145813272350573702773953)
  ·
    refine ⟨87109359954262930277080465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116145813272350573702773953 87109359954262930277080465)
    ·
      refine ⟨65332019965697197707810349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87109359954262930277080465 65332019965697197707810349)
      ·
        refine ⟨24499507487136449140428881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65332019965697197707810349 24499507487136449140428881)
        ·
          refine ⟨18374630615352336855321661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24499507487136449140428881 18374630615352336855321661)
          ·
            refine ⟨6890486480757126320745623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18374630615352336855321661 6890486480757126320745623)
            ·
              refine ⟨10335729721135689481118435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890486480757126320745623 10335729721135689481118435)
              ·
                refine ⟨15503594581703534221677653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10335729721135689481118435 15503594581703534221677653)
                ·
                  refine ⟨181682749004338291660285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15503594581703534221677653 181682749004338291660285)
                  ·
                    rfl

theorem cell23_3184433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_3184433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184433 prefixEnd_3184433 := by exact prefixLift 3184433
  have htrace : WordTrace (prefixWord ++ tailWord_3184433) baseStart_3184433 baseEnd_3184433 := by
    simpa [prefixWord, tailWord_3184433, baseEnd_3184433] using wordTrace_append hprefix tailTrace_3184433
  have hstable : (prefixWord ++ tailWord_3184433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184433).length < 2 ^ (prefixWord ++ tailWord_3184433).sum := by decide
  have hdescent : baseEnd_3184433 < baseStart_3184433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184437 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3184437 : Nat := 118140960795 + 3184437 * 2 ^ 59
def prefixEnd_3184437 : Nat := 4983230072969 + 3 ^ 40 * 3184437 * 2
def baseEnd_3184437 : Nat := 545048931653887536430849

theorem tailTrace_3184437 : CollatzResearch.WordTrace tailWord_3184437 prefixEnd_3184437 545048931653887536430849 := by
  unfold tailWord_3184437
  simp only [CollatzResearch.WordTrace]
  refine ⟨116145959164336082385919565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77430639442890721590613043 116145959164336082385919565)
  ·
    refine ⟨43554734686626030894719837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116145959164336082385919565 43554734686626030894719837)
    ·
      refine ⟨16333025507484761585519939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43554734686626030894719837 16333025507484761585519939)
      ·
        refine ⟨24499538261227142378279909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16333025507484761585519939 24499538261227142378279909)
        ·
          refine ⟨4593663423980089195927483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24499538261227142378279909 4593663423980089195927483)
          ·
            refine ⟨6890495135970133793891225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593663423980089195927483 6890495135970133793891225)
            ·
              refine ⟨5167871351977600345418419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6890495135970133793891225 5167871351977600345418419)
              ·
                refine ⟨7751807027966400518127629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167871351977600345418419 7751807027966400518127629)
                ·
                  refine ⟨2906927635487400194297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7751807027966400518127629 2906927635487400194297861)
                  ·
                    refine ⟨545048931653887536430849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906927635487400194297861 545048931653887536430849)
                    ·
                      rfl

theorem cell23_3184437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3184437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184437 prefixEnd_3184437 := by exact prefixLift 3184437
  have htrace : WordTrace (prefixWord ++ tailWord_3184437) baseStart_3184437 baseEnd_3184437 := by
    simpa [prefixWord, tailWord_3184437, baseEnd_3184437] using wordTrace_append hprefix tailTrace_3184437
  have hstable : (prefixWord ++ tailWord_3184437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184437).length < 2 ^ (prefixWord ++ tailWord_3184437).sum := by decide
  have hdescent : baseEnd_3184437 < baseStart_3184437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184454 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3184454 : Nat := 118140960795 + 3184454 * 2 ^ 59
def prefixEnd_3184454 : Nat := 4983230072969 + 3 ^ 40 * 3184454 * 2
def baseEnd_3184454 : Nat := 545051841377596347593323

theorem tailTrace_3184454 : CollatzResearch.WordTrace tailWord_3184454 prefixEnd_3184454 545051841377596347593323 := by
  unfold tailWord_3184454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629580600164827946540263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77431052803516329526192277 3629580600164827946540263)
  ·
    refine ⟨5444370900247241919810395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629580600164827946540263 5444370900247241919810395)
    ·
      refine ⟨8166556350370862879715593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444370900247241919810395 8166556350370862879715593)
      ·
        refine ⟨6124917262778147159786695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8166556350370862879715593 6124917262778147159786695)
        ·
          refine ⟨9187375894167220739680043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124917262778147159786695 9187375894167220739680043)
          ·
            refine ⟨13781063841250831109520065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187375894167220739680043 13781063841250831109520065)
            ·
              refine ⟨10335797880938123332140049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13781063841250831109520065 10335797880938123332140049)
              ·
                refine ⟨7751848410703592499105037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335797880938123332140049 7751848410703592499105037)
                ·
                  refine ⟨2906943154013847187164389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7751848410703592499105037 2906943154013847187164389)
                  ·
                    refine ⟨545051841377596347593323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906943154013847187164389 545051841377596347593323)
                    ·
                      rfl

theorem cell23_3184454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3184454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184454 prefixEnd_3184454 := by exact prefixLift 3184454
  have htrace : WordTrace (prefixWord ++ tailWord_3184454) baseStart_3184454 baseEnd_3184454 := by
    simpa [prefixWord, tailWord_3184454, baseEnd_3184454] using wordTrace_append hprefix tailTrace_3184454
  have hstable : (prefixWord ++ tailWord_3184454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184454).length < 2 ^ (prefixWord ++ tailWord_3184454).sum := by decide
  have hdescent : baseEnd_3184454 < baseStart_3184454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184471 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 1, 4]
def baseStart_3184471 : Nat := 118140960795 + 3184471 * 2 ^ 59
def prefixEnd_3184471 : Nat := 4983230072969 + 3 ^ 40 * 3184471 * 2
def baseEnd_3184471 : Nat := 545054751101305158755797

theorem tailTrace_3184471 : CollatzResearch.WordTrace tailWord_3184471 prefixEnd_3184471 545054751101305158755797 := by
  unfold tailWord_3184471
  simp only [CollatzResearch.WordTrace]
  refine ⟨116147199246212906192657267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77431466164141937461771511 116147199246212906192657267)
  ·
    refine ⟨174220798869319359288985901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116147199246212906192657267 174220798869319359288985901)
    ·
      refine ⟨65332799575994759733369713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174220798869319359288985901 65332799575994759733369713)
      ·
        refine ⟨48999599681996069800027285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65332799575994759733369713 48999599681996069800027285)
        ·
          refine ⟨2296856235093565771876279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48999599681996069800027285 2296856235093565771876279)
          ·
            refine ⟨3445284352640348657814419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296856235093565771876279 3445284352640348657814419)
            ·
              refine ⟨5167926528960522986721629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445284352640348657814419 5167926528960522986721629)
              ·
                refine ⟨1937972448360196120020611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5167926528960522986721629 1937972448360196120020611)
                ·
                  refine ⟨2906958672540294180030917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937972448360196120020611 2906958672540294180030917)
                  ·
                    refine ⟨545054751101305158755797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2906958672540294180030917 545054751101305158755797)
                    ·
                      rfl

theorem cell23_3184471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 4].length) (baseStart_3184471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184471 prefixEnd_3184471 := by exact prefixLift 3184471
  have htrace : WordTrace (prefixWord ++ tailWord_3184471) baseStart_3184471 baseEnd_3184471 := by
    simpa [prefixWord, tailWord_3184471, baseEnd_3184471] using wordTrace_append hprefix tailTrace_3184471
  have hstable : (prefixWord ++ tailWord_3184471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184471).length < 2 ^ (prefixWord ++ tailWord_3184471).sum := by decide
  have hdescent : baseEnd_3184471 < baseStart_3184471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184480 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_3184480 : Nat := 118140960795 + 3184480 * 2 ^ 59
def prefixEnd_3184480 : Nat := 4983230072969 + 3 ^ 40 * 3184480 * 2
def baseEnd_3184480 : Nat := 545056291543268647018283

theorem tailTrace_3184480 : CollatzResearch.WordTrace tailWord_3184480 prefixEnd_3184480 545056291543268647018283 := by
  unfold tailWord_3184480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58073763751590150364867447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77431685002120200486489929 58073763751590150364867447)
  ·
    refine ⟨87110645627385225547301171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58073763751590150364867447 87110645627385225547301171)
    ·
      refine ⟨130665968441077838320951757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87110645627385225547301171 130665968441077838320951757)
      ·
        refine ⟨48999738165404189370356909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130665968441077838320951757 48999738165404189370356909)
        ·
          refine ⟨18374901812026571013883841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48999738165404189370356909 18374901812026571013883841)
          ·
            refine ⟨13781176359019928260412881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18374901812026571013883841 13781176359019928260412881)
            ·
              refine ⟨10335882269264946195309661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13781176359019928260412881 10335882269264946195309661)
              ·
                refine ⟨3875955850974354823241123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10335882269264946195309661 3875955850974354823241123)
                ·
                  refine ⟨5813933776461532234861685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3875955850974354823241123 5813933776461532234861685)
                  ·
                    refine ⟨545056291543268647018283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5813933776461532234861685 545056291543268647018283)
                    ·
                      rfl

theorem cell23_3184480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_3184480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184480 prefixEnd_3184480 := by exact prefixLift 3184480
  have htrace : WordTrace (prefixWord ++ tailWord_3184480) baseStart_3184480 baseEnd_3184480 := by
    simpa [prefixWord, tailWord_3184480, baseEnd_3184480] using wordTrace_append hprefix tailTrace_3184480
  have hstable : (prefixWord ++ tailWord_3184480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184480).length < 2 ^ (prefixWord ++ tailWord_3184480).sum := by decide
  have hdescent : baseEnd_3184480 < baseStart_3184480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184487 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_3184487 : Nat := 118140960795 + 3184487 * 2 ^ 59
def prefixEnd_3184487 : Nat := 4983230072969 + 3 ^ 40 * 3184487 * 2
def baseEnd_3184487 : Nat := 1635172468994387413667317

theorem tailTrace_3184487 : CollatzResearch.WordTrace tailWord_3184487 prefixEnd_3184487 1635172468994387413667317 := by
  unfold tailWord_3184487
  simp only [CollatzResearch.WordTrace]
  refine ⟨116147782814154940925239715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77431855209436627283493143 116147782814154940925239715)
  ·
    refine ⟨174221674221232411387859573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116147782814154940925239715 174221674221232411387859573)
    ·
      refine ⟨16333281958240538567611835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174221674221232411387859573 16333281958240538567611835)
      ·
        refine ⟨24499922937360807851417753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16333281958240538567611835 24499922937360807851417753)
        ·
          refine ⟨18374942203020605888563315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24499922937360807851417753 18374942203020605888563315)
          ·
            refine ⟨27562413304530908832844973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18374942203020605888563315 27562413304530908832844973)
            ·
              refine ⟨10335904989199090812316865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27562413304530908832844973 10335904989199090812316865)
              ·
                refine ⟨7751928741899318109237649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10335904989199090812316865 7751928741899318109237649)
                ·
                  refine ⟨5813946556424488581928237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751928741899318109237649 5813946556424488581928237)
                  ·
                    refine ⟨2180229958659183218223089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5813946556424488581928237 2180229958659183218223089)
                    ·
                      refine ⟨1635172468994387413667317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180229958659183218223089 1635172468994387413667317)
                      ·
                        rfl

theorem cell23_3184487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_3184487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184487 prefixEnd_3184487 := by exact prefixLift 3184487
  have htrace : WordTrace (prefixWord ++ tailWord_3184487) baseStart_3184487 baseEnd_3184487 := by
    simpa [prefixWord, tailWord_3184487, baseEnd_3184487] using wordTrace_append hprefix tailTrace_3184487
  have hstable : (prefixWord ++ tailWord_3184487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184487).length < 2 ^ (prefixWord ++ tailWord_3184487).sum := by decide
  have hdescent : baseEnd_3184487 < baseStart_3184487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184494 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3184494 : Nat := 118140960795 + 3184494 * 2 ^ 59
def prefixEnd_3184494 : Nat := 4983230072969 + 3 ^ 40 * 3184494 * 2
def baseEnd_3184494 : Nat := 1635176063358968886279785

theorem tailTrace_3184494 : CollatzResearch.WordTrace tailWord_3184494 prefixEnd_3184494 1635176063358968886279785 := by
  unfold tailWord_3184494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14518504765641197640093067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77432025416753054080496357 14518504765641197640093067)
  ·
    refine ⟨21777757148461796460139601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14518504765641197640093067 21777757148461796460139601)
    ·
      refine ⟨16333317861346347345104701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21777757148461796460139601 16333317861346347345104701)
      ·
        refine ⟨6124994198004880254414263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16333317861346347345104701 6124994198004880254414263)
        ·
          refine ⟨9187491297007320381621395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6124994198004880254414263 9187491297007320381621395)
          ·
            refine ⟨13781236945510980572432093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187491297007320381621395 13781236945510980572432093)
            ·
              refine ⟨5167963854566617714662035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13781236945510980572432093 5167963854566617714662035)
              ·
                refine ⟨7751945781849926571993053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167963854566617714662035 7751945781849926571993053)
                ·
                  refine ⟨2906979668193722464497395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7751945781849926571993053 2906979668193722464497395)
                  ·
                    refine ⟨4360469502290583696746093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2906979668193722464497395 4360469502290583696746093)
                    ·
                      refine ⟨1635176063358968886279785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360469502290583696746093 1635176063358968886279785)
                      ·
                        rfl

theorem cell23_3184494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3184494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184494 prefixEnd_3184494 := by exact prefixLift 3184494
  have htrace : WordTrace (prefixWord ++ tailWord_3184494) baseStart_3184494 baseEnd_3184494 := by
    simpa [prefixWord, tailWord_3184494, baseEnd_3184494] using wordTrace_append hprefix tailTrace_3184494
  have hstable : (prefixWord ++ tailWord_3184494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184494).length < 2 ^ (prefixWord ++ tailWord_3184494).sum := by decide
  have hdescent : baseEnd_3184494 < baseStart_3184494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184503 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_3184503 : Nat := 118140960795 + 3184503 * 2 ^ 59
def prefixEnd_3184503 : Nat := 4983230072969 + 3 ^ 40 * 3184503 * 2
def baseEnd_3184503 : Nat := 1635180684684859351067243

theorem tailTrace_3184503 : CollatzResearch.WordTrace tailWord_3184503 prefixEnd_3184503 1635180684684859351067243 := by
  unfold tailWord_3184503
  simp only [CollatzResearch.WordTrace]
  refine ⟨116148366382096975657822163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77432244254731317105214775 116148366382096975657822163)
  ·
    refine ⟨174222549573145463486733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116148366382096975657822163 174222549573145463486733245)
    ·
      refine ⟨65333456089929548807524967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174222549573145463486733245 65333456089929548807524967)
      ·
        refine ⟨98000184134894323211287451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65333456089929548807524967 98000184134894323211287451)
        ·
          refine ⟨147000276202341484816931177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98000184134894323211287451 147000276202341484816931177)
          ·
            refine ⟨110250207151756113612698383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147000276202341484816931177 110250207151756113612698383)
            ·
              refine ⟨165375310727634170419047575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110250207151756113612698383 165375310727634170419047575)
              ·
                refine ⟨248062966091451255628571363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165375310727634170419047575 248062966091451255628571363)
                ·
                  refine ⟨372094449137176883442857045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248062966091451255628571363 372094449137176883442857045)
                  ·
                    refine ⟨4360481825826291602845981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 372094449137176883442857045 4360481825826291602845981)
                    ·
                      refine ⟨1635180684684859351067243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360481825826291602845981 1635180684684859351067243)
                      ·
                        rfl

theorem cell23_3184503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_3184503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184503 prefixEnd_3184503 := by exact prefixLift 3184503
  have htrace : WordTrace (prefixWord ++ tailWord_3184503) baseStart_3184503 baseEnd_3184503 := by
    simpa [prefixWord, tailWord_3184503, baseEnd_3184503] using wordTrace_append hprefix tailTrace_3184503
  have hstable : (prefixWord ++ tailWord_3184503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184503).length < 2 ^ (prefixWord ++ tailWord_3184503).sum := by decide
  have hdescent : baseEnd_3184503 < baseStart_3184503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184517 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 5, 2, 2]
def baseStart_3184517 : Nat := 118140960795 + 3184517 * 2 ^ 59
def prefixEnd_3184517 : Nat := 4983230072969 + 3 ^ 40 * 3184517 * 2
def baseEnd_3184517 : Nat := 1635187873414022296292179

theorem tailTrace_3184517 : CollatzResearch.WordTrace tailWord_3184517 prefixEnd_3184517 1635187873414022296292179 := by
  unfold tailWord_3184517
  simp only [CollatzResearch.WordTrace]
  refine ⟨116148877004046256048831805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77432584669364170699221203 116148877004046256048831805)
  ·
    refine ⟨43555828876517346018311927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116148877004046256048831805 43555828876517346018311927)
    ·
      refine ⟨65333743314776019027467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43555828876517346018311927 65333743314776019027467891)
      ·
        refine ⟨98000614972164028541201837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65333743314776019027467891 98000614972164028541201837)
        ·
          refine ⟨36750230614561510702950689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98000614972164028541201837 36750230614561510702950689)
          ·
            refine ⟨27562672960921133027213017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36750230614561510702950689 27562672960921133027213017)
            ·
              refine ⟨20672004720690849770409763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27562672960921133027213017 20672004720690849770409763)
              ·
                refine ⟨31008007081036274655614645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20672004720690849770409763 31008007081036274655614645)
                ·
                  refine ⟨2907000663847150748963873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31008007081036274655614645 2907000663847150748963873)
                  ·
                    refine ⟨2180250497885363061722905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2907000663847150748963873 2180250497885363061722905)
                    ·
                      refine ⟨1635187873414022296292179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180250497885363061722905 1635187873414022296292179)
                      ·
                        rfl

theorem cell23_3184517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_3184517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184517 prefixEnd_3184517 := by exact prefixLift 3184517
  have htrace : WordTrace (prefixWord ++ tailWord_3184517) baseStart_3184517 baseEnd_3184517 := by
    simpa [prefixWord, tailWord_3184517, baseEnd_3184517] using wordTrace_append hprefix tailTrace_3184517
  have hstable : (prefixWord ++ tailWord_3184517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184517).length < 2 ^ (prefixWord ++ tailWord_3184517).sum := by decide
  have hdescent : baseEnd_3184517 < baseStart_3184517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184545 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3184545 : Nat := 118140960795 + 3184545 * 2 ^ 59
def prefixEnd_3184545 : Nat := 4983230072969 + 3 ^ 40 * 3184545 * 2
def baseEnd_3184545 : Nat := 1635202250872348186742051

theorem tailTrace_3184545 : CollatzResearch.WordTrace tailWord_3184545 prefixEnd_3184545 1635202250872348186742051 := by
  unfold tailWord_3184545
  simp only [CollatzResearch.WordTrace]
  refine ⟨116149898247944816830851089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77433265498629877887234059 116149898247944816830851089)
  ·
    refine ⟨87112423685958612623138317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116149898247944816830851089 87112423685958612623138317)
    ·
      refine ⟨32667158882234479733676869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87112423685958612623138317 32667158882234479733676869)
      ·
        refine ⟨6125092290418964950064413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32667158882234479733676869 6125092290418964950064413)
        ·
          refine ⟨2296909608907111856274155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6125092290418964950064413 2296909608907111856274155)
          ·
            refine ⟨3445364413360667784411233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296909608907111856274155 3445364413360667784411233)
            ·
              refine ⟨2584023310020500838308425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445364413360667784411233 2584023310020500838308425)
              ·
                refine ⟨1938017482515375628731319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584023310020500838308425 1938017482515375628731319)
                ·
                  refine ⟨2907026223773063443096979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938017482515375628731319 2907026223773063443096979)
                  ·
                    refine ⟨4360539335659595164645469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907026223773063443096979 4360539335659595164645469)
                    ·
                      refine ⟨1635202250872348186742051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360539335659595164645469 1635202250872348186742051)
                      ·
                        rfl

theorem cell23_3184545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3184545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184545 prefixEnd_3184545 := by exact prefixLift 3184545
  have htrace : WordTrace (prefixWord ++ tailWord_3184545) baseStart_3184545 baseEnd_3184545 := by
    simpa [prefixWord, tailWord_3184545, baseEnd_3184545] using wordTrace_append hprefix tailTrace_3184545
  have hstable : (prefixWord ++ tailWord_3184545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184545).length < 2 ^ (prefixWord ++ tailWord_3184545).sum := by decide
  have hdescent : baseEnd_3184545 < baseStart_3184545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184583 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3184583 : Nat := 118140960795 + 3184583 * 2 ^ 59
def prefixEnd_3184583 : Nat := 4983230072969 + 3 ^ 40 * 3184583 * 2
def baseEnd_3184583 : Nat := 545073921045739679355625

theorem tailTrace_3184583 : CollatzResearch.WordTrace tailWord_3184583 prefixEnd_3184583 545073921045739679355625 := by
  unfold tailWord_3184583
  simp only [CollatzResearch.WordTrace]
  refine ⟨116151284221807149320734403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77434189481204766213822935 116151284221807149320734403)
  ·
    refine ⟨174226926332710723981101605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116151284221807149320734403 174226926332710723981101605)
    ·
      refine ⟨32667548687383260746456551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174226926332710723981101605 32667548687383260746456551)
      ·
        refine ⟨49001323031074891119684827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32667548687383260746456551 49001323031074891119684827)
        ·
          refine ⟨73501984546612336679527241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49001323031074891119684827 73501984546612336679527241)
          ·
            refine ⟨55126488409959252509645431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73501984546612336679527241 55126488409959252509645431)
            ·
              refine ⟨82689732614938878764468147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55126488409959252509645431 82689732614938878764468147)
              ·
                refine ⟨124034598922408318146702221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82689732614938878764468147 124034598922408318146702221)
                ·
                  refine ⟨46512974595903119305013333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124034598922408318146702221 46512974595903119305013333)
                  ·
                    refine ⟨545073921045739679355625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46512974595903119305013333 545073921045739679355625)
                    ·
                      rfl

theorem cell23_3184583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3184583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184583 prefixEnd_3184583 := by exact prefixLift 3184583
  have htrace : WordTrace (prefixWord ++ tailWord_3184583) baseStart_3184583 baseEnd_3184583 := by
    simpa [prefixWord, tailWord_3184583, baseEnd_3184583] using wordTrace_append hprefix tailTrace_3184583
  have hstable : (prefixWord ++ tailWord_3184583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184583).length < 2 ^ (prefixWord ++ tailWord_3184583).sum := by decide
  have hdescent : baseEnd_3184583 < baseStart_3184583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184601 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 3]
def baseStart_3184601 : Nat := 118140960795 + 3184601 * 2 ^ 59
def prefixEnd_3184601 : Nat := 4983230072969 + 3 ^ 40 * 3184601 * 2
def baseEnd_3184601 : Nat := 1635231005788999967641793

theorem tailTrace_3184601 : CollatzResearch.WordTrace tailWord_3184601 prefixEnd_3184601 1635231005788999967641793 := by
  unfold tailWord_3184601
  simp only [CollatzResearch.WordTrace]
  refine ⟨116151940735741938394889657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77434627157161292263259771 116151940735741938394889657)
  ·
    refine ⟨87113955551806453796167243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116151940735741938394889657 87113955551806453796167243)
    ·
      refine ⟨130670933327709680694250865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87113955551806453796167243 130670933327709680694250865)
      ·
        refine ⟨98003199995782260520688149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130670933327709680694250865 98003199995782260520688149)
        ·
          refine ⟨4593899999802293461907257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98003199995782260520688149 4593899999802293461907257)
          ·
            refine ⟨3445424999851720096430443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593899999802293461907257 3445424999851720096430443)
            ·
              refine ⟨5168137499777580144645665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445424999851720096430443 5168137499777580144645665)
              ·
                refine ⟨3876103124833185108484249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5168137499777580144645665 3876103124833185108484249)
                ·
                  refine ⟨2907077343624888831363187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876103124833185108484249 2907077343624888831363187)
                  ·
                    refine ⟨4360616015437333247044781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907077343624888831363187 4360616015437333247044781)
                    ·
                      refine ⟨1635231005788999967641793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360616015437333247044781 1635231005788999967641793)
                      ·
                        rfl

theorem cell23_3184601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_3184601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184601 prefixEnd_3184601 := by exact prefixLift 3184601
  have htrace : WordTrace (prefixWord ++ tailWord_3184601) baseStart_3184601 baseEnd_3184601 := by
    simpa [prefixWord, tailWord_3184601, baseEnd_3184601] using wordTrace_append hprefix tailTrace_3184601
  have hstable : (prefixWord ++ tailWord_3184601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184601).length < 2 ^ (prefixWord ++ tailWord_3184601).sum := by decide
  have hdescent : baseEnd_3184601 < baseStart_3184601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184624 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2]
def baseStart_3184624 : Nat := 118140960795 + 3184624 * 2 ^ 59
def prefixEnd_3184624 : Nat := 4983230072969 + 3 ^ 40 * 3184624 * 2
def baseEnd_3184624 : Nat := 1635242815844053377654187

theorem tailTrace_3184624 : CollatzResearch.WordTrace tailWord_3184624 prefixEnd_3184624 1635242815844053377654187 := by
  unfold tailWord_3184624
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076389807329306661488463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77435186409772408881984617 58076389807329306661488463)
  ·
    refine ⟨87114584710993959992232695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58076389807329306661488463 87114584710993959992232695)
    ·
      refine ⟨130671877066490939988349043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87114584710993959992232695 130671877066490939988349043)
      ·
        refine ⟨196007815599736409982523565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130671877066490939988349043 196007815599736409982523565)
        ·
          refine ⟨73502930849901153743446337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196007815599736409982523565 73502930849901153743446337)
          ·
            refine ⟨55127198137425865307584753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73502930849901153743446337 55127198137425865307584753)
            ·
              refine ⟨41345398603069398980688565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55127198137425865307584753 41345398603069398980688565)
              ·
                refine ⟨3876131119037756154439553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41345398603069398980688565 3876131119037756154439553)
                ·
                  refine ⟨2907098339278317115829665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876131119037756154439553 2907098339278317115829665)
                  ·
                    refine ⟨2180323754458737836872249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2907098339278317115829665 2180323754458737836872249)
                    ·
                      refine ⟨1635242815844053377654187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180323754458737836872249 1635242815844053377654187)
                      ·
                        rfl

theorem cell23_3184624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2].length) (baseStart_3184624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184624 prefixEnd_3184624 := by exact prefixLift 3184624
  have htrace : WordTrace (prefixWord ++ tailWord_3184624) baseStart_3184624 baseEnd_3184624 := by
    simpa [prefixWord, tailWord_3184624, baseEnd_3184624] using wordTrace_append hprefix tailTrace_3184624
  have hstable : (prefixWord ++ tailWord_3184624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184624).length < 2 ^ (prefixWord ++ tailWord_3184624).sum := by decide
  have hdescent : baseEnd_3184624 < baseStart_3184624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_3184640 : Nat := 118140960795 + 3184640 * 2 ^ 59
def prefixEnd_3184640 : Nat := 4983230072969 + 3 ^ 40 * 3184640 * 2
def baseEnd_3184640 : Nat := 1635251031534525315054113

theorem tailTrace_3184640 : CollatzResearch.WordTrace tailWord_3184640 prefixEnd_3184640 1635251031534525315054113 := by
  unfold tailWord_3184640
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076681591300324027779687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77435575455067098703706249 58076681591300324027779687)
  ·
    refine ⟨87115022386950486041669531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58076681591300324027779687 87115022386950486041669531)
    ·
      refine ⟨130672533580425729062504297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87115022386950486041669531 130672533580425729062504297)
      ·
        refine ⟨98004400185319296796878223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130672533580425729062504297 98004400185319296796878223)
        ·
          refine ⟨147006600277978945195317335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98004400185319296796878223 147006600277978945195317335)
          ·
            refine ⟨220509900416968417792976003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147006600277978945195317335 220509900416968417792976003)
            ·
              refine ⟨330764850625452626689464005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220509900416968417792976003 330764850625452626689464005)
              ·
                refine ⟨62018409492272367504274501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330764850625452626689464005 62018409492272367504274501)
                ·
                  refine ⟨11628451779801068907051469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62018409492272367504274501 11628451779801068907051469)
                  ·
                    refine ⟨4360669417425400840144301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11628451779801068907051469 4360669417425400840144301)
                    ·
                      refine ⟨1635251031534525315054113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360669417425400840144301 1635251031534525315054113)
                      ·
                        rfl

theorem cell23_3184640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_3184640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184640 prefixEnd_3184640 := by exact prefixLift 3184640
  have htrace : WordTrace (prefixWord ++ tailWord_3184640) baseStart_3184640 baseEnd_3184640 := by
    simpa [prefixWord, tailWord_3184640, baseEnd_3184640] using wordTrace_append hprefix tailTrace_3184640
  have hstable : (prefixWord ++ tailWord_3184640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184640).length < 2 ^ (prefixWord ++ tailWord_3184640).sum := by decide
  have hdescent : baseEnd_3184640 < baseStart_3184640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184644 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3184644 : Nat := 118140960795 + 3184644 * 2 ^ 59
def prefixEnd_3184644 : Nat := 4983230072969 + 3 ^ 40 * 3184644 * 2
def baseEnd_3184644 : Nat := 1635253085457143299404095

theorem tailTrace_3184644 : CollatzResearch.WordTrace tailWord_3184644 prefixEnd_3184644 1635253085457143299404095 := by
  unfold tailWord_3184644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58076754537293078369352493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77435672716390771159136657 58076754537293078369352493)
  ·
    refine ⟨21778782951484904388507185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58076754537293078369352493 21778782951484904388507185)
    ·
      refine ⟨16334087213613678291380389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21778782951484904388507185 16334087213613678291380389)
      ·
        refine ⟨3062641352552564679633823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16334087213613678291380389 3062641352552564679633823)
        ·
          refine ⟨4593962028828847019450735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062641352552564679633823 4593962028828847019450735)
          ·
            refine ⟨6890943043243270529176103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593962028828847019450735 6890943043243270529176103)
            ·
              refine ⟨10336414564864905793764155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6890943043243270529176103 10336414564864905793764155)
              ·
                refine ⟨15504621847297358690646233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10336414564864905793764155 15504621847297358690646233)
                ·
                  refine ⟨11628466385473019017984675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15504621847297358690646233 11628466385473019017984675)
                  ·
                    refine ⟨17442699578209528526977013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11628466385473019017984675 17442699578209528526977013)
                    ·
                      refine ⟨1635253085457143299404095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17442699578209528526977013 1635253085457143299404095)
                      ·
                        rfl

theorem cell23_3184644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3184644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184644 prefixEnd_3184644 := by exact prefixLift 3184644
  have htrace : WordTrace (prefixWord ++ tailWord_3184644) baseStart_3184644 baseEnd_3184644 := by
    simpa [prefixWord, tailWord_3184644, baseEnd_3184644] using wordTrace_append hprefix tailTrace_3184644
  have hstable : (prefixWord ++ tailWord_3184644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184644).length < 2 ^ (prefixWord ++ tailWord_3184644).sum := by decide
  have hdescent : baseEnd_3184644 < baseStart_3184644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184664 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 5]
def baseStart_3184664 : Nat := 118140960795 + 3184664 * 2 ^ 59
def prefixEnd_3184664 : Nat := 4983230072969 + 3 ^ 40 * 3184664 * 2
def baseEnd_3184664 : Nat := 181695928341137024572667

theorem tailTrace_3184664 : CollatzResearch.WordTrace tailWord_3184664 prefixEnd_3184664 181695928341137024572667 := by
  unfold tailWord_3184664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58077119267256850077216523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77436159023009133436288697 58077119267256850077216523)
  ·
    refine ⟨87115678900885275115824785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58077119267256850077216523 87115678900885275115824785)
    ·
      refine ⟨65336759175663956336868589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87115678900885275115824785 65336759175663956336868589)
      ·
        refine ⟨24501284690873983626325721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65336759175663956336868589 24501284690873983626325721)
        ·
          refine ⟨18375963518155487719744291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24501284690873983626325721 18375963518155487719744291)
          ·
            refine ⟨27563945277233231579616437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18375963518155487719744291 27563945277233231579616437)
            ·
              refine ⟨2584119869740615460589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27563945277233231579616437 2584119869740615460589041)
              ·
                refine ⟨1938089902305461595441781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2584119869740615460589041 1938089902305461595441781)
                ·
                  refine ⟨181695928341137024572667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938089902305461595441781 181695928341137024572667)
                  ·
                    rfl

theorem cell23_3184664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 5].length) (baseStart_3184664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184664 prefixEnd_3184664 := by exact prefixLift 3184664
  have htrace : WordTrace (prefixWord ++ tailWord_3184664) baseStart_3184664 baseEnd_3184664 := by
    simpa [prefixWord, tailWord_3184664, baseEnd_3184664] using wordTrace_append hprefix tailTrace_3184664
  have hstable : (prefixWord ++ tailWord_3184664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184664).length < 2 ^ (prefixWord ++ tailWord_3184664).sum := by decide
  have hdescent : baseEnd_3184664 < baseStart_3184664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184694 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3184694 : Nat := 118140960795 + 3184694 * 2 ^ 59
def prefixEnd_3184694 : Nat := 4983230072969 + 3 ^ 40 * 3184694 * 2
def baseEnd_3184694 : Nat := 545092919829956034592955

theorem tailTrace_3184694 : CollatzResearch.WordTrace tailWord_3184694 prefixEnd_3184694 545092919829956034592955 := by
  unfold tailWord_3184694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259708295275313454876571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77436888482936676852016757 7259708295275313454876571)
  ·
    refine ⟨10889562442912970182314857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259708295275313454876571 10889562442912970182314857)
    ·
      refine ⟨8167171832184727636736143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10889562442912970182314857 8167171832184727636736143)
      ·
        refine ⟨12250757748277091455104215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167171832184727636736143 12250757748277091455104215)
        ·
          refine ⟨18376136622415637182656323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12250757748277091455104215 18376136622415637182656323)
          ·
            refine ⟨27564204933623455773984485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18376136622415637182656323 27564204933623455773984485)
            ·
              refine ⟨5168288425054397957622091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27564204933623455773984485 5168288425054397957622091)
              ·
                refine ⟨7752432637581596936433137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168288425054397957622091 7752432637581596936433137)
                ·
                  refine ⟨5814324478186197702324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7752432637581596936433137 5814324478186197702324853)
                  ·
                    refine ⟨545092919829956034592955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5814324478186197702324853 545092919829956034592955)
                    ·
                      rfl

theorem cell23_3184694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3184694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184694 prefixEnd_3184694 := by exact prefixLift 3184694
  have htrace : WordTrace (prefixWord ++ tailWord_3184694) baseStart_3184694 baseEnd_3184694 := by
    simpa [prefixWord, tailWord_3184694, baseEnd_3184694] using wordTrace_append hprefix tailTrace_3184694
  have hstable : (prefixWord ++ tailWord_3184694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184694).length < 2 ^ (prefixWord ++ tailWord_3184694).sum := by decide
  have hdescent : baseEnd_3184694 < baseStart_3184694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184717 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3184717 : Nat := 118140960795 + 3184717 * 2 ^ 59
def prefixEnd_3184717 : Nat := 4983230072969 + 3 ^ 40 * 3184717 * 2
def baseEnd_3184717 : Nat := 1635290569544921513791259

theorem tailTrace_3184717 : CollatzResearch.WordTrace tailWord_3184717 prefixEnd_3184717 1635290569544921513791259 := by
  unfold tailWord_3184717
  simp only [CollatzResearch.WordTrace]
  refine ⟨116156171603321690206112405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77437447735547793470741603 116156171603321690206112405)
  ·
    refine ⟨5444820543905704228411519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116156171603321690206112405 5444820543905704228411519)
    ·
      refine ⟨8167230815858556342617279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444820543905704228411519 8167230815858556342617279)
      ·
        refine ⟨12250846223787834513925919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167230815858556342617279 12250846223787834513925919)
        ·
          refine ⟨18376269335681751770888879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12250846223787834513925919 18376269335681751770888879)
          ·
            refine ⟨27564404003522627656333319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18376269335681751770888879 27564404003522627656333319)
            ·
              refine ⟨41346606005283941484499979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27564404003522627656333319 41346606005283941484499979)
              ·
                refine ⟨62019909007925912226749969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41346606005283941484499979 62019909007925912226749969)
                ·
                  refine ⟨46514931755944434170062477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62019909007925912226749969 46514931755944434170062477)
                  ·
                    refine ⟨17443099408479162813773429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46514931755944434170062477 17443099408479162813773429)
                    ·
                      refine ⟨1635290569544921513791259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17443099408479162813773429 1635290569544921513791259)
                      ·
                        rfl

theorem cell23_3184717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3184717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184717 prefixEnd_3184717 := by exact prefixLift 3184717
  have htrace : WordTrace (prefixWord ++ tailWord_3184717) baseStart_3184717 baseEnd_3184717 := by
    simpa [prefixWord, tailWord_3184717, baseEnd_3184717] using wordTrace_append hprefix tailTrace_3184717
  have hstable : (prefixWord ++ tailWord_3184717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184717).length < 2 ^ (prefixWord ++ tailWord_3184717).sum := by decide
  have hdescent : baseEnd_3184717 < baseStart_3184717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184758 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_3184758 : Nat := 118140960795 + 3184758 * 2 ^ 59
def prefixEnd_3184758 : Nat := 4983230072969 + 3 ^ 40 * 3184758 * 2
def baseEnd_3184758 : Nat := 545103874083918617792857

theorem tailTrace_3184758 : CollatzResearch.WordTrace tailWord_3184758 prefixEnd_3184758 545103874083918617792857 := by
  unfold tailWord_3184758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259854187260822138022183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77438444664115436138903285 7259854187260822138022183)
  ·
    refine ⟨10889781280891233207033275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259854187260822138022183 10889781280891233207033275)
    ·
      refine ⟨16334671921336849810549913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10889781280891233207033275 16334671921336849810549913)
      ·
        refine ⟨12251003941002637357912435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16334671921336849810549913 12251003941002637357912435)
        ·
          refine ⟨18376505911503956036868653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12251003941002637357912435 18376505911503956036868653)
          ·
            refine ⟨6891189716813983513825745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18376505911503956036868653 6891189716813983513825745)
            ·
              refine ⟨5168392287610487635369309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6891189716813983513825745 5168392287610487635369309)
              ·
                refine ⟨1938147107853932863263491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5168392287610487635369309 1938147107853932863263491)
                ·
                  refine ⟨2907220661780899294895237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938147107853932863263491 2907220661780899294895237)
                  ·
                    refine ⟨545103874083918617792857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2907220661780899294895237 545103874083918617792857)
                    ·
                      rfl

theorem cell23_3184758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_3184758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184758 prefixEnd_3184758 := by exact prefixLift 3184758
  have htrace : WordTrace (prefixWord ++ tailWord_3184758) baseStart_3184758 baseEnd_3184758 := by
    simpa [prefixWord, tailWord_3184758, baseEnd_3184758] using wordTrace_append hprefix tailTrace_3184758
  have hstable : (prefixWord ++ tailWord_3184758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184758).length < 2 ^ (prefixWord ++ tailWord_3184758).sum := by decide
  have hdescent : baseEnd_3184758 < baseStart_3184758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184760 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3184760 : Nat := 118140960795 + 3184760 * 2 ^ 59
def prefixEnd_3184760 : Nat := 4983230072969 + 3 ^ 40 * 3184760 * 2
def baseEnd_3184760 : Nat := 1635312649213064845553561

theorem tailTrace_3184760 : CollatzResearch.WordTrace tailWord_3184760 prefixEnd_3184760 1635312649213064845553561 := by
  unfold tailWord_3184760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58078869971082954274963867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77438493294777272366618489 58078869971082954274963867)
  ·
    refine ⟨87118304956624431412445801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58078869971082954274963867 87118304956624431412445801)
    ·
      refine ⟨65338728717468323559334351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87118304956624431412445801 65338728717468323559334351)
      ·
        refine ⟨98008093076202485339001527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65338728717468323559334351 98008093076202485339001527)
        ·
          refine ⟨147012139614303728008502291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98008093076202485339001527 147012139614303728008502291)
          ·
            refine ⟨220518209421455592012753437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147012139614303728008502291 220518209421455592012753437)
            ·
              refine ⟨82694328533045847004782539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220518209421455592012753437 82694328533045847004782539)
              ·
                refine ⟨124041492799568770507173809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82694328533045847004782539 124041492799568770507173809)
                ·
                  refine ⟨93031119599676577880380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124041492799568770507173809 93031119599676577880380357)
                  ·
                    refine ⟨17443334924939358352571317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93031119599676577880380357 17443334924939358352571317)
                    ·
                      refine ⟨1635312649213064845553561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17443334924939358352571317 1635312649213064845553561)
                      ·
                        rfl

theorem cell23_3184760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3184760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184760 prefixEnd_3184760 := by exact prefixLift 3184760
  have htrace : WordTrace (prefixWord ++ tailWord_3184760) baseStart_3184760 baseEnd_3184760 := by
    simpa [prefixWord, tailWord_3184760, baseEnd_3184760] using wordTrace_append hprefix tailTrace_3184760
  have hstable : (prefixWord ++ tailWord_3184760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184760).length < 2 ^ (prefixWord ++ tailWord_3184760).sum := by decide
  have hdescent : baseEnd_3184760 < baseStart_3184760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184780 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_3184780 : Nat := 118140960795 + 3184780 * 2 ^ 59
def prefixEnd_3184780 : Nat := 4983230072969 + 3 ^ 40 * 3184780 * 2
def baseEnd_3184780 : Nat := 545107639608718255767823

theorem tailTrace_3184780 : CollatzResearch.WordTrace tailWord_3184780 prefixEnd_3184780 545107639608718255767823 := by
  unfold tailWord_3184780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58079234701046725982827897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77438979601395634643770529 58079234701046725982827897)
  ·
    refine ⟨43559426025785044487120923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58079234701046725982827897 43559426025785044487120923)
    ·
      refine ⟨65339139038677566730681385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43559426025785044487120923 65339139038677566730681385)
      ·
        refine ⟨49004354279008175048011039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65339139038677566730681385 49004354279008175048011039)
        ·
          refine ⟨73506531418512262572016559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49004354279008175048011039 73506531418512262572016559)
          ·
            refine ⟨110259797127768393858024839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73506531418512262572016559 110259797127768393858024839)
            ·
              refine ⟨165389695691652590787037259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110259797127768393858024839 165389695691652590787037259)
              ·
                refine ⟨248084543537478886180555889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165389695691652590787037259 248084543537478886180555889)
                ·
                  refine ⟨186063407653109164635416917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248084543537478886180555889 186063407653109164635416917)
                  ·
                    refine ⟨545107639608718255767823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 186063407653109164635416917 545107639608718255767823)
                    ·
                      rfl

theorem cell23_3184780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_3184780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184780 prefixEnd_3184780 := by exact prefixLift 3184780
  have htrace : WordTrace (prefixWord ++ tailWord_3184780) baseStart_3184780 baseEnd_3184780 := by
    simpa [prefixWord, tailWord_3184780, baseEnd_3184780] using wordTrace_append hprefix tailTrace_3184780
  have hstable : (prefixWord ++ tailWord_3184780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184780).length < 2 ^ (prefixWord ++ tailWord_3184780).sum := by decide
  have hdescent : baseEnd_3184780 < baseStart_3184780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184788 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3184788 : Nat := 118140960795 + 3184788 * 2 ^ 59
def prefixEnd_3184788 : Nat := 4983230072969 + 3 ^ 40 * 3184788 * 2
def baseEnd_3184788 : Nat := 181703002963487859555937

theorem tailTrace_3184788 : CollatzResearch.WordTrace tailWord_3184788 prefixEnd_3184788 181703002963487859555937 := by
  unfold tailWord_3184788
  simp only [CollatzResearch.WordTrace]
  refine ⟨58079380593032234665973509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77439174124042979554631345 58079380593032234665973509)
  ·
    refine ⟨10889883861193543999870033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58079380593032234665973509 10889883861193543999870033)
    ·
      refine ⟨8167412895895157999902525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10889883861193543999870033 8167412895895157999902525)
      ·
        refine ⟨3062779835960684249963447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8167412895895157999902525 3062779835960684249963447)
        ·
          refine ⟨4594169753941026374945171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062779835960684249963447 4594169753941026374945171)
          ·
            refine ⟨6891254630911539562417757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594169753941026374945171 6891254630911539562417757)
            ·
              refine ⟨2584220486591827335906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6891254630911539562417757 2584220486591827335906659)
              ·
                refine ⟨3876330729887741003859989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584220486591827335906659 3876330729887741003859989)
                ·
                  refine ⟨181703002963487859555937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3876330729887741003859989 181703002963487859555937)
                  ·
                    rfl

theorem cell23_3184788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3184788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184788 prefixEnd_3184788 := by exact prefixLift 3184788
  have htrace : WordTrace (prefixWord ++ tailWord_3184788) baseStart_3184788 baseEnd_3184788 := by
    simpa [prefixWord, tailWord_3184788, baseEnd_3184788] using wordTrace_append hprefix tailTrace_3184788
  have hstable : (prefixWord ++ tailWord_3184788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184788).length < 2 ^ (prefixWord ++ tailWord_3184788).sum := by decide
  have hdescent : baseEnd_3184788 < baseStart_3184788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184824 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3184824 : Nat := 118140960795 + 3184824 * 2 ^ 59
def prefixEnd_3184824 : Nat := 4983230072969 + 3 ^ 40 * 3184824 * 2
def baseEnd_3184824 : Nat := 1635345511974952595153267

theorem tailTrace_3184824 : CollatzResearch.WordTrace tailWord_3184824 prefixEnd_3184824 1635345511974952595153267 := by
  unfold tailWord_3184824
  simp only [CollatzResearch.WordTrace]
  refine ⟨58080037106967023740128763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77440049475956031653505017 58080037106967023740128763)
  ·
    refine ⟨87120055660450535610193145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58080037106967023740128763 87120055660450535610193145)
    ·
      refine ⟨65340041745337901707644859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87120055660450535610193145 65340041745337901707644859)
      ·
        refine ⟨98010062618006852561467289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65340041745337901707644859 98010062618006852561467289)
        ·
          refine ⟨73507546963505139421100467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98010062618006852561467289 73507546963505139421100467)
          ·
            refine ⟨110261320445257709131650701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73507546963505139421100467 110261320445257709131650701)
            ·
              refine ⟨41347995166971640924369013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110261320445257709131650701 41347995166971640924369013)
              ·
                refine ⟨3876374546903591336659595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41347995166971640924369013 3876374546903591336659595)
                ·
                  refine ⟨5814561820355387004989393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876374546903591336659595 5814561820355387004989393)
                  ·
                    refine ⟨4360921365266540253742045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814561820355387004989393 4360921365266540253742045)
                    ·
                      refine ⟨1635345511974952595153267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360921365266540253742045 1635345511974952595153267)
                      ·
                        rfl

theorem cell23_3184824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3184824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184824 prefixEnd_3184824 := by exact prefixLift 3184824
  have htrace : WordTrace (prefixWord ++ tailWord_3184824) baseStart_3184824 baseEnd_3184824 := by
    simpa [prefixWord, tailWord_3184824, baseEnd_3184824] using wordTrace_append hprefix tailTrace_3184824
  have hstable : (prefixWord ++ tailWord_3184824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184824).length < 2 ^ (prefixWord ++ tailWord_3184824).sum := by decide
  have hdescent : baseEnd_3184824 < baseStart_3184824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184871 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3184871 : Nat := 118140960795 + 3184871 * 2 ^ 59
def prefixEnd_3184871 : Nat := 4983230072969 + 3 ^ 40 * 3184871 * 2
def baseEnd_3184871 : Nat := 1635369645565713911265551

theorem tailTrace_3184871 : CollatzResearch.WordTrace tailWord_3184871 prefixEnd_3184871 1635369645565713911265551 := by
  unfold tailWord_3184871
  simp only [CollatzResearch.WordTrace]
  refine ⟨116161788444763774507218467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77441192296509183004812311 116161788444763774507218467)
  ·
    refine ⟨174242682667145661760827701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116161788444763774507218467 174242682667145661760827701)
    ·
      refine ⟨16335251500044905790077597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174242682667145661760827701 16335251500044905790077597)
      ·
        refine ⟨6125719312516839671279099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16335251500044905790077597 6125719312516839671279099)
        ·
          refine ⟨9188578968775259506918649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125719312516839671279099 9188578968775259506918649)
          ·
            refine ⟨6891434226581444630188987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188578968775259506918649 6891434226581444630188987)
            ·
              refine ⟨10337151339872166945283481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891434226581444630188987 10337151339872166945283481)
              ·
                refine ⟨7752863504904125208962611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10337151339872166945283481 7752863504904125208962611)
                ·
                  refine ⟨11629295257356187813443917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7752863504904125208962611 11629295257356187813443917)
                  ·
                    refine ⟨4360985721508570430041469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11629295257356187813443917 4360985721508570430041469)
                    ·
                      refine ⟨1635369645565713911265551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4360985721508570430041469 1635369645565713911265551)
                      ·
                        rfl

theorem cell23_3184871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3184871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184871 prefixEnd_3184871 := by exact prefixLift 3184871
  have htrace : WordTrace (prefixWord ++ tailWord_3184871) baseStart_3184871 baseEnd_3184871 := by
    simpa [prefixWord, tailWord_3184871, baseEnd_3184871] using wordTrace_append hprefix tailTrace_3184871
  have hstable : (prefixWord ++ tailWord_3184871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184871).length < 2 ^ (prefixWord ++ tailWord_3184871).sum := by decide
  have hdescent : baseEnd_3184871 < baseStart_3184871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184881 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_3184881 : Nat := 118140960795 + 3184881 * 2 ^ 59
def prefixEnd_3184881 : Nat := 4983230072969 + 3 ^ 40 * 3184881 * 2
def baseEnd_3184881 : Nat := 1635374780372258872140505

theorem tailTrace_3184881 : CollatzResearch.WordTrace tailWord_3184881 prefixEnd_3184881 1635374780372258872140505 := by
  unfold tailWord_3184881
  simp only [CollatzResearch.WordTrace]
  refine ⟨116162153174727546215082497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77441435449818364143388331 116162153174727546215082497)
  ·
    refine ⟨87121614881045659661311873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116162153174727546215082497 87121614881045659661311873)
    ·
      refine ⟨65341211160784244745983905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87121614881045659661311873 65341211160784244745983905)
      ·
        refine ⟨49005908370588183559487929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65341211160784244745983905 49005908370588183559487929)
        ·
          refine ⟨36754431277941137669615947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49005908370588183559487929 36754431277941137669615947)
          ·
            refine ⟨55131646916911706504423921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36754431277941137669615947 55131646916911706504423921)
            ·
              refine ⟨41348735187683779878317941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55131646916911706504423921 41348735187683779878317941)
              ·
                refine ⟨3876443923845354363592307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41348735187683779878317941 3876443923845354363592307)
                ·
                  refine ⟨5814665885768031545388461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876443923845354363592307 5814665885768031545388461)
                  ·
                    refine ⟨2180499707163011829520673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5814665885768031545388461 2180499707163011829520673)
                    ·
                      refine ⟨1635374780372258872140505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180499707163011829520673 1635374780372258872140505)
                      ·
                        rfl

theorem cell23_3184881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_3184881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184881 prefixEnd_3184881 := by exact prefixLift 3184881
  have htrace : WordTrace (prefixWord ++ tailWord_3184881) baseStart_3184881 baseEnd_3184881 := by
    simpa [prefixWord, tailWord_3184881, baseEnd_3184881] using wordTrace_append hprefix tailTrace_3184881
  have hstable : (prefixWord ++ tailWord_3184881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184881).length < 2 ^ (prefixWord ++ tailWord_3184881).sum := by decide
  have hdescent : baseEnd_3184881 < baseStart_3184881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184894 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3184894 : Nat := 118140960795 + 3184894 * 2 ^ 59
def prefixEnd_3184894 : Nat := 4983230072969 + 3 ^ 40 * 3184894 * 2
def baseEnd_3184894 : Nat := 1635381455620767321277945

theorem tailTrace_3184894 : CollatzResearch.WordTrace tailWord_3184894 prefixEnd_3184894 1635381455620767321277945 := by
  unfold tailWord_3184894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520328415460056179413217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77441751549120299623537157 14520328415460056179413217)
  ·
    refine ⟨10890246311595042134559913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14520328415460056179413217 10890246311595042134559913)
    ·
      refine ⟨8167684733696281600919935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10890246311595042134559913 8167684733696281600919935)
      ·
        refine ⟨12251527100544422401379903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167684733696281600919935 12251527100544422401379903)
        ·
          refine ⟨18377290650816633602069855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12251527100544422401379903 18377290650816633602069855)
          ·
            refine ⟨27565935976224950403104783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18377290650816633602069855 27565935976224950403104783)
            ·
              refine ⟨41348903964337425604657175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27565935976224950403104783 41348903964337425604657175)
              ·
                refine ⟨62023355946506138406985763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41348903964337425604657175 62023355946506138406985763)
                ·
                  refine ⟨93035033919759207610478645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62023355946506138406985763 93035033919759207610478645)
                  ·
                    refine ⟨8722034429977425713482373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93035033919759207610478645 8722034429977425713482373)
                    ·
                      refine ⟨1635381455620767321277945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8722034429977425713482373 1635381455620767321277945)
                      ·
                        rfl

theorem cell23_3184894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3184894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184894 prefixEnd_3184894 := by exact prefixLift 3184894
  have htrace : WordTrace (prefixWord ++ tailWord_3184894) baseStart_3184894 baseEnd_3184894 := by
    simpa [prefixWord, tailWord_3184894, baseEnd_3184894] using wordTrace_append hprefix tailTrace_3184894
  have hstable : (prefixWord ++ tailWord_3184894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184894).length < 2 ^ (prefixWord ++ tailWord_3184894).sum := by decide
  have hdescent : baseEnd_3184894 < baseStart_3184894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184898 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3184898 : Nat := 118140960795 + 3184898 * 2 ^ 59
def prefixEnd_3184898 : Nat := 4983230072969 + 3 ^ 40 * 3184898 * 2
def baseEnd_3184898 : Nat := 1635383509543385305627927

theorem tailTrace_3184898 : CollatzResearch.WordTrace tailWord_3184898 prefixEnd_3184898 1635383509543385305627927 := by
  unfold tailWord_3184898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040693303916489529612837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77441848810443972078967565 29040693303916489529612837)
  ·
    refine ⟨5445129994484341786802407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29040693303916489529612837 5445129994484341786802407)
    ·
      refine ⟨8167694991726512680203611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445129994484341786802407 8167694991726512680203611)
      ·
        refine ⟨12251542487589769020305417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8167694991726512680203611 12251542487589769020305417)
        ·
          refine ⟨9188656865692326765229063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12251542487589769020305417 9188656865692326765229063)
          ·
            refine ⟨13782985298538490147843595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188656865692326765229063 13782985298538490147843595)
            ·
              refine ⟨20674477947807735221765393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13782985298538490147843595 20674477947807735221765393)
              ·
                refine ⟨15505858460855801416324045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20674477947807735221765393 15505858460855801416324045)
                ·
                  refine ⟨5814696922820925531121517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15505858460855801416324045 5814696922820925531121517)
                  ·
                    refine ⟨2180511346057847074170569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5814696922820925531121517 2180511346057847074170569)
                    ·
                      refine ⟨1635383509543385305627927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180511346057847074170569 1635383509543385305627927)
                      ·
                        rfl

theorem cell23_3184898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3184898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184898 prefixEnd_3184898 := by exact prefixLift 3184898
  have htrace : WordTrace (prefixWord ++ tailWord_3184898) baseStart_3184898 baseEnd_3184898 := by
    simpa [prefixWord, tailWord_3184898, baseEnd_3184898] using wordTrace_append hprefix tailTrace_3184898
  have hstable : (prefixWord ++ tailWord_3184898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184898).length < 2 ^ (prefixWord ++ tailWord_3184898).sum := by decide
  have hdescent : baseEnd_3184898 < baseStart_3184898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184904 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_3184904 : Nat := 118140960795 + 3184904 * 2 ^ 59
def prefixEnd_3184904 : Nat := 4983230072969 + 3 ^ 40 * 3184904 * 2
def baseEnd_3184904 : Nat := 545128863475770760717633

theorem tailTrace_3184904 : CollatzResearch.WordTrace tailWord_3184904 prefixEnd_3184904 545128863475770760717633 := by
  unfold tailWord_3184904
  simp only [CollatzResearch.WordTrace]
  refine ⟨58081496026822110571584883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77441994702429480762113177 58081496026822110571584883)
  ·
    refine ⟨87122244040233165857377325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58081496026822110571584883 87122244040233165857377325)
    ·
      refine ⟨32670841515087437196516497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87122244040233165857377325 32670841515087437196516497)
      ·
        refine ⟨24503131136315577897387373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32670841515087437196516497 24503131136315577897387373)
        ·
          refine ⟨9188674176118341711520265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24503131136315577897387373 9188674176118341711520265)
          ·
            refine ⟨6891505632088756283640199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9188674176118341711520265 6891505632088756283640199)
            ·
              refine ⟨10337258448133134425460299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6891505632088756283640199 10337258448133134425460299)
              ·
                refine ⟨15505887672199701638190449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10337258448133134425460299 15505887672199701638190449)
                ·
                  refine ⟨11629415754149776228642837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15505887672199701638190449 11629415754149776228642837)
                  ·
                    refine ⟨545128863475770760717633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11629415754149776228642837 545128863475770760717633)
                    ·
                      rfl

theorem cell23_3184904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_3184904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184904 prefixEnd_3184904 := by exact prefixLift 3184904
  have htrace : WordTrace (prefixWord ++ tailWord_3184904) baseStart_3184904 baseEnd_3184904 := by
    simpa [prefixWord, tailWord_3184904, baseEnd_3184904] using wordTrace_append hprefix tailTrace_3184904
  have hstable : (prefixWord ++ tailWord_3184904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184904).length < 2 ^ (prefixWord ++ tailWord_3184904).sum := by decide
  have hdescent : baseEnd_3184904 < baseStart_3184904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3184917 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 9]
def baseStart_3184917 : Nat := 118140960795 + 3184917 * 2 ^ 59
def prefixEnd_3184917 : Nat := 4983230072969 + 3 ^ 40 * 3184917 * 2
def baseEnd_3184917 : Nat := 181710362852868970143371

theorem tailTrace_3184917 : CollatzResearch.WordTrace tailWord_3184917 prefixEnd_3184917 181710362852868970143371 := by
  unfold tailWord_3184917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116163466202597124363393005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77442310801731416242262003 116163466202597124363393005)
  ·
    refine ⟨43561299825973921636272377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116163466202597124363393005 43561299825973921636272377)
    ·
      refine ⟨32670974869480441227204283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43561299825973921636272377 32670974869480441227204283)
      ·
        refine ⟨49006462304220661840806425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32670974869480441227204283 49006462304220661840806425)
        ·
          refine ⟨36754846728165496380604819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49006462304220661840806425 36754846728165496380604819)
          ·
            refine ⟨55132270092248244570907229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36754846728165496380604819 55132270092248244570907229)
            ·
              refine ⟨20674601284593091714090211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55132270092248244570907229 20674601284593091714090211)
              ·
                refine ⟨31011901926889637571135317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20674601284593091714090211 31011901926889637571135317)
                ·
                  refine ⟨181710362852868970143371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31011901926889637571135317 181710362852868970143371)
                  ·
                    rfl

theorem cell23_3184917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_3184917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3184917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3184917 prefixEnd_3184917 := by exact prefixLift 3184917
  have htrace : WordTrace (prefixWord ++ tailWord_3184917) baseStart_3184917 baseEnd_3184917 := by
    simpa [prefixWord, tailWord_3184917, baseEnd_3184917] using wordTrace_append hprefix tailTrace_3184917
  have hstable : (prefixWord ++ tailWord_3184917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3184917).length < 2 ^ (prefixWord ++ tailWord_3184917).sum := by decide
  have hdescent : baseEnd_3184917 < baseStart_3184917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3184917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185038 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3185038 : Nat := 118140960795 + 3185038 * 2 ^ 59
def prefixEnd_3185038 : Nat := 4983230072969 + 3 ^ 40 * 3185038 * 2
def baseEnd_3185038 : Nat := 1635455396835014757877283

theorem tailTrace_3185038 : CollatzResearch.WordTrace tailWord_3185038 prefixEnd_3185038 1635455396835014757877283 := by
  unfold tailWord_3185038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520984929394845253568471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77445252956772508019031845 14520984929394845253568471)
  ·
    refine ⟨21781477394092267880352707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14520984929394845253568471 21781477394092267880352707)
    ·
      refine ⟨32672216091138401820529061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781477394092267880352707 32672216091138401820529061)
      ·
        refine ⟨6126040517088450341349199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32672216091138401820529061 6126040517088450341349199)
        ·
          refine ⟨9189060775632675512023799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126040517088450341349199 9189060775632675512023799)
          ·
            refine ⟨13783591163449013268035699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189060775632675512023799 13783591163449013268035699)
            ·
              refine ⟨20675386745173519902053549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13783591163449013268035699 20675386745173519902053549)
              ·
                refine ⟨7753270029440069963270081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20675386745173519902053549 7753270029440069963270081)
                ·
                  refine ⟨5814952522080052472452561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7753270029440069963270081 5814952522080052472452561)
                  ·
                    refine ⟨4361214391560039354339421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5814952522080052472452561 4361214391560039354339421)
                    ·
                      refine ⟨1635455396835014757877283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361214391560039354339421 1635455396835014757877283)
                      ·
                        rfl

theorem cell23_3185038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3185038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185038 prefixEnd_3185038 := by exact prefixLift 3185038
  have htrace : WordTrace (prefixWord ++ tailWord_3185038) baseStart_3185038 baseEnd_3185038 := by
    simpa [prefixWord, tailWord_3185038, baseEnd_3185038] using wordTrace_append hprefix tailTrace_3185038
  have hstable : (prefixWord ++ tailWord_3185038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185038).length < 2 ^ (prefixWord ++ tailWord_3185038).sum := by decide
  have hdescent : baseEnd_3185038 < baseStart_3185038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185089 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3185089 : Nat := 118140960795 + 3185089 * 2 ^ 59
def prefixEnd_3185089 : Nat := 4983230072969 + 3 ^ 40 * 3185089 * 2
def baseEnd_3185089 : Nat := 1635481584348394058339549

theorem tailTrace_3185089 : CollatzResearch.WordTrace tailWord_3185089 prefixEnd_3185089 1635481584348394058339549 := by
  unfold tailWord_3185089
  simp only [CollatzResearch.WordTrace]
  refine ⟨116169739557973997738654321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77446493038649331825769547 116169739557973997738654321)
  ·
    refine ⟨87127304668480498303990741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116169739557973997738654321 87127304668480498303990741)
    ·
      refine ⟨2042046203167511678999783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87127304668480498303990741 2042046203167511678999783)
      ·
        refine ⟨3063069304751267518499675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042046203167511678999783 3063069304751267518499675)
        ·
          refine ⟨4594603957126901277749513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063069304751267518499675 4594603957126901277749513)
          ·
            refine ⟨3445952967845175958312135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594603957126901277749513 3445952967845175958312135)
            ·
              refine ⟨5168929451767763937468203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445952967845175958312135 5168929451767763937468203)
              ·
                refine ⟨7753394177651645906202305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168929451767763937468203 7753394177651645906202305)
                ·
                  refine ⟨5815045633238734429651729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7753394177651645906202305 5815045633238734429651729)
                  ·
                    refine ⟨4361284224929050822238797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5815045633238734429651729 4361284224929050822238797)
                    ·
                      refine ⟨1635481584348394058339549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361284224929050822238797 1635481584348394058339549)
                      ·
                        rfl

theorem cell23_3185089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3185089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185089 prefixEnd_3185089 := by exact prefixLift 3185089
  have htrace : WordTrace (prefixWord ++ tailWord_3185089) baseStart_3185089 baseEnd_3185089 := by
    simpa [prefixWord, tailWord_3185089, baseEnd_3185089] using wordTrace_append hprefix tailTrace_3185089
  have hstable : (prefixWord ++ tailWord_3185089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185089).length < 2 ^ (prefixWord ++ tailWord_3185089).sum := by decide
  have hdescent : baseEnd_3185089 < baseStart_3185089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185091 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 4]
def baseStart_3185091 : Nat := 118140960795 + 3185091 * 2 ^ 59
def prefixEnd_3185091 : Nat := 4983230072969 + 3 ^ 40 * 3185091 * 2
def baseEnd_3185091 : Nat := 1635482611309703050514539

theorem tailTrace_3185091 : CollatzResearch.WordTrace tailWord_3185091 prefixEnd_3185091 1635482611309703050514539 := by
  unfold tailWord_3185091
  simp only [CollatzResearch.WordTrace]
  refine ⟨116169812503966752080227127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77446541669311168053484751 116169812503966752080227127)
  ·
    refine ⟨174254718755950128120340691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116169812503966752080227127 174254718755950128120340691)
    ·
      refine ⟨261382078133925192180511037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174254718755950128120340691 261382078133925192180511037)
      ·
        refine ⟨98018279300221947067691639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261382078133925192180511037 98018279300221947067691639)
        ·
          refine ⟨147027418950332920601537459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98018279300221947067691639 147027418950332920601537459)
          ·
            refine ⟨220541128425499380902306189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147027418950332920601537459 220541128425499380902306189)
            ·
              refine ⟨82702923159562267838364821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220541128425499380902306189 82702923159562267838364821)
              ·
                refine ⟨3876699523104481304923351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82702923159562267838364821 3876699523104481304923351)
                ·
                  refine ⟨5815049284656721957385027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3876699523104481304923351 5815049284656721957385027)
                  ·
                    refine ⟨8722573926985082936077541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5815049284656721957385027 8722573926985082936077541)
                    ·
                      refine ⟨1635482611309703050514539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8722573926985082936077541 1635482611309703050514539)
                      ·
                        rfl

theorem cell23_3185091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_3185091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185091 prefixEnd_3185091 := by exact prefixLift 3185091
  have htrace : WordTrace (prefixWord ++ tailWord_3185091) baseStart_3185091 baseEnd_3185091 := by
    simpa [prefixWord, tailWord_3185091, baseEnd_3185091] using wordTrace_append hprefix tailTrace_3185091
  have hstable : (prefixWord ++ tailWord_3185091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185091).length < 2 ^ (prefixWord ++ tailWord_3185091).sum := by decide
  have hdescent : baseEnd_3185091 < baseStart_3185091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185095 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_3185095 : Nat := 118140960795 + 3185095 * 2 ^ 59
def prefixEnd_3185095 : Nat := 4983230072969 + 3 ^ 40 * 3185095 * 2
def baseEnd_3185095 : Nat := 1635484665232321034864521

theorem tailTrace_3185095 : CollatzResearch.WordTrace tailWord_3185095 prefixEnd_3185095 1635484665232321034864521 := by
  unfold tailWord_3185095
  simp only [CollatzResearch.WordTrace]
  refine ⟨116169958395952260763372739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77446638930634840508915159 116169958395952260763372739)
  ·
    refine ⟨174254937593928391145059109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116169958395952260763372739 174254937593928391145059109)
    ·
      refine ⟨32672800798861573339698583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174254937593928391145059109 32672800798861573339698583)
      ·
        refine ⟨49009201198292360009547875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32672800798861573339698583 49009201198292360009547875)
        ·
          refine ⟨73513801797438540014321813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49009201198292360009547875 73513801797438540014321813)
          ·
            refine ⟨3445959459254931563171335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73513801797438540014321813 3445959459254931563171335)
            ·
              refine ⟨5168939188882397344757003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445959459254931563171335 5168939188882397344757003)
              ·
                refine ⟨7753408783323596017135505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168939188882397344757003 7753408783323596017135505)
                ·
                  refine ⟨5815056587492697012851629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7753408783323596017135505 5815056587492697012851629)
                  ·
                    refine ⟨2180646220309761379819361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5815056587492697012851629 2180646220309761379819361)
                    ·
                      refine ⟨1635484665232321034864521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180646220309761379819361 1635484665232321034864521)
                      ·
                        rfl

theorem cell23_3185095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_3185095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185095 prefixEnd_3185095 := by exact prefixLift 3185095
  have htrace : WordTrace (prefixWord ++ tailWord_3185095) baseStart_3185095 baseEnd_3185095 := by
    simpa [prefixWord, tailWord_3185095, baseEnd_3185095] using wordTrace_append hprefix tailTrace_3185095
  have hstable : (prefixWord ++ tailWord_3185095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185095).length < 2 ^ (prefixWord ++ tailWord_3185095).sum := by decide
  have hdescent : baseEnd_3185095 < baseStart_3185095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185114 : List Nat := [3, 1, 1, 2, 3, 1, 12]
def baseStart_3185114 : Nat := 118140960795 + 3185114 * 2 ^ 59
def prefixEnd_3185114 : Nat := 4983230072969 + 3 ^ 40 * 3185114 * 2
def baseEnd_3185114 : Nat := 20191289152651314327493

theorem tailTrace_3185114 : CollatzResearch.WordTrace tailWord_3185114 prefixEnd_3185114 20191289152651314327493 := by
  unfold tailWord_3185114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042662845720856752078599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77447100921922284672209597 29042662845720856752078599)
  ·
    refine ⟨43563994268581285128117899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29042662845720856752078599 43563994268581285128117899)
    ·
      refine ⟨65345991402871927692176849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43563994268581285128117899 65345991402871927692176849)
      ·
        refine ⟨49009493552153945769132637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65345991402871927692176849 49009493552153945769132637)
        ·
          refine ⟨18378560082057729663424739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49009493552153945769132637 18378560082057729663424739)
          ·
            refine ⟨27567840123086594495137109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18378560082057729663424739 27567840123086594495137109)
            ·
              refine ⟨20191289152651314327493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27567840123086594495137109 20191289152651314327493)
              ·
                rfl

theorem cell23_3185114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 12].length) (baseStart_3185114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185114 prefixEnd_3185114 := by exact prefixLift 3185114
  have htrace : WordTrace (prefixWord ++ tailWord_3185114) baseStart_3185114 baseEnd_3185114 := by
    simpa [prefixWord, tailWord_3185114, baseEnd_3185114] using wordTrace_append hprefix tailTrace_3185114
  have hstable : (prefixWord ++ tailWord_3185114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185114).length < 2 ^ (prefixWord ++ tailWord_3185114).sum := by decide
  have hdescent : baseEnd_3185114 < baseStart_3185114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185124 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3185124 : Nat := 118140960795 + 3185124 * 2 ^ 59
def prefixEnd_3185124 : Nat := 4983230072969 + 3 ^ 40 * 3185124 * 2
def baseEnd_3185124 : Nat := 1635499556171301421401887

theorem tailTrace_3185124 : CollatzResearch.WordTrace tailWord_3185124 prefixEnd_3185124 1635499556171301421401887 := by
  unfold tailWord_3185124
  simp only [CollatzResearch.WordTrace]
  refine ⟨58085508056423599358089213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77447344075231465810785617 58085508056423599358089213)
  ·
    refine ⟨21782065521158849759283455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58085508056423599358089213 21782065521158849759283455)
    ·
      refine ⟨32673098281738274638925183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21782065521158849759283455 32673098281738274638925183)
      ·
        refine ⟨49009647422607411958387775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32673098281738274638925183 49009647422607411958387775)
        ·
          refine ⟨73514471133911117937581663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49009647422607411958387775 73514471133911117937581663)
          ·
            refine ⟨110271706700866676906372495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73514471133911117937581663 110271706700866676906372495)
            ·
              refine ⟨165407560051300015359558743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110271706700866676906372495 165407560051300015359558743)
              ·
                refine ⟨248111340076950023039338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165407560051300015359558743 248111340076950023039338115)
                ·
                  refine ⟨372167010115425034559007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248111340076950023039338115 372167010115425034559007173)
                  ·
                    refine ⟨69781314396642193979813845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372167010115425034559007173 69781314396642193979813845)
                    ·
                      refine ⟨1635499556171301421401887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69781314396642193979813845 1635499556171301421401887)
                      ·
                        rfl

theorem cell23_3185124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3185124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185124 prefixEnd_3185124 := by exact prefixLift 3185124
  have htrace : WordTrace (prefixWord ++ tailWord_3185124) baseStart_3185124 baseEnd_3185124 := by
    simpa [prefixWord, tailWord_3185124, baseEnd_3185124] using wordTrace_append hprefix tailTrace_3185124
  have hstable : (prefixWord ++ tailWord_3185124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185124).length < 2 ^ (prefixWord ++ tailWord_3185124).sum := by decide
  have hdescent : baseEnd_3185124 < baseStart_3185124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185138 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3185138 : Nat := 118140960795 + 3185138 * 2 ^ 59
def prefixEnd_3185138 : Nat := 4983230072969 + 3 ^ 40 * 3185138 * 2
def baseEnd_3185138 : Nat := 1635506744900464366626823

theorem tailTrace_3185138 : CollatzResearch.WordTrace tailWord_3185138 prefixEnd_3185138 1635506744900464366626823 := by
  unfold tailWord_3185138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042881683699119776797017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77447684489864319404792045 29042881683699119776797017)
  ·
    refine ⟨21782161262774339832597763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29042881683699119776797017 21782161262774339832597763)
    ·
      refine ⟨32673241894161509748896645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21782161262774339832597763 32673241894161509748896645)
      ·
        refine ⟨6126232855155283077918121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32673241894161509748896645 6126232855155283077918121)
        ·
          refine ⟨4594674641366462308438591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6126232855155283077918121 4594674641366462308438591)
          ·
            refine ⟨6892011962049693462657887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594674641366462308438591 6892011962049693462657887)
            ·
              refine ⟨10338017943074540193986831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892011962049693462657887 10338017943074540193986831)
              ·
                refine ⟨15507026914611810290980247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338017943074540193986831 15507026914611810290980247)
                ·
                  refine ⟨23260540371917715436470371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15507026914611810290980247 23260540371917715436470371)
                  ·
                    refine ⟨34890810557876573154705557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23260540371917715436470371 34890810557876573154705557)
                    ·
                      refine ⟨1635506744900464366626823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34890810557876573154705557 1635506744900464366626823)
                      ·
                        rfl

theorem cell23_3185138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3185138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185138 prefixEnd_3185138 := by exact prefixLift 3185138
  have htrace : WordTrace (prefixWord ++ tailWord_3185138) baseStart_3185138 baseEnd_3185138 := by
    simpa [prefixWord, tailWord_3185138, baseEnd_3185138] using wordTrace_append hprefix tailTrace_3185138
  have hstable : (prefixWord ++ tailWord_3185138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185138).length < 2 ^ (prefixWord ++ tailWord_3185138).sum := by decide
  have hdescent : baseEnd_3185138 < baseStart_3185138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185165 : List Nat := [1, 7, 1, 1, 1, 3, 9]
def baseStart_3185165 : Nat := 118140960795 + 3185165 * 2 ^ 59
def prefixEnd_3185165 : Nat := 4983230072969 + 3 ^ 40 * 3185165 * 2
def baseEnd_3185165 : Nat := 20191612455285626678879

theorem tailTrace_3185165 : CollatzResearch.WordTrace tailWord_3185165 prefixEnd_3185165 20191612455285626678879 := by
  unfold tailWord_3185165
  simp only [CollatzResearch.WordTrace]
  refine ⟨116172511505698662718420949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77448341003799108478947299 116172511505698662718420949)
  ·
    refine ⟨2722793238414812407462991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 116172511505698662718420949 2722793238414812407462991)
    ·
      refine ⟨4084189857622218611194487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722793238414812407462991 4084189857622218611194487)
      ·
        refine ⟨6126284786433327916791731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084189857622218611194487 6126284786433327916791731)
        ·
          refine ⟨9189427179649991875187597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126284786433327916791731 9189427179649991875187597)
          ·
            refine ⟨3446035192368746953195349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9189427179649991875187597 3446035192368746953195349)
            ·
              refine ⟨20191612455285626678879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3446035192368746953195349 20191612455285626678879)
              ·
                rfl

theorem cell23_3185165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 9].length) (baseStart_3185165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185165 prefixEnd_3185165 := by exact prefixLift 3185165
  have htrace : WordTrace (prefixWord ++ tailWord_3185165) baseStart_3185165 baseEnd_3185165 := by
    simpa [prefixWord, tailWord_3185165, baseEnd_3185165] using wordTrace_append hprefix tailTrace_3185165
  have hstable : (prefixWord ++ tailWord_3185165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185165).length < 2 ^ (prefixWord ++ tailWord_3185165).sum := by decide
  have hdescent : baseEnd_3185165 < baseStart_3185165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185192 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3185192 : Nat := 118140960795 + 3185192 * 2 ^ 59
def prefixEnd_3185192 : Nat := 4983230072969 + 3 ^ 40 * 3185192 * 2
def baseEnd_3185192 : Nat := 1635534472855807155351575

theorem tailTrace_3185192 : CollatzResearch.WordTrace tailWord_3185192 prefixEnd_3185192 1635534472855807155351575 := by
  unfold tailWord_3185192
  simp only [CollatzResearch.WordTrace]
  refine ⟨58086748138300423164826915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77448997517733897553102553 58086748138300423164826915)
  ·
    refine ⟨87130122207450634747240373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58086748138300423164826915 87130122207450634747240373)
    ·
      refine ⟨8168448956948497007553785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87130122207450634747240373 8168448956948497007553785)
      ·
        refine ⟨6126336717711372755665339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168448956948497007553785 6126336717711372755665339)
        ·
          refine ⟨9189505076567059133498009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126336717711372755665339 9189505076567059133498009)
          ·
            refine ⟨6892128807425294350123507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9189505076567059133498009 6892128807425294350123507)
            ·
              refine ⟨10338193211137941525185261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892128807425294350123507 10338193211137941525185261)
              ·
                refine ⟨3876822454176728071944473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10338193211137941525185261 3876822454176728071944473)
                ·
                  refine ⟨2907616840632546053958355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3876822454176728071944473 2907616840632546053958355)
                  ·
                    refine ⟨4361425260948819080937533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907616840632546053958355 4361425260948819080937533)
                    ·
                      refine ⟨1635534472855807155351575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361425260948819080937533 1635534472855807155351575)
                      ·
                        rfl

theorem cell23_3185192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3185192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185192 prefixEnd_3185192 := by exact prefixLift 3185192
  have htrace : WordTrace (prefixWord ++ tailWord_3185192) baseStart_3185192 baseEnd_3185192 := by
    simpa [prefixWord, tailWord_3185192, baseEnd_3185192] using wordTrace_append hprefix tailTrace_3185192
  have hstable : (prefixWord ++ tailWord_3185192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185192).length < 2 ^ (prefixWord ++ tailWord_3185192).sum := by decide
  have hdescent : baseEnd_3185192 < baseStart_3185192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185201 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3185201 : Nat := 118140960795 + 3185201 * 2 ^ 59
def prefixEnd_3185201 : Nat := 4983230072969 + 3 ^ 40 * 3185201 * 2
def baseEnd_3185201 : Nat := 1635539094181697620139033

theorem tailTrace_3185201 : CollatzResearch.WordTrace tailWord_3185201 prefixEnd_3185201 1635539094181697620139033 := by
  unfold tailWord_3185201
  simp only [CollatzResearch.WordTrace]
  refine ⟨116173824533568240866731457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77449216355712160577820971 116173824533568240866731457)
  ·
    refine ⟨87130368400176180650048593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116173824533568240866731457 87130368400176180650048593)
    ·
      refine ⟨65347776300132135487536445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87130368400176180650048593 65347776300132135487536445)
      ·
        refine ⟨24505416112549550807826167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65347776300132135487536445 24505416112549550807826167)
        ·
          refine ⟨36758124168824326211739251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24505416112549550807826167 36758124168824326211739251)
          ·
            refine ⟨55137186253236489317608877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36758124168824326211739251 55137186253236489317608877)
            ·
              refine ⟨20676444844963683494103329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55137186253236489317608877 20676444844963683494103329)
              ·
                refine ⟨15507333633722762620577497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20676444844963683494103329 15507333633722762620577497)
                ·
                  refine ⟨11630500225292071965433123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15507333633722762620577497 11630500225292071965433123)
                  ·
                    refine ⟨17445750337938107948149685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11630500225292071965433123 17445750337938107948149685)
                    ·
                      refine ⟨1635539094181697620139033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17445750337938107948149685 1635539094181697620139033)
                      ·
                        rfl

theorem cell23_3185201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3185201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185201 prefixEnd_3185201 := by exact prefixLift 3185201
  have htrace : WordTrace (prefixWord ++ tailWord_3185201) baseStart_3185201 baseEnd_3185201 := by
    simpa [prefixWord, tailWord_3185201, baseEnd_3185201] using wordTrace_append hprefix tailTrace_3185201
  have hstable : (prefixWord ++ tailWord_3185201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185201).length < 2 ^ (prefixWord ++ tailWord_3185201).sum := by decide
  have hdescent : baseEnd_3185201 < baseStart_3185201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185251 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 7]
def baseStart_3185251 : Nat := 118140960795 + 3185251 * 2 ^ 59
def prefixEnd_3185251 : Nat := 4983230072969 + 3 ^ 40 * 3185251 * 2
def baseEnd_3185251 : Nat := 545188256071474141504601

theorem tailTrace_3185251 : CollatzResearch.WordTrace tailWord_3185251 prefixEnd_3185251 545188256071474141504601 := by
  unfold tailWord_3185251
  simp only [CollatzResearch.WordTrace]
  refine ⟨116175648183387099406051607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77450432122258066270701071 116175648183387099406051607)
  ·
    refine ⟨174263472275080649109077411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116175648183387099406051607 174263472275080649109077411)
    ·
      refine ⟨261395208412620973663616117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174263472275080649109077411 261395208412620973663616117)
      ·
        refine ⟨24505800788683216280964011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261395208412620973663616117 24505800788683216280964011)
        ·
          refine ⟨36758701183024824421446017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24505800788683216280964011 36758701183024824421446017)
          ·
            refine ⟨27569025887268618316084513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36758701183024824421446017 27569025887268618316084513)
            ·
              refine ⟨20676769415451463737063385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27569025887268618316084513 20676769415451463737063385)
              ·
                refine ⟨15507577061588597802797539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20676769415451463737063385 15507577061588597802797539)
                ·
                  refine ⟨23261365592382896704196309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15507577061588597802797539 23261365592382896704196309)
                  ·
                    refine ⟨545188256071474141504601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23261365592382896704196309 545188256071474141504601)
                    ·
                      rfl

theorem cell23_3185251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_3185251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185251 prefixEnd_3185251 := by exact prefixLift 3185251
  have htrace : WordTrace (prefixWord ++ tailWord_3185251) baseStart_3185251 baseEnd_3185251 := by
    simpa [prefixWord, tailWord_3185251, baseEnd_3185251] using wordTrace_append hprefix tailTrace_3185251
  have hstable : (prefixWord ++ tailWord_3185251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185251).length < 2 ^ (prefixWord ++ tailWord_3185251).sum := by decide
  have hdescent : baseEnd_3185251 < baseStart_3185251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185325 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3185325 : Nat := 118140960795 + 3185325 * 2 ^ 59
def prefixEnd_3185325 : Nat := 4983230072969 + 3 ^ 40 * 3185325 * 2
def baseEnd_3185325 : Nat := 1635602765782855134988463

theorem tailTrace_3185325 : CollatzResearch.WordTrace tailWord_3185325 prefixEnd_3185325 1635602765782855134988463 := by
  unfold tailWord_3185325
  simp only [CollatzResearch.WordTrace]
  refine ⟨116178347185119010044245429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77452231456746006696163619 116178347185119010044245429)
  ·
    refine ⟨10891720048604907191648009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116178347185119010044245429 10891720048604907191648009)
    ·
      refine ⟨8168790036453680393736007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10891720048604907191648009 8168790036453680393736007)
      ·
        refine ⟨12253185054680520590604011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168790036453680393736007 12253185054680520590604011)
        ·
          refine ⟨18379777582020780885906017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12253185054680520590604011 18379777582020780885906017)
          ·
            refine ⟨13784833186515585664429513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18379777582020780885906017 13784833186515585664429513)
            ·
              refine ⟨10338624889886689248322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13784833186515585664429513 10338624889886689248322135)
              ·
                refine ⟨15507937334830033872483203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338624889886689248322135 15507937334830033872483203)
                ·
                  refine ⟨23261906002245050808724805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15507937334830033872483203 23261906002245050808724805)
                  ·
                    refine ⟨4361607375420947026635901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23261906002245050808724805 4361607375420947026635901)
                    ·
                      refine ⟨1635602765782855134988463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361607375420947026635901 1635602765782855134988463)
                      ·
                        rfl

theorem cell23_3185325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3185325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185325 prefixEnd_3185325 := by exact prefixLift 3185325
  have htrace : WordTrace (prefixWord ++ tailWord_3185325) baseStart_3185325 baseEnd_3185325 := by
    simpa [prefixWord, tailWord_3185325, baseEnd_3185325] using wordTrace_append hprefix tailTrace_3185325
  have hstable : (prefixWord ++ tailWord_3185325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185325).length < 2 ^ (prefixWord ++ tailWord_3185325).sum := by decide
  have hdescent : baseEnd_3185325 < baseStart_3185325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185375 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 1, 5]
def baseStart_3185375 : Nat := 118140960795 + 3185375 * 2 ^ 59
def prefixEnd_3185375 : Nat := 4983230072969 + 3 ^ 40 * 3185375 * 2
def baseEnd_3185375 : Nat := 545209479938526646454411

theorem tailTrace_3185375 : CollatzResearch.WordTrace tailWord_3185375 prefixEnd_3185375 545209479938526646454411 := by
  unfold tailWord_3185375
  simp only [CollatzResearch.WordTrace]
  refine ⟨116180170834937868583565579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77453447223291912389043719 116180170834937868583565579)
  ·
    refine ⟨174270256252406802875348369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116180170834937868583565579 174270256252406802875348369)
    ·
      refine ⟨130702692189305102156511277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174270256252406802875348369 130702692189305102156511277)
      ·
        refine ⟨49013509570989413308691729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130702692189305102156511277 49013509570989413308691729)
        ·
          refine ⟨36760132178242059981518797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49013509570989413308691729 36760132178242059981518797)
          ·
            refine ⟨13785049566840772493069549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36760132178242059981518797 13785049566840772493069549)
            ·
              refine ⟨5169393587565289684901081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13785049566840772493069549 5169393587565289684901081)
              ·
                refine ⟨3877045190673967263675811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5169393587565289684901081 3877045190673967263675811)
                ·
                  refine ⟨5815567786010950895513717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877045190673967263675811 5815567786010950895513717)
                  ·
                    refine ⟨545209479938526646454411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5815567786010950895513717 545209479938526646454411)
                    ·
                      rfl

theorem cell23_3185375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_3185375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185375 prefixEnd_3185375 := by exact prefixLift 3185375
  have htrace : WordTrace (prefixWord ++ tailWord_3185375) baseStart_3185375 baseEnd_3185375 := by
    simpa [prefixWord, tailWord_3185375, baseEnd_3185375] using wordTrace_append hprefix tailTrace_3185375
  have hstable : (prefixWord ++ tailWord_3185375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185375).length < 2 ^ (prefixWord ++ tailWord_3185375).sum := by decide
  have hdescent : baseEnd_3185375 < baseStart_3185375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185389 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3185389 : Nat := 118140960795 + 3185389 * 2 ^ 59
def prefixEnd_3185389 : Nat := 4983230072969 + 3 ^ 40 * 3185389 * 2
def baseEnd_3185389 : Nat := 1635635628544742884588169

theorem tailTrace_3185389 : CollatzResearch.WordTrace tailWord_3185389 prefixEnd_3185389 1635635628544742884588169 := by
  unfold tailWord_3185389
  simp only [CollatzResearch.WordTrace]
  refine ⟨116180681456887148974575221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77453787637924765983050147 116180681456887148974575221)
  ·
    refine ⟨10891938886583170216366427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116180681456887148974575221 10891938886583170216366427)
    ·
      refine ⟨16337908329874755324549641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10891938886583170216366427 16337908329874755324549641)
      ·
        refine ⟨12253431247406066493412231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16337908329874755324549641 12253431247406066493412231)
        ·
          refine ⟨18380146871109099740118347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12253431247406066493412231 18380146871109099740118347)
          ·
            refine ⟨27570220306663649610177521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18380146871109099740118347 27570220306663649610177521)
            ·
              refine ⟨20677665229997737207633141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27570220306663649610177521 20677665229997737207633141)
              ·
                refine ⟨1938531115312287863215607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20677665229997737207633141 1938531115312287863215607)
                ·
                  refine ⟨2907796672968431794823411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938531115312287863215607 2907796672968431794823411)
                  ·
                    refine ⟨4361695009452647692235117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907796672968431794823411 4361695009452647692235117)
                    ·
                      refine ⟨1635635628544742884588169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361695009452647692235117 1635635628544742884588169)
                      ·
                        rfl

theorem cell23_3185389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3185389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185389 prefixEnd_3185389 := by exact prefixLift 3185389
  have htrace : WordTrace (prefixWord ++ tailWord_3185389) baseStart_3185389 baseEnd_3185389 := by
    simpa [prefixWord, tailWord_3185389, baseEnd_3185389] using wordTrace_append hprefix tailTrace_3185389
  have hstable : (prefixWord ++ tailWord_3185389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185389).length < 2 ^ (prefixWord ++ tailWord_3185389).sum := by decide
  have hdescent : baseEnd_3185389 < baseStart_3185389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185406 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_3185406 : Nat := 118140960795 + 3185406 * 2 ^ 59
def prefixEnd_3185406 : Nat := 4983230072969 + 3 ^ 40 * 3185406 * 2
def baseEnd_3185406 : Nat := 1635644357715869318075591

theorem tailTrace_3185406 : CollatzResearch.WordTrace tailWord_3185406 prefixEnd_3185406 1635644357715869318075591 := by
  unfold tailWord_3185406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522662687228195109743009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77454200998550373918629381 14522662687228195109743009)
  ·
    refine ⟨10891997015421146332307257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14522662687228195109743009 10891997015421146332307257)
    ·
      refine ⟨8168997761565859749230443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10891997015421146332307257 8168997761565859749230443)
      ·
        refine ⟨12253496642348789623845665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168997761565859749230443 12253496642348789623845665)
        ·
          refine ⟨9190122481761592217884249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12253496642348789623845665 9190122481761592217884249)
          ·
            refine ⟨6892591861321194163413187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9190122481761592217884249 6892591861321194163413187)
            ·
              refine ⟨10338887791981791245119781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892591861321194163413187 10338887791981791245119781)
              ·
                refine ⟨1938541460996585858459959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10338887791981791245119781 1938541460996585858459959)
                ·
                  refine ⟨2907812191494878787689939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938541460996585858459959 2907812191494878787689939)
                  ·
                    refine ⟨4361718287242318181534909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2907812191494878787689939 4361718287242318181534909)
                    ·
                      refine ⟨1635644357715869318075591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361718287242318181534909 1635644357715869318075591)
                      ·
                        rfl

theorem cell23_3185406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_3185406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185406 prefixEnd_3185406 := by exact prefixLift 3185406
  have htrace : WordTrace (prefixWord ++ tailWord_3185406) baseStart_3185406 baseEnd_3185406 := by
    simpa [prefixWord, tailWord_3185406, baseEnd_3185406] using wordTrace_append hprefix tailTrace_3185406
  have hstable : (prefixWord ++ tailWord_3185406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185406).length < 2 ^ (prefixWord ++ tailWord_3185406).sum := by decide
  have hdescent : baseEnd_3185406 < baseStart_3185406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185445 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_3185445 : Nat := 118140960795 + 3185445 * 2 ^ 59
def prefixEnd_3185445 : Nat := 4983230072969 + 3 ^ 40 * 3185445 * 2
def baseEnd_3185445 : Nat := 1635664383461394665487911

theorem tailTrace_3185445 : CollatzResearch.WordTrace tailWord_3185445 prefixEnd_3185445 1635664383461394665487911 := by
  unfold tailWord_3185445
  simp only [CollatzResearch.WordTrace]
  refine ⟨116182723944684270538613789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77455149296456180359075859 116182723944684270538613789)
  ·
    refine ⟨43568521479256601451980171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116182723944684270538613789 43568521479256601451980171)
    ·
      refine ⟨65352782218884902177970257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43568521479256601451980171 65352782218884902177970257)
      ·
        refine ⟨49014586664163676633477693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65352782218884902177970257 49014586664163676633477693)
        ·
          refine ⟨18380469999061378737554135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49014586664163676633477693 18380469999061378737554135)
          ·
            refine ⟨27570704998592068106331203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18380469999061378737554135 27570704998592068106331203)
            ·
              refine ⟨41356057497888102159496805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27570704998592068106331203 41356057497888102159496805)
              ·
                refine ⟨7754260780854019154905651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41356057497888102159496805 7754260780854019154905651)
                ·
                  refine ⟨11631391171281028732358477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754260780854019154905651 11631391171281028732358477)
                  ·
                    refine ⟨4361771689230385774634429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631391171281028732358477 4361771689230385774634429)
                    ·
                      refine ⟨1635664383461394665487911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361771689230385774634429 1635664383461394665487911)
                      ·
                        rfl

theorem cell23_3185445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_3185445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185445 prefixEnd_3185445 := by exact prefixLift 3185445
  have htrace : WordTrace (prefixWord ++ tailWord_3185445) baseStart_3185445 baseEnd_3185445 := by
    simpa [prefixWord, tailWord_3185445, baseEnd_3185445] using wordTrace_append hprefix tailTrace_3185445
  have hstable : (prefixWord ++ tailWord_3185445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185445).length < 2 ^ (prefixWord ++ tailWord_3185445).sum := by decide
  have hdescent : baseEnd_3185445 < baseStart_3185445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185476 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3185476 : Nat := 118140960795 + 3185476 * 2 ^ 59
def prefixEnd_3185476 : Nat := 4983230072969 + 3 ^ 40 * 3185476 * 2
def baseEnd_3185476 : Nat := 1635680301361684044200269

theorem tailTrace_3185476 : CollatzResearch.WordTrace tailWord_3185476 prefixEnd_3185476 1635680301361684044200269 := by
  unfold tailWord_3185476
  simp only [CollatzResearch.WordTrace]
  refine ⟨58091927303785981416496141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77455903071714641888661521 58091927303785981416496141)
  ·
    refine ⟨21784472738919743031186053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58091927303785981416496141 21784472738919743031186053)
    ·
      refine ⟨4084588638547451818347385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21784472738919743031186053 4084588638547451818347385)
      ·
        refine ⟨3063441478910588863760539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084588638547451818347385 3063441478910588863760539)
        ·
          refine ⟨4595162218365883295640809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063441478910588863760539 4595162218365883295640809)
          ·
            refine ⟨3446371663774412471730607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595162218365883295640809 3446371663774412471730607)
            ·
              refine ⟨5169557495661618707595911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446371663774412471730607 5169557495661618707595911)
              ·
                refine ⟨7754336243492428061393867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169557495661618707595911 7754336243492428061393867)
                ·
                  refine ⟨11631504365238642092090801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754336243492428061393867 11631504365238642092090801)
                  ·
                    refine ⟨8723628273928981569068101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11631504365238642092090801 8723628273928981569068101)
                    ·
                      refine ⟨1635680301361684044200269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8723628273928981569068101 1635680301361684044200269)
                      ·
                        rfl

theorem cell23_3185476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3185476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185476 prefixEnd_3185476 := by exact prefixLift 3185476
  have htrace : WordTrace (prefixWord ++ tailWord_3185476) baseStart_3185476 baseEnd_3185476 := by
    simpa [prefixWord, tailWord_3185476, baseEnd_3185476] using wordTrace_append hprefix tailTrace_3185476
  have hstable : (prefixWord ++ tailWord_3185476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185476).length < 2 ^ (prefixWord ++ tailWord_3185476).sum := by decide
  have hdescent : baseEnd_3185476 < baseStart_3185476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185528 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3185528 : Nat := 118140960795 + 3185528 * 2 ^ 59
def prefixEnd_3185528 : Nat := 4983230072969 + 3 ^ 40 * 3185528 * 2
def baseEnd_3185528 : Nat := 1635707002355717840750029

theorem tailTrace_3185528 : CollatzResearch.WordTrace tailWord_3185528 prefixEnd_3185528 1635707002355717840750029 := by
  unfold tailWord_3185528
  simp only [CollatzResearch.WordTrace]
  refine ⟨58092875601691787856942619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77457167468922383809256825 58092875601691787856942619)
  ·
    refine ⟨87139313402537681785413929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58092875601691787856942619 87139313402537681785413929)
    ·
      refine ⟨65354485051903261339060447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87139313402537681785413929 65354485051903261339060447)
      ·
        refine ⟨98031727577854892008590671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65354485051903261339060447 98031727577854892008590671)
        ·
          refine ⟨147047591366782338012886007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98031727577854892008590671 147047591366782338012886007)
          ·
            refine ⟨220571387050173507019329011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147047591366782338012886007 220571387050173507019329011)
            ·
              refine ⟨330857080575260260528993517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220571387050173507019329011 330857080575260260528993517)
              ·
                refine ⟨124071405215722597698372569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330857080575260260528993517 124071405215722597698372569)
                ·
                  refine ⟨93053553911791948273779427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124071405215722597698372569 93053553911791948273779427)
                  ·
                    refine ⟨139580330867687922410669141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93053553911791948273779427 139580330867687922410669141)
                    ·
                      refine ⟨1635707002355717840750029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139580330867687922410669141 1635707002355717840750029)
                      ·
                        rfl

theorem cell23_3185528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3185528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185528 prefixEnd_3185528 := by exact prefixLift 3185528
  have htrace : WordTrace (prefixWord ++ tailWord_3185528) baseStart_3185528 baseEnd_3185528 := by
    simpa [prefixWord, tailWord_3185528, baseEnd_3185528] using wordTrace_append hprefix tailTrace_3185528
  have hstable : (prefixWord ++ tailWord_3185528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185528).length < 2 ^ (prefixWord ++ tailWord_3185528).sum := by decide
  have hdescent : baseEnd_3185528 < baseStart_3185528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185535 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_3185535 : Nat := 118140960795 + 3185535 * 2 ^ 59
def prefixEnd_3185535 : Nat := 4983230072969 + 3 ^ 40 * 3185535 * 2
def baseEnd_3185535 : Nat := 1635710596720299313362497

theorem tailTrace_3185535 : CollatzResearch.WordTrace tailWord_3185535 prefixEnd_3185535 1635710596720299313362497 := by
  unfold tailWord_3185535
  simp only [CollatzResearch.WordTrace]
  refine ⟨116186006514358215909390059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77457337676238810606260039 116186006514358215909390059)
  ·
    refine ⟨174279009771537323864085089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116186006514358215909390059 174279009771537323864085089)
    ·
      refine ⟨130709257328652992898063817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174279009771537323864085089 130709257328652992898063817)
      ·
        refine ⟨98031942996489744673547863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130709257328652992898063817 98031942996489744673547863)
        ·
          refine ⟨147047914494734617010321795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98031942996489744673547863 147047914494734617010321795)
          ·
            refine ⟨220571871742101925515482693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147047914494734617010321795 220571871742101925515482693)
            ·
              refine ⟨41357225951644111034153005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220571871742101925515482693 41357225951644111034153005)
              ·
                refine ⟨15508959731866541637807377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41357225951644111034153005 15508959731866541637807377)
                ·
                  refine ⟨11631719798899906228355533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15508959731866541637807377 11631719798899906228355533)
                  ·
                    refine ⟨4361894924587464835633325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11631719798899906228355533 4361894924587464835633325)
                    ·
                      refine ⟨1635710596720299313362497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4361894924587464835633325 1635710596720299313362497)
                      ·
                        rfl

theorem cell23_3185535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_3185535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185535 prefixEnd_3185535 := by exact prefixLift 3185535
  have htrace : WordTrace (prefixWord ++ tailWord_3185535) baseStart_3185535 baseEnd_3185535 := by
    simpa [prefixWord, tailWord_3185535, baseEnd_3185535] using wordTrace_append hprefix tailTrace_3185535
  have hstable : (prefixWord ++ tailWord_3185535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185535).length < 2 ^ (prefixWord ++ tailWord_3185535).sum := by decide
  have hdescent : baseEnd_3185535 < baseStart_3185535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185565 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3185565 : Nat := 118140960795 + 3185565 * 2 ^ 59
def prefixEnd_3185565 : Nat := 4983230072969 + 3 ^ 40 * 3185565 * 2
def baseEnd_3185565 : Nat := 1635726001139934195987359

theorem tailTrace_3185565 : CollatzResearch.WordTrace tailWord_3185565 prefixEnd_3185565 1635726001139934195987359 := by
  unfold tailWord_3185565
  simp only [CollatzResearch.WordTrace]
  refine ⟨116187100704249531032982149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77458067136166354021988099 116187100704249531032982149)
  ·
    refine ⟨21785081382046787068684153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116187100704249531032982149 21785081382046787068684153)
    ·
      refine ⟨16338811036535090301513115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21785081382046787068684153 16338811036535090301513115)
      ·
        refine ⟨24508216554802635452269673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16338811036535090301513115 24508216554802635452269673)
        ·
          refine ⟨18381162416101976589202255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24508216554802635452269673 18381162416101976589202255)
          ·
            refine ⟨27571743624152964883803383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381162416101976589202255 27571743624152964883803383)
            ·
              refine ⟨41357615436229447325705075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27571743624152964883803383 41357615436229447325705075)
              ·
                refine ⟨62036423154344170988557613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41357615436229447325705075 62036423154344170988557613)
                ·
                  refine ⟨23263658682879064120709105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62036423154344170988557613 23263658682879064120709105)
                  ·
                    refine ⟨17447744012159298090531829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23263658682879064120709105 17447744012159298090531829)
                    ·
                      refine ⟨1635726001139934195987359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17447744012159298090531829 1635726001139934195987359)
                      ·
                        rfl

theorem cell23_3185565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3185565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185565 prefixEnd_3185565 := by exact prefixLift 3185565
  have htrace : WordTrace (prefixWord ++ tailWord_3185565) baseStart_3185565 baseEnd_3185565 := by
    simpa [prefixWord, tailWord_3185565, baseEnd_3185565] using wordTrace_append hprefix tailTrace_3185565
  have hstable : (prefixWord ++ tailWord_3185565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185565).length < 2 ^ (prefixWord ++ tailWord_3185565).sum := by decide
  have hdescent : baseEnd_3185565 < baseStart_3185565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185592 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_3185592 : Nat := 118140960795 + 3185592 * 2 ^ 59
def prefixEnd_3185592 : Nat := 4983230072969 + 3 ^ 40 * 3185592 * 2
def baseEnd_3185592 : Nat := 1635739865117605590349735

theorem tailTrace_3185592 : CollatzResearch.WordTrace tailWord_3185592 prefixEnd_3185592 1635739865117605590349735 := by
  unfold tailWord_3185592
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094042737575857322107515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77458723650101143096143353 58094042737575857322107515)
  ·
    refine ⟨87141064106363785983161273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58094042737575857322107515 87141064106363785983161273)
    ·
      refine ⟨65355798079772839487370955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87141064106363785983161273 65355798079772839487370955)
      ·
        refine ⟨98033697119659259231056433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65355798079772839487370955 98033697119659259231056433)
        ·
          refine ⟨73525272839744444423292325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98033697119659259231056433 73525272839744444423292325)
          ·
            refine ⟨13785988657452083329367311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73525272839744444423292325 13785988657452083329367311)
            ·
              refine ⟨20678982986178124994050967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13785988657452083329367311 20678982986178124994050967)
              ·
                refine ⟨31018474479267187491076451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20678982986178124994050967 31018474479267187491076451)
                ·
                  refine ⟨46527711718900781236614677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31018474479267187491076451 46527711718900781236614677)
                  ·
                    refine ⟨2180986486823474120466313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46527711718900781236614677 2180986486823474120466313)
                    ·
                      refine ⟨1635739865117605590349735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2180986486823474120466313 1635739865117605590349735)
                      ·
                        rfl

theorem cell23_3185592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_3185592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185592 prefixEnd_3185592 := by exact prefixLift 3185592
  have htrace : WordTrace (prefixWord ++ tailWord_3185592) baseStart_3185592 baseEnd_3185592 := by
    simpa [prefixWord, tailWord_3185592, baseEnd_3185592] using wordTrace_append hprefix tailTrace_3185592
  have hstable : (prefixWord ++ tailWord_3185592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185592).length < 2 ^ (prefixWord ++ tailWord_3185592).sum := by decide
  have hdescent : baseEnd_3185592 < baseStart_3185592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185612 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3185612 : Nat := 118140960795 + 3185612 * 2 ^ 59
def prefixEnd_3185612 : Nat := 4983230072969 + 3 ^ 40 * 3185612 * 2
def baseEnd_3185612 : Nat := 1635750134730695512099643

theorem tailTrace_3185612 : CollatzResearch.WordTrace tailWord_3185612 prefixEnd_3185612 1635750134730695512099643 := by
  unfold tailWord_3185612
  simp only [CollatzResearch.WordTrace]
  refine ⟨58094407467539629029971545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77459209956719505373295393 58094407467539629029971545)
  ·
    refine ⟨43570805600654721772478659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58094407467539629029971545 43570805600654721772478659)
    ·
      refine ⟨65356208400982082658717989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43570805600654721772478659 65356208400982082658717989)
      ·
        refine ⟨12254289075184140498509623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65356208400982082658717989 12254289075184140498509623)
        ·
          refine ⟨18381433612776210747764435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254289075184140498509623 18381433612776210747764435)
          ·
            refine ⟨27572150419164316121646653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381433612776210747764435 27572150419164316121646653)
            ·
              refine ⟨10339556407186618545617495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27572150419164316121646653 10339556407186618545617495)
              ·
                refine ⟨15509334610779927818426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339556407186618545617495 15509334610779927818426243)
                ·
                  refine ⟨23264001916169891727639365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15509334610779927818426243 23264001916169891727639365)
                  ·
                    refine ⟨4362000359281854698932381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23264001916169891727639365 4362000359281854698932381)
                    ·
                      refine ⟨1635750134730695512099643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362000359281854698932381 1635750134730695512099643)
                      ·
                        rfl

theorem cell23_3185612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3185612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185612 prefixEnd_3185612 := by exact prefixLift 3185612
  have htrace : WordTrace (prefixWord ++ tailWord_3185612) baseStart_3185612 baseEnd_3185612 := by
    simpa [prefixWord, tailWord_3185612, baseEnd_3185612] using wordTrace_append hprefix tailTrace_3185612
  have hstable : (prefixWord ++ tailWord_3185612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185612).length < 2 ^ (prefixWord ++ tailWord_3185612).sum := by decide
  have hdescent : baseEnd_3185612 < baseStart_3185612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185635 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3185635 : Nat := 118140960795 + 3185635 * 2 ^ 59
def prefixEnd_3185635 : Nat := 4983230072969 + 3 ^ 40 * 3185635 * 2
def baseEnd_3185635 : Nat := 1635761944785748922112037

theorem tailTrace_3185635 : CollatzResearch.WordTrace tailWord_3185635 prefixEnd_3185635 1635761944785748922112037 := by
  unfold tailWord_3185635
  simp only [CollatzResearch.WordTrace]
  refine ⟨116189653813995932988030359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77459769209330621992020239 116189653813995932988030359)
  ·
    refine ⟨174284480720993899482045539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116189653813995932988030359 174284480720993899482045539)
    ·
      refine ⟨261426721081490849223068309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174284480720993899482045539 261426721081490849223068309)
      ·
        refine ⟨12254377550694883557331327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 261426721081490849223068309 12254377550694883557331327)
        ·
          refine ⟨18381566326042325335996991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12254377550694883557331327 18381566326042325335996991)
          ·
            refine ⟨27572349489063488003995487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18381566326042325335996991 27572349489063488003995487)
            ·
              refine ⟨41358524233595232005993231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27572349489063488003995487 41358524233595232005993231)
              ·
                refine ⟨62037786350392848008989847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41358524233595232005993231 62037786350392848008989847)
                ·
                  refine ⟨93056679525589272013484771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62037786350392848008989847 93056679525589272013484771)
                  ·
                    refine ⟨139585019288383908020227157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93056679525589272013484771 139585019288383908020227157)
                    ·
                      refine ⟨1635761944785748922112037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139585019288383908020227157 1635761944785748922112037)
                      ·
                        rfl

theorem cell23_3185635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3185635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185635 prefixEnd_3185635 := by exact prefixLift 3185635
  have htrace : WordTrace (prefixWord ++ tailWord_3185635) baseStart_3185635 baseEnd_3185635 := by
    simpa [prefixWord, tailWord_3185635, baseEnd_3185635] using wordTrace_append hprefix tailTrace_3185635
  have hstable : (prefixWord ++ tailWord_3185635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185635).length < 2 ^ (prefixWord ++ tailWord_3185635).sum := by decide
  have hdescent : baseEnd_3185635 < baseStart_3185635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185649 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 6]
def baseStart_3185649 : Nat := 118140960795 + 3185649 * 2 ^ 59
def prefixEnd_3185649 : Nat := 4983230072969 + 3 ^ 40 * 3185649 * 2
def baseEnd_3185649 : Nat := 181752125946101318592997

theorem tailTrace_3185649 : CollatzResearch.WordTrace tailWord_3185649 prefixEnd_3185649 181752125946101318592997 := by
  unfold tailWord_3185649
  simp only [CollatzResearch.WordTrace]
  refine ⟨116190164435945213379040001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77460109623963475586026667 116190164435945213379040001)
  ·
    refine ⟨87142623326958910034280001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116190164435945213379040001 87142623326958910034280001)
    ·
      refine ⟨65356967495219182525710001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87142623326958910034280001 65356967495219182525710001)
      ·
        refine ⟨49017725621414386894282501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65356967495219182525710001 49017725621414386894282501)
        ·
          refine ⟨9190823554015197542677969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49017725621414386894282501 9190823554015197542677969)
          ·
            refine ⟨6893117665511398157008477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9190823554015197542677969 6893117665511398157008477)
            ·
              refine ⟨2584919124566774308878179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6893117665511398157008477 2584919124566774308878179)
              ·
                refine ⟨3877378686850161463317269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584919124566774308878179 3877378686850161463317269)
                ·
                  refine ⟨181752125946101318592997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3877378686850161463317269 181752125946101318592997)
                  ·
                    rfl

theorem cell23_3185649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_3185649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185649 prefixEnd_3185649 := by exact prefixLift 3185649
  have htrace : WordTrace (prefixWord ++ tailWord_3185649) baseStart_3185649 baseEnd_3185649 := by
    simpa [prefixWord, tailWord_3185649, baseEnd_3185649] using wordTrace_append hprefix tailTrace_3185649
  have hstable : (prefixWord ++ tailWord_3185649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185649).length < 2 ^ (prefixWord ++ tailWord_3185649).sum := by decide
  have hdescent : baseEnd_3185649 < baseStart_3185649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185669 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_3185669 : Nat := 118140960795 + 3185669 * 2 ^ 59
def prefixEnd_3185669 : Nat := 4983230072969 + 3 ^ 40 * 3185669 * 2
def baseEnd_3185669 : Nat := 1635779403128001789086881

theorem tailTrace_3185669 : CollatzResearch.WordTrace tailWord_3185669 prefixEnd_3185669 1635779403128001789086881 := by
  unfold tailWord_3185669
  simp only [CollatzResearch.WordTrace]
  refine ⟨116190893895872756794768061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77460595930581837863178707 116190893895872756794768061)
  ·
    refine ⟨43571585210952283798038023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116190893895872756794768061 43571585210952283798038023)
    ·
      refine ⟨65357377816428425697057035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43571585210952283798038023 65357377816428425697057035)
      ·
        refine ⟨98036066724642638545585553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65357377816428425697057035 98036066724642638545585553)
        ·
          refine ⟨73527050043481978909189165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98036066724642638545585553 73527050043481978909189165)
          ·
            refine ⟨27572643766305742090945937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73527050043481978909189165 27572643766305742090945937)
            ·
              refine ⟨20679482824729306568209453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27572643766305742090945937 20679482824729306568209453)
              ·
                refine ⟨7754806059273489963078545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20679482824729306568209453 7754806059273489963078545)
                ·
                  refine ⟨5816104544455117472308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7754806059273489963078545 5816104544455117472308909)
                  ·
                    refine ⟨2181039204170669052115841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5816104544455117472308909 2181039204170669052115841)
                    ·
                      refine ⟨1635779403128001789086881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181039204170669052115841 1635779403128001789086881)
                      ·
                        rfl

theorem cell23_3185669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_3185669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185669 prefixEnd_3185669 := by exact prefixLift 3185669
  have htrace : WordTrace (prefixWord ++ tailWord_3185669) baseStart_3185669 baseEnd_3185669 := by
    simpa [prefixWord, tailWord_3185669, baseEnd_3185669] using wordTrace_append hprefix tailTrace_3185669
  have hstable : (prefixWord ++ tailWord_3185669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185669).length < 2 ^ (prefixWord ++ tailWord_3185669).sum := by decide
  have hdescent : baseEnd_3185669 < baseStart_3185669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185693 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3185693 : Nat := 118140960795 + 3185693 * 2 ^ 59
def prefixEnd_3185693 : Nat := 4983230072969 + 3 ^ 40 * 3185693 * 2
def baseEnd_3185693 : Nat := 1635791726663709695186771

theorem tailTrace_3185693 : CollatzResearch.WordTrace tailWord_3185693 prefixEnd_3185693 1635791726663709695186771 := by
  unfold tailWord_3185693
  simp only [CollatzResearch.WordTrace]
  refine ⟨116191769247785808893641733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77461179498523872595761155 116191769247785808893641733)
  ·
    refine ⟨21785956733959839167557825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116191769247785808893641733 21785956733959839167557825)
    ·
      refine ⟨16339467550469879375668369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21785956733959839167557825 16339467550469879375668369)
      ·
        refine ⟨12254600662852409531751277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16339467550469879375668369 12254600662852409531751277)
        ·
          refine ⟨4595475248569653574406729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12254600662852409531751277 4595475248569653574406729)
          ·
            refine ⟨3446606436427240180805047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595475248569653574406729 3446606436427240180805047)
            ·
              refine ⟨5169909654640860271207571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446606436427240180805047 5169909654640860271207571)
              ·
                refine ⟨7754864481961290406811357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5169909654640860271207571 7754864481961290406811357)
                ·
                  refine ⟨2908074180735483902554259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7754864481961290406811357 2908074180735483902554259)
                  ·
                    refine ⟨4362111271103225853831389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908074180735483902554259 4362111271103225853831389)
                    ·
                      refine ⟨1635791726663709695186771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362111271103225853831389 1635791726663709695186771)
                      ·
                        rfl

theorem cell23_3185693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3185693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185693 prefixEnd_3185693 := by exact prefixLift 3185693
  have htrace : WordTrace (prefixWord ++ tailWord_3185693) baseStart_3185693 baseEnd_3185693 := by
    simpa [prefixWord, tailWord_3185693, baseEnd_3185693] using wordTrace_append hprefix tailTrace_3185693
  have hstable : (prefixWord ++ tailWord_3185693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185693).length < 2 ^ (prefixWord ++ tailWord_3185693).sum := by decide
  have hdescent : baseEnd_3185693 < baseStart_3185693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185712 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_3185712 : Nat := 118140960795 + 3185712 * 2 ^ 59
def prefixEnd_3185712 : Nat := 4983230072969 + 3 ^ 40 * 3185712 * 2
def baseEnd_3185712 : Nat := 1635801482796145120849183

theorem tailTrace_3185712 : CollatzResearch.WordTrace tailWord_3185712 prefixEnd_3185712 1635801482796145120849183 := by
  unfold tailWord_3185712
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096231117358487569291695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77461641489811316759055593 58096231117358487569291695)
  ·
    refine ⟨87144346676037731353937543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58096231117358487569291695 87144346676037731353937543)
    ·
      refine ⟨130716520014056597030906315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87144346676037731353937543 130716520014056597030906315)
      ·
        refine ⟨196074780021084895546359473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130716520014056597030906315 196074780021084895546359473)
        ·
          refine ⟨147056085015813671659769605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196074780021084895546359473 147056085015813671659769605)
          ·
            refine ⟨27573015940465063436206801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147056085015813671659769605 27573015940465063436206801)
            ·
              refine ⟨20679761955348797577155101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27573015940465063436206801 20679761955348797577155101)
              ·
                refine ⟨7754910733255799091433163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20679761955348797577155101 7754910733255799091433163)
                ·
                  refine ⟨11632366099883698637149745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7754910733255799091433163 11632366099883698637149745)
                  ·
                    refine ⟨8724274574912773977862309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11632366099883698637149745 8724274574912773977862309)
                    ·
                      refine ⟨1635801482796145120849183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8724274574912773977862309 1635801482796145120849183)
                      ·
                        rfl

theorem cell23_3185712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_3185712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185712 prefixEnd_3185712 := by exact prefixLift 3185712
  have htrace : WordTrace (prefixWord ++ tailWord_3185712) baseStart_3185712 baseEnd_3185712 := by
    simpa [prefixWord, tailWord_3185712, baseEnd_3185712] using wordTrace_append hprefix tailTrace_3185712
  have hstable : (prefixWord ++ tailWord_3185712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185712).length < 2 ^ (prefixWord ++ tailWord_3185712).sum := by decide
  have hdescent : baseEnd_3185712 < baseStart_3185712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185716 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3185716 : Nat := 118140960795 + 3185716 * 2 ^ 59
def prefixEnd_3185716 : Nat := 4983230072969 + 3 ^ 40 * 3185716 * 2
def baseEnd_3185716 : Nat := 1635803536718763105199165

theorem tailTrace_3185716 : CollatzResearch.WordTrace tailWord_3185716 prefixEnd_3185716 1635803536718763105199165 := by
  unfold tailWord_3185716
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096304063351241910864501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77461738751134989214486001 58096304063351241910864501)
  ·
    refine ⟨5446528505939178929143547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58096304063351241910864501 5446528505939178929143547)
    ·
      refine ⟨8169792758908768393715321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5446528505939178929143547 8169792758908768393715321)
      ·
        refine ⟨6127344569181576295286491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8169792758908768393715321 6127344569181576295286491)
        ·
          refine ⟨9191016853772364442929737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127344569181576295286491 9191016853772364442929737)
          ·
            refine ⟨6893262640329273332197303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191016853772364442929737 6893262640329273332197303)
            ·
              refine ⟨10339893960493909998295955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893262640329273332197303 10339893960493909998295955)
              ·
                refine ⟨15509840940740864997443933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10339893960493909998295955 15509840940740864997443933)
                ·
                  refine ⟨5816190352777824374041475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15509840940740864997443933 5816190352777824374041475)
                  ·
                    refine ⟨8724285529166736561062213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5816190352777824374041475 8724285529166736561062213)
                    ·
                      refine ⟨1635803536718763105199165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8724285529166736561062213 1635803536718763105199165)
                      ·
                        rfl

theorem cell23_3185716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3185716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185716 prefixEnd_3185716 := by exact prefixLift 3185716
  have htrace : WordTrace (prefixWord ++ tailWord_3185716) baseStart_3185716 baseEnd_3185716 := by
    simpa [prefixWord, tailWord_3185716, baseEnd_3185716] using wordTrace_append hprefix tailTrace_3185716
  have hstable : (prefixWord ++ tailWord_3185716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185716).length < 2 ^ (prefixWord ++ tailWord_3185716).sum := by decide
  have hdescent : baseEnd_3185716 < baseStart_3185716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185736 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_3185736 : Nat := 118140960795 + 3185736 * 2 ^ 59
def prefixEnd_3185736 : Nat := 4983230072969 + 3 ^ 40 * 3185736 * 2
def baseEnd_3185736 : Nat := 1635813806331853026949073

theorem tailTrace_3185736 : CollatzResearch.WordTrace tailWord_3185736 prefixEnd_3185736 1635813806331853026949073 := by
  unfold tailWord_3185736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58096668793315013618728531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77462225057753351491638041 58096668793315013618728531)
  ·
    refine ⟨87145003189972520428092797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58096668793315013618728531 87145003189972520428092797)
    ·
      refine ⟨32679376196239695160534799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87145003189972520428092797 32679376196239695160534799)
      ·
        refine ⟨49019064294359542740802199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32679376196239695160534799 49019064294359542740802199)
        ·
          refine ⟨73528596441539314111203299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49019064294359542740802199 73528596441539314111203299)
          ·
            refine ⟨110292894662308971166804949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73528596441539314111203299 110292894662308971166804949)
            ·
              refine ⟨2584989718647866511721991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110292894662308971166804949 2584989718647866511721991)
              ·
                refine ⟨3877484577971799767582987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584989718647866511721991 3877484577971799767582987)
                ·
                  refine ⟨5816226866957699651374481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877484577971799767582987 5816226866957699651374481)
                  ·
                    refine ⟨4362170150218274738530861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816226866957699651374481 4362170150218274738530861)
                    ·
                      refine ⟨1635813806331853026949073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362170150218274738530861 1635813806331853026949073)
                      ·
                        rfl

theorem cell23_3185736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_3185736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185736 prefixEnd_3185736 := by exact prefixLift 3185736
  have htrace : WordTrace (prefixWord ++ tailWord_3185736) baseStart_3185736 baseEnd_3185736 := by
    simpa [prefixWord, tailWord_3185736, baseEnd_3185736] using wordTrace_append hprefix tailTrace_3185736
  have hstable : (prefixWord ++ tailWord_3185736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185736).length < 2 ^ (prefixWord ++ tailWord_3185736).sum := by decide
  have hdescent : baseEnd_3185736 < baseStart_3185736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185759 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 5, 3, 2]
def baseStart_3185759 : Nat := 118140960795 + 3185759 * 2 ^ 59
def prefixEnd_3185759 : Nat := 4983230072969 + 3 ^ 40 * 3185759 * 2
def baseEnd_3185759 : Nat := 1635825616386906436961467

theorem tailTrace_3185759 : CollatzResearch.WordTrace tailWord_3185759 prefixEnd_3185759 1635825616386906436961467 := by
  unfold tailWord_3185759
  simp only [CollatzResearch.WordTrace]
  refine ⟨116194176465546702165544331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77462784310364468110362887 116194176465546702165544331)
  ·
    refine ⟨174291264698320053248316497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116194176465546702165544331 174291264698320053248316497)
    ·
      refine ⟨130718448523740039936237373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174291264698320053248316497 130718448523740039936237373)
      ·
        refine ⟨49019418196402514976089015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130718448523740039936237373 49019418196402514976089015)
        ·
          refine ⟨73529127294603772464133523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49019418196402514976089015 73529127294603772464133523)
          ·
            refine ⟨110293690941905658696200285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73529127294603772464133523 110293690941905658696200285)
            ·
              refine ⟨41360134103214622011075107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110293690941905658696200285 41360134103214622011075107)
              ·
                refine ⟨62040201154821933016612661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41360134103214622011075107 62040201154821933016612661)
                ·
                  refine ⟨5816268858264556220307437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62040201154821933016612661 5816268858264556220307437)
                  ·
                    refine ⟨2181100821849208582615289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5816268858264556220307437 2181100821849208582615289)
                    ·
                      refine ⟨1635825616386906436961467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181100821849208582615289 1635825616386906436961467)
                      ·
                        rfl

theorem cell23_3185759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_3185759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185759 prefixEnd_3185759 := by exact prefixLift 3185759
  have htrace : WordTrace (prefixWord ++ tailWord_3185759) baseStart_3185759 baseEnd_3185759 := by
    simpa [prefixWord, tailWord_3185759, baseEnd_3185759] using wordTrace_append hprefix tailTrace_3185759
  have hstable : (prefixWord ++ tailWord_3185759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185759).length < 2 ^ (prefixWord ++ tailWord_3185759).sum := by decide
  have hdescent : baseEnd_3185759 < baseStart_3185759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185772 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3185772 : Nat := 118140960795 + 3185772 * 2 ^ 59
def prefixEnd_3185772 : Nat := 4983230072969 + 3 ^ 40 * 3185772 * 2
def baseEnd_3185772 : Nat := 1635832291635414886098907

theorem tailTrace_3185772 : CollatzResearch.WordTrace tailWord_3185772 prefixEnd_3185772 1635832291635414886098907 := by
  unfold tailWord_3185772
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097325307249802692883785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77463100409666403590511713 58097325307249802692883785)
  ·
    refine ⟨43572993980437352019662839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58097325307249802692883785 43572993980437352019662839)
    ·
      refine ⟨65359490970656028029494259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43572993980437352019662839 65359490970656028029494259)
      ·
        refine ⟨98039236455984042044241389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65359490970656028029494259 98039236455984042044241389)
        ·
          refine ⟨36764713670994015766590521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98039236455984042044241389 36764713670994015766590521)
          ·
            refine ⟨27573535253245511824942891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36764713670994015766590521 27573535253245511824942891)
            ·
              refine ⟨41360302879868267737414337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27573535253245511824942891 41360302879868267737414337)
              ·
                refine ⟨31020227159901200803060753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41360302879868267737414337 31020227159901200803060753)
                ·
                  refine ⟨23265170369925900602295565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31020227159901200803060753 23265170369925900602295565)
                  ·
                    refine ⟨8724438888722212725860837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23265170369925900602295565 8724438888722212725860837)
                    ·
                      refine ⟨1635832291635414886098907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8724438888722212725860837 1635832291635414886098907)
                      ·
                        rfl

theorem cell23_3185772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3185772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185772 prefixEnd_3185772 := by exact prefixLift 3185772
  have htrace : WordTrace (prefixWord ++ tailWord_3185772) baseStart_3185772 baseEnd_3185772 := by
    simpa [prefixWord, tailWord_3185772, baseEnd_3185772] using wordTrace_append hprefix tailTrace_3185772
  have hstable : (prefixWord ++ tailWord_3185772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185772).length < 2 ^ (prefixWord ++ tailWord_3185772).sum := by decide
  have hdescent : baseEnd_3185772 < baseStart_3185772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185776 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2]
def baseStart_3185776 : Nat := 118140960795 + 3185776 * 2 ^ 59
def prefixEnd_3185776 : Nat := 4983230072969 + 3 ^ 40 * 3185776 * 2
def baseEnd_3185776 : Nat := 1635834345558032870448889

theorem tailTrace_3185776 : CollatzResearch.WordTrace tailWord_3185776 prefixEnd_3185776 1635834345558032870448889 := by
  unfold tailWord_3185776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097398253242557034456591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77463197670990076045942121 58097398253242557034456591)
  ·
    refine ⟨87146097379863835551684887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58097398253242557034456591 87146097379863835551684887)
    ·
      refine ⟨130719146069795753327527331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87146097379863835551684887 130719146069795753327527331)
      ·
        refine ⟨196078719104693629991290997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130719146069795753327527331 196078719104693629991290997)
        ·
          refine ⟨18382379916065027811683531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196078719104693629991290997 18382379916065027811683531)
          ·
            refine ⟨27573569874097541717525297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18382379916065027811683531 27573569874097541717525297)
            ·
              refine ⟨20680177405573156288143973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27573569874097541717525297 20680177405573156288143973)
              ·
                refine ⟨3877533263544966804026995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20680177405573156288143973 3877533263544966804026995)
                ·
                  refine ⟨5816299895317450206040493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877533263544966804026995 5816299895317450206040493)
                  ·
                    refine ⟨2181112460744043827265185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5816299895317450206040493 2181112460744043827265185)
                    ·
                      refine ⟨1635834345558032870448889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181112460744043827265185 1635834345558032870448889)
                      ·
                        rfl

theorem cell23_3185776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2].length) (baseStart_3185776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185776 prefixEnd_3185776 := by exact prefixLift 3185776
  have htrace : WordTrace (prefixWord ++ tailWord_3185776) baseStart_3185776 baseEnd_3185776 := by
    simpa [prefixWord, tailWord_3185776, baseEnd_3185776] using wordTrace_append hprefix tailTrace_3185776
  have hstable : (prefixWord ++ tailWord_3185776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185776).length < 2 ^ (prefixWord ++ tailWord_3185776).sum := by decide
  have hdescent : baseEnd_3185776 < baseStart_3185776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185792 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_3185792 : Nat := 118140960795 + 3185792 * 2 ^ 59
def prefixEnd_3185792 : Nat := 4983230072969 + 3 ^ 40 * 3185792 * 2
def baseEnd_3185792 : Nat := 1635842561248504807848815

theorem tailTrace_3185792 : CollatzResearch.WordTrace tailWord_3185792 prefixEnd_3185792 1635842561248504807848815 := by
  unfold tailWord_3185792
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097690037213574400747815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77463586716284765867663753 58097690037213574400747815)
  ·
    refine ⟨87146535055820361601121723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58097690037213574400747815 87146535055820361601121723)
    ·
      refine ⟨130719802583730542401682585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87146535055820361601121723 130719802583730542401682585)
      ·
        refine ⟨98039851937797906801261939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130719802583730542401682585 98039851937797906801261939)
        ·
          refine ⟨147059777906696860201892909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98039851937797906801261939 147059777906696860201892909)
          ·
            refine ⟨55147416715011322575709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147059777906696860201892909 55147416715011322575709841)
            ·
              refine ⟨41360562536258491931782381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55147416715011322575709841 41360562536258491931782381)
              ·
                refine ⟨15510210951096934474418393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41360562536258491931782381 15510210951096934474418393)
                ·
                  refine ⟨11632658213322700855813795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15510210951096934474418393 11632658213322700855813795)
                  ·
                    refine ⟨17448987319984051283720693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11632658213322700855813795 17448987319984051283720693)
                    ·
                      refine ⟨1635842561248504807848815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17448987319984051283720693 1635842561248504807848815)
                      ·
                        rfl

theorem cell23_3185792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_3185792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185792 prefixEnd_3185792 := by exact prefixLift 3185792
  have htrace : WordTrace (prefixWord ++ tailWord_3185792) baseStart_3185792 baseEnd_3185792 := by
    simpa [prefixWord, tailWord_3185792, baseEnd_3185792] using wordTrace_append hprefix tailTrace_3185792
  have hstable : (prefixWord ++ tailWord_3185792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185792).length < 2 ^ (prefixWord ++ tailWord_3185792).sum := by decide
  have hdescent : baseEnd_3185792 < baseStart_3185792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185793 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_3185793 : Nat := 118140960795 + 3185793 * 2 ^ 59
def prefixEnd_3185793 : Nat := 4983230072969 + 3 ^ 40 * 3185793 * 2
def baseEnd_3185793 : Nat := 1635843074729159303936311

theorem tailTrace_3185793 : CollatzResearch.WordTrace tailWord_3185793 prefixEnd_3185793 1635843074729159303936311 := by
  unfold tailWord_3185793
  simp only [CollatzResearch.WordTrace]
  refine ⟨116195416547423525972282033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77463611031615683981521355 116195416547423525972282033)
  ·
    refine ⟨87146562410567644479211525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116195416547423525972282033 87146562410567644479211525)
    ·
      refine ⟨16339980451981433339852161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87146562410567644479211525 16339980451981433339852161)
      ·
        refine ⟨12254985338986075004889121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16339980451981433339852161 12254985338986075004889121)
        ·
          refine ⟨9191239004239556253666841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12254985338986075004889121 9191239004239556253666841)
          ·
            refine ⟨6893429253179667190250131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191239004239556253666841 6893429253179667190250131)
            ·
              refine ⟨10340143879769500785375197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893429253179667190250131 10340143879769500785375197)
              ·
                refine ⟨3877553954913562794515699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10340143879769500785375197 3877553954913562794515699)
                ·
                  refine ⟨5816330932370344191773549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877553954913562794515699 5816330932370344191773549)
                  ·
                    refine ⟨2181124099638879071915081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5816330932370344191773549 2181124099638879071915081)
                    ·
                      refine ⟨1635843074729159303936311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181124099638879071915081 1635843074729159303936311)
                      ·
                        rfl

theorem cell23_3185793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_3185793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185793 prefixEnd_3185793 := by exact prefixLift 3185793
  have htrace : WordTrace (prefixWord ++ tailWord_3185793) baseStart_3185793 baseEnd_3185793 := by
    simpa [prefixWord, tailWord_3185793, baseEnd_3185793] using wordTrace_append hprefix tailTrace_3185793
  have hstable : (prefixWord ++ tailWord_3185793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185793).length < 2 ^ (prefixWord ++ tailWord_3185793).sum := by decide
  have hdescent : baseEnd_3185793 < baseStart_3185793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185800 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3185800 : Nat := 118140960795 + 3185800 * 2 ^ 59
def prefixEnd_3185800 : Nat := 4983230072969 + 3 ^ 40 * 3185800 * 2
def baseEnd_3185800 : Nat := 1635846669093740776548779

theorem tailTrace_3185800 : CollatzResearch.WordTrace tailWord_3185800 prefixEnd_3185800 1635846669093740776548779 := by
  unfold tailWord_3185800
  simp only [CollatzResearch.WordTrace]
  refine ⟨58097835929199083083893427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77463781238932110778524569 58097835929199083083893427)
  ·
    refine ⟨87146753893798624625840141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58097835929199083083893427 87146753893798624625840141)
    ·
      refine ⟨32680032710174484234690053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87146753893798624625840141 32680032710174484234690053)
      ·
        refine ⟨6127506133157715794004385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32680032710174484234690053 6127506133157715794004385)
        ·
          refine ⟨4595629599868286845503289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127506133157715794004385 4595629599868286845503289)
          ·
            refine ⟨3446722199901215134127467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595629599868286845503289 3446722199901215134127467)
            ·
              refine ⟨5170083299851822701191201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446722199901215134127467 5170083299851822701191201)
              ·
                refine ⟨3877562474888867025893401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170083299851822701191201 3877562474888867025893401)
                ·
                  refine ⟨2908171856166650269420051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877562474888867025893401 2908171856166650269420051)
                  ·
                    refine ⟨4362257784249975404130077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908171856166650269420051 4362257784249975404130077)
                    ·
                      refine ⟨1635846669093740776548779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362257784249975404130077 1635846669093740776548779)
                      ·
                        rfl

theorem cell23_3185800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3185800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185800 prefixEnd_3185800 := by exact prefixLift 3185800
  have htrace : WordTrace (prefixWord ++ tailWord_3185800) baseStart_3185800 baseEnd_3185800 := by
    simpa [prefixWord, tailWord_3185800, baseEnd_3185800] using wordTrace_append hprefix tailTrace_3185800
  have hstable : (prefixWord ++ tailWord_3185800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185800).length < 2 ^ (prefixWord ++ tailWord_3185800).sum := by decide
  have hdescent : baseEnd_3185800 < baseStart_3185800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185896 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3185896 : Nat := 118140960795 + 3185896 * 2 ^ 59
def prefixEnd_3185896 : Nat := 4983230072969 + 3 ^ 40 * 3185896 * 2
def baseEnd_3185896 : Nat := 1635895963236572400948337

theorem tailTrace_3185896 : CollatzResearch.WordTrace tailWord_3185896 prefixEnd_3185896 1635895963236572400948337 := by
  unfold tailWord_3185896
  simp only [CollatzResearch.WordTrace]
  refine ⟨58099586633025187281640771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77466115510700249708854361 58099586633025187281640771)
  ·
    refine ⟨87149379949537780922461157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58099586633025187281640771 87149379949537780922461157)
    ·
      refine ⟨16340508740538333922961467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87149379949537780922461157 16340508740538333922961467)
      ·
        refine ⟨24510763110807500884442201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16340508740538333922961467 24510763110807500884442201)
        ·
          refine ⟨18383072333105625663331651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24510763110807500884442201 18383072333105625663331651)
          ·
            refine ⟨27574608499658438494997477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18383072333105625663331651 27574608499658438494997477)
            ·
              refine ⟨5170239093685957217812027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27574608499658438494997477 5170239093685957217812027)
              ·
                refine ⟨7755358640528935826718041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170239093685957217812027 7755358640528935826718041)
                ·
                  refine ⟨5816518980396701870038531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7755358640528935826718041 5816518980396701870038531)
                  ·
                    refine ⟨8724778470595052805057797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5816518980396701870038531 8724778470595052805057797)
                    ·
                      refine ⟨1635895963236572400948337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8724778470595052805057797 1635895963236572400948337)
                      ·
                        rfl

theorem cell23_3185896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3185896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185896 prefixEnd_3185896 := by exact prefixLift 3185896
  have htrace : WordTrace (prefixWord ++ tailWord_3185896) baseStart_3185896 baseEnd_3185896 := by
    simpa [prefixWord, tailWord_3185896, baseEnd_3185896] using wordTrace_append hprefix tailTrace_3185896
  have hstable : (prefixWord ++ tailWord_3185896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185896).length < 2 ^ (prefixWord ++ tailWord_3185896).sum := by decide
  have hdescent : baseEnd_3185896 < baseStart_3185896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185919 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 6]
def baseStart_3185919 : Nat := 118140960795 + 3185919 * 2 ^ 59
def prefixEnd_3185919 : Nat := 4983230072969 + 3 ^ 40 * 3185919 * 2
def baseEnd_3185919 : Nat := 181767530365736201217859

theorem tailTrace_3185919 : CollatzResearch.WordTrace tailWord_3185919 prefixEnd_3185919 181767530365736201217859 := by
  unfold tailWord_3185919
  simp only [CollatzResearch.WordTrace]
  refine ⟨116200012144967049491368811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77466674763311366327579207 116200012144967049491368811)
  ·
    refine ⟨174300018217450574237053217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116200012144967049491368811 174300018217450574237053217)
    ·
      refine ⟨130725013663087930677789913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174300018217450574237053217 130725013663087930677789913)
      ·
        refine ⟨98043760247315948008342435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130725013663087930677789913 98043760247315948008342435)
        ·
          refine ⟨147065640370973922012513653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98043760247315948008342435 147065640370973922012513653)
          ·
            refine ⟨13787403784778805188673155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147065640370973922012513653 13787403784778805188673155)
            ·
              refine ⟨20681105677168207783009733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13787403784778805188673155 20681105677168207783009733)
              ·
                refine ⟨3877707314469038959314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20681105677168207783009733 3877707314469038959314325)
                ·
                  refine ⟨181767530365736201217859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3877707314469038959314325 181767530365736201217859)
                  ·
                    rfl

theorem cell23_3185919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 6].length) (baseStart_3185919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185919 prefixEnd_3185919 := by exact prefixLift 3185919
  have htrace : WordTrace (prefixWord ++ tailWord_3185919) baseStart_3185919 baseEnd_3185919 := by
    simpa [prefixWord, tailWord_3185919, baseEnd_3185919] using wordTrace_append hprefix tailTrace_3185919
  have hstable : (prefixWord ++ tailWord_3185919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185919).length < 2 ^ (prefixWord ++ tailWord_3185919).sum := by decide
  have hdescent : baseEnd_3185919 < baseStart_3185919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185923 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 1, 4]
def baseStart_3185923 : Nat := 118140960795 + 3185923 * 2 ^ 59
def prefixEnd_3185923 : Nat := 4983230072969 + 3 ^ 40 * 3185923 * 2
def baseEnd_3185923 : Nat := 545303275738081265103571

theorem tailTrace_3185923 : CollatzResearch.WordTrace tailWord_3185923 prefixEnd_3185923 545303275738081265103571 := by
  unfold tailWord_3185923
  simp only [CollatzResearch.WordTrace]
  refine ⟨116200158036952558174514423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77466772024635038783009615 116200158036952558174514423)
  ·
    refine ⟨174300237055428837261771635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116200158036952558174514423 174300237055428837261771635)
    ·
      refine ⟨261450355583143255892657453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174300237055428837261771635 261450355583143255892657453)
      ·
        refine ⟨98043883343678720959746545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261450355583143255892657453 98043883343678720959746545)
        ·
          refine ⟨73532912507759040719809909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98043883343678720959746545 73532912507759040719809909)
          ·
            refine ⟨6893710547602410067482179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73532912507759040719809909 6893710547602410067482179)
            ·
              refine ⟨10340565821403615101223269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893710547602410067482179 10340565821403615101223269)
              ·
                refine ⟨1938856091513177831479363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10340565821403615101223269 1938856091513177831479363)
                ·
                  refine ⟨2908284137269766747219045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938856091513177831479363 2908284137269766747219045)
                  ·
                    refine ⟨545303275738081265103571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908284137269766747219045 545303275738081265103571)
                    ·
                      rfl

theorem cell23_3185923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 4].length) (baseStart_3185923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185923 prefixEnd_3185923 := by exact prefixLift 3185923
  have htrace : WordTrace (prefixWord ++ tailWord_3185923) baseStart_3185923 baseEnd_3185923 := by
    simpa [prefixWord, tailWord_3185923, baseEnd_3185923] using wordTrace_append hprefix tailTrace_3185923
  have hstable : (prefixWord ++ tailWord_3185923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185923).length < 2 ^ (prefixWord ++ tailWord_3185923).sum := by decide
  have hdescent : baseEnd_3185923 < baseStart_3185923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185950 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3185950 : Nat := 118140960795 + 3185950 * 2 ^ 59
def prefixEnd_3185950 : Nat := 4983230072969 + 3 ^ 40 * 3185950 * 2
def baseEnd_3185950 : Nat := 1635923691191915189673089

theorem tailTrace_3185950 : CollatzResearch.WordTrace tailWord_3185950 prefixEnd_3185950 1635923691191915189673089 := by
  unfold tailWord_3185950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525142850981842723218413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77467428538569827857164869 14525142850981842723218413)
  ·
    refine ⟨5446928569118191021206905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14525142850981842723218413 5446928569118191021206905)
    ·
      refine ⟨4085196426838643265905179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5446928569118191021206905 4085196426838643265905179)
      ·
        refine ⟨6127794640257964898857769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085196426838643265905179 6127794640257964898857769)
        ·
          refine ⟨4595845980193473674143327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127794640257964898857769 4595845980193473674143327)
          ·
            refine ⟨6893768970290210511214991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595845980193473674143327 6893768970290210511214991)
            ·
              refine ⟨10340653455435315766822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893768970290210511214991 10340653455435315766822487)
              ·
                refine ⟨15510980183152973650233731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10340653455435315766822487 15510980183152973650233731)
                ·
                  refine ⟨23266470274729460475350597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15510980183152973650233731 23266470274729460475350597)
                  ·
                    refine ⟨4362463176511773839128237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23266470274729460475350597 4362463176511773839128237)
                    ·
                      refine ⟨1635923691191915189673089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362463176511773839128237 1635923691191915189673089)
                      ·
                        rfl

theorem cell23_3185950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3185950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185950 prefixEnd_3185950 := by exact prefixLift 3185950
  have htrace : WordTrace (prefixWord ++ tailWord_3185950) baseStart_3185950 baseEnd_3185950 := by
    simpa [prefixWord, tailWord_3185950, baseEnd_3185950] using wordTrace_append hprefix tailTrace_3185950
  have hstable : (prefixWord ++ tailWord_3185950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185950).length < 2 ^ (prefixWord ++ tailWord_3185950).sum := by decide
  have hdescent : baseEnd_3185950 < baseStart_3185950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185980 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_3185980 : Nat := 118140960795 + 3185980 * 2 ^ 59
def prefixEnd_3185980 : Nat := 4983230072969 + 3 ^ 40 * 3185980 * 2
def baseEnd_3185980 : Nat := 1635939095611550072297951

theorem tailTrace_3185980 : CollatzResearch.WordTrace tailWord_3185980 prefixEnd_3185980 1635939095611550072297951 := by
  unfold tailWord_3185980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58101118498873028454669697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77468157998497371272892929 58101118498873028454669697)
  ·
    refine ⟨43575838874154771341002273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58101118498873028454669697 43575838874154771341002273)
    ·
      refine ⟨32681879155616078505751705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43575838874154771341002273 32681879155616078505751705)
      ·
        refine ⟨24511409366712058879313779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32681879155616078505751705 24511409366712058879313779)
        ·
          refine ⟨36767114050068088318970669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24511409366712058879313779 36767114050068088318970669)
          ·
            refine ⟨13787667768775533119614001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36767114050068088318970669 13787667768775533119614001)
            ·
              refine ⟨10340750826581649839710501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13787667768775533119614001 10340750826581649839710501)
              ·
                refine ⟨1938890779984059344945719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10340750826581649839710501 1938890779984059344945719)
                ·
                  refine ⟨2908336169976089017418579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938890779984059344945719 2908336169976089017418579)
                  ·
                    refine ⟨4362504254964133526127869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908336169976089017418579 4362504254964133526127869)
                    ·
                      refine ⟨1635939095611550072297951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362504254964133526127869 1635939095611550072297951)
                      ·
                        rfl

theorem cell23_3185980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_3185980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185980 prefixEnd_3185980 := by exact prefixLift 3185980
  have htrace : WordTrace (prefixWord ++ tailWord_3185980) baseStart_3185980 baseEnd_3185980 := by
    simpa [prefixWord, tailWord_3185980, baseEnd_3185980] using wordTrace_append hprefix tailTrace_3185980
  have hstable : (prefixWord ++ tailWord_3185980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185980).length < 2 ^ (prefixWord ++ tailWord_3185980).sum := by decide
  have hdescent : baseEnd_3185980 < baseStart_3185980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3185996 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_3185996 : Nat := 118140960795 + 3185996 * 2 ^ 59
def prefixEnd_3185996 : Nat := 4983230072969 + 3 ^ 40 * 3185996 * 2
def baseEnd_3185996 : Nat := 545315770434007336565959

theorem tailTrace_3185996 : CollatzResearch.WordTrace tailWord_3185996 prefixEnd_3185996 545315770434007336565959 := by
  unfold tailWord_3185996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58101410282844045820960921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77468547043792061094614561 58101410282844045820960921)
  ·
    refine ⟨43576057712133034365720691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58101410282844045820960921 43576057712133034365720691)
    ·
      refine ⟨65364086568199551548581037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43576057712133034365720691 65364086568199551548581037)
      ·
        refine ⟨24511532463074831830717889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65364086568199551548581037 24511532463074831830717889)
        ·
          refine ⟨18383649347306123873038417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24511532463074831830717889 18383649347306123873038417)
          ·
            refine ⟨13787737010479592904778813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18383649347306123873038417 13787737010479592904778813)
            ·
              refine ⟨5170401378929847339292055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13787737010479592904778813 5170401378929847339292055)
              ·
                refine ⟨7755602068394771008938083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170401378929847339292055 7755602068394771008938083)
                ·
                  refine ⟨11633403102592156513407125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755602068394771008938083 11633403102592156513407125)
                  ·
                    refine ⟨545315770434007336565959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11633403102592156513407125 545315770434007336565959)
                    ·
                      rfl

theorem cell23_3185996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_3185996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3185996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3185996 prefixEnd_3185996 := by exact prefixLift 3185996
  have htrace : WordTrace (prefixWord ++ tailWord_3185996) baseStart_3185996 baseEnd_3185996 := by
    simpa [prefixWord, tailWord_3185996, baseEnd_3185996] using wordTrace_append hprefix tailTrace_3185996
  have hstable : (prefixWord ++ tailWord_3185996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3185996).length < 2 ^ (prefixWord ++ tailWord_3185996).sum := by decide
  have hdescent : baseEnd_3185996 < baseStart_3185996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3185996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186003 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 3, 2, 2]
def baseStart_3186003 : Nat := 118140960795 + 3186003 * 2 ^ 59
def prefixEnd_3186003 : Nat := 4983230072969 + 3 ^ 40 * 3186003 * 2
def baseEnd_3186003 : Nat := 1635950905666603482310345

theorem tailTrace_3186003 : CollatzResearch.WordTrace tailWord_3186003 prefixEnd_3186003 1635950905666603482310345 := by
  unfold tailWord_3186003
  simp only [CollatzResearch.WordTrace]
  refine ⟨116203075876662731837426663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77468717251108487891617775 116203075876662731837426663)
  ·
    refine ⟨174304613814994097756139995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116203075876662731837426663 174304613814994097756139995)
    ·
      refine ⟨261456920722491146634209993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174304613814994097756139995 261456920722491146634209993)
      ·
        refine ⟨196092690541868359975657495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261456920722491146634209993 196092690541868359975657495)
        ·
          refine ⟨294139035812802539963486243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196092690541868359975657495 294139035812802539963486243)
          ·
            refine ⟨441208553719203809945229365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294139035812802539963486243 441208553719203809945229365)
            ·
              refine ⟨41363301911175357182365253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441208553719203809945229365 41363301911175357182365253)
              ·
                refine ⟨7755619108345379471693485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41363301911175357182365253 7755619108345379471693485)
                ·
                  refine ⟨2908357165629517301885057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7755619108345379471693485 2908357165629517301885057)
                  ·
                    refine ⟨2181267874222137976413793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908357165629517301885057 2181267874222137976413793)
                    ·
                      refine ⟨1635950905666603482310345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181267874222137976413793 1635950905666603482310345)
                      ·
                        rfl

theorem cell23_3186003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3, 2, 2].length) (baseStart_3186003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186003 prefixEnd_3186003 := by exact prefixLift 3186003
  have htrace : WordTrace (prefixWord ++ tailWord_3186003) baseStart_3186003 baseEnd_3186003 := by
    simpa [prefixWord, tailWord_3186003, baseEnd_3186003] using wordTrace_append hprefix tailTrace_3186003
  have hstable : (prefixWord ++ tailWord_3186003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186003).length < 2 ^ (prefixWord ++ tailWord_3186003).sum := by decide
  have hdescent : baseEnd_3186003 < baseStart_3186003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186023 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3186023 : Nat := 118140960795 + 3186023 * 2 ^ 59
def prefixEnd_3186023 : Nat := 4983230072969 + 3 ^ 40 * 3186023 * 2
def baseEnd_3186023 : Nat := 1635961175279693404060253

theorem tailTrace_3186023 : CollatzResearch.WordTrace tailWord_3186023 prefixEnd_3186023 1635961175279693404060253 := by
  unfold tailWord_3186023
  simp only [CollatzResearch.WordTrace]
  refine ⟨116203805336590275253154723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77469203557726850168769815 116203805336590275253154723)
  ·
    refine ⟨174305708004885412879732085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116203805336590275253154723 174305708004885412879732085)
    ·
      refine ⟨16341160125458007457474883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174305708004885412879732085 16341160125458007457474883)
      ·
        refine ⟨24511740188187011186212325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16341160125458007457474883 24511740188187011186212325)
        ·
          refine ⟨4595951285285064597414811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24511740188187011186212325 4595951285285064597414811)
          ·
            refine ⟨6893926927927596896122217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595951285285064597414811 6893926927927596896122217)
            ·
              refine ⟨5170445195945697672091663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893926927927596896122217 5170445195945697672091663)
              ·
                refine ⟨7755667793918546508137495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170445195945697672091663 7755667793918546508137495)
                ·
                  refine ⟨11633501690877819762206243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7755667793918546508137495 11633501690877819762206243)
                  ·
                    refine ⟨17450252536316729643309365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11633501690877819762206243 17450252536316729643309365)
                    ·
                      refine ⟨1635961175279693404060253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17450252536316729643309365 1635961175279693404060253)
                      ·
                        rfl

theorem cell23_3186023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3186023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186023 prefixEnd_3186023 := by exact prefixLift 3186023
  have htrace : WordTrace (prefixWord ++ tailWord_3186023) baseStart_3186023 baseEnd_3186023 := by
    simpa [prefixWord, tailWord_3186023, baseEnd_3186023] using wordTrace_append hprefix tailTrace_3186023
  have hstable : (prefixWord ++ tailWord_3186023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186023).length < 2 ^ (prefixWord ++ tailWord_3186023).sum := by decide
  have hdescent : baseEnd_3186023 < baseStart_3186023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186039 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 7]
def baseStart_3186039 : Nat := 118140960795 + 3186039 * 2 ^ 59
def prefixEnd_3186039 : Nat := 4983230072969 + 3 ^ 40 * 3186039 * 2
def baseEnd_3186039 : Nat := 545323130323388447153393

theorem tailTrace_3186039 : CollatzResearch.WordTrace tailWord_3186039 prefixEnd_3186039 545323130323388447153393 := by
  unfold tailWord_3186039
  simp only [CollatzResearch.WordTrace]
  refine ⟨116204388904532309985737171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77469592603021539990491447 116204388904532309985737171)
  ·
    refine ⟨174306583356798464978605757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116204388904532309985737171 174306583356798464978605757)
    ·
      refine ⟨65364968758799424366977159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174306583356798464978605757 65364968758799424366977159)
      ·
        refine ⟨98047453138199136550465739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65364968758799424366977159 98047453138199136550465739)
        ·
          refine ⟨147071179707298704825698609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98047453138199136550465739 147071179707298704825698609)
          ·
            refine ⟨110303384780474028619273957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147071179707298704825698609 110303384780474028619273957)
            ·
              refine ⟨20681884646338880366113867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110303384780474028619273957 20681884646338880366113867)
              ·
                refine ⟨31022826969508320549170801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20681884646338880366113867 31022826969508320549170801)
                ·
                  refine ⟨23267120227131240411878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31022826969508320549170801 23267120227131240411878101)
                  ·
                    refine ⟨545323130323388447153393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23267120227131240411878101 545323130323388447153393)
                    ·
                      rfl

theorem cell23_3186039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_3186039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186039 prefixEnd_3186039 := by exact prefixLift 3186039
  have htrace : WordTrace (prefixWord ++ tailWord_3186039) baseStart_3186039 baseEnd_3186039 := by
    simpa [prefixWord, tailWord_3186039, baseEnd_3186039] using wordTrace_append hprefix tailTrace_3186039
  have hstable : (prefixWord ++ tailWord_3186039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186039).length < 2 ^ (prefixWord ++ tailWord_3186039).sum := by decide
  have hdescent : baseEnd_3186039 < baseStart_3186039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186057 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 1, 2, 3]
def baseStart_3186057 : Nat := 118140960795 + 3186057 * 2 ^ 59
def prefixEnd_3186057 : Nat := 4983230072969 + 3 ^ 40 * 3186057 * 2
def baseEnd_3186057 : Nat := 1635978633621946271035097

theorem tailTrace_3186057 : CollatzResearch.WordTrace tailWord_3186057 prefixEnd_3186057 1635978633621946271035097 := by
  unfold tailWord_3186057
  simp only [CollatzResearch.WordTrace]
  refine ⟨116205045418467099059892425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77470030278978066039928283 116205045418467099059892425)
  ·
    refine ⟨87153784063850324294919319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116205045418467099059892425 87153784063850324294919319)
    ·
      refine ⟨130730676095775486442378979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87153784063850324294919319 130730676095775486442378979)
      ·
        refine ⟨196096014143663229663568469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130730676095775486442378979 196096014143663229663568469)
        ·
          refine ⟨2298000165746053472619943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 196096014143663229663568469 2298000165746053472619943)
          ·
            refine ⟨3447000248619080208929915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298000165746053472619943 3447000248619080208929915)
            ·
              refine ⟨5170500372928620313394873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447000248619080208929915 5170500372928620313394873)
              ·
                refine ⟨3877875279696465235046155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170500372928620313394873 3877875279696465235046155)
                ·
                  refine ⟨5816812919544697852569233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3877875279696465235046155 5816812919544697852569233)
                  ·
                    refine ⟨4362609689658523389426925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5816812919544697852569233 4362609689658523389426925)
                    ·
                      refine ⟨1635978633621946271035097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362609689658523389426925 1635978633621946271035097)
                      ·
                        rfl

theorem cell23_3186057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 2, 3].length) (baseStart_3186057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186057 prefixEnd_3186057 := by exact prefixLift 3186057
  have htrace : WordTrace (prefixWord ++ tailWord_3186057) baseStart_3186057 baseEnd_3186057 := by
    simpa [prefixWord, tailWord_3186057, baseEnd_3186057] using wordTrace_append hprefix tailTrace_3186057
  have hstable : (prefixWord ++ tailWord_3186057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186057).length < 2 ^ (prefixWord ++ tailWord_3186057).sum := by decide
  have hdescent : baseEnd_3186057 < baseStart_3186057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186088 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3186088 : Nat := 118140960795 + 3186088 * 2 ^ 59
def prefixEnd_3186088 : Nat := 4983230072969 + 3 ^ 40 * 3186088 * 2
def baseEnd_3186088 : Nat := 1635994551522235649747455

theorem tailTrace_3186088 : CollatzResearch.WordTrace tailWord_3186088 prefixEnd_3186088 1635994551522235649747455 := by
  unfold tailWord_3186088
  simp only [CollatzResearch.WordTrace]
  refine ⟨58103088040677395677135459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77470784054236527569513945 58103088040677395677135459)
  ·
    refine ⟨87154632061016093515703189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58103088040677395677135459 87154632061016093515703189)
    ·
      refine ⟨4085373377860129383548587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87154632061016093515703189 4085373377860129383548587)
      ·
        refine ⟨6128060066790194075322881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085373377860129383548587 6128060066790194075322881)
        ·
          refine ⟨4596045050092645556492161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128060066790194075322881 4596045050092645556492161)
          ·
            refine ⟨3447033787569484167369121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596045050092645556492161 3447033787569484167369121)
            ·
              refine ⟨2585275340677113125526841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3447033787569484167369121 2585275340677113125526841)
              ·
                refine ⟨1938956505507834844145131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585275340677113125526841 1938956505507834844145131)
                ·
                  refine ⟨2908434758261752266217697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938956505507834844145131 2908434758261752266217697)
                  ·
                    refine ⟨2181326068696314199663273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908434758261752266217697 2181326068696314199663273)
                    ·
                      refine ⟨1635994551522235649747455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181326068696314199663273 1635994551522235649747455)
                      ·
                        rfl

theorem cell23_3186088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3186088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186088 prefixEnd_3186088 := by exact prefixLift 3186088
  have htrace : WordTrace (prefixWord ++ tailWord_3186088) baseStart_3186088 baseEnd_3186088 := by
    simpa [prefixWord, tailWord_3186088, baseEnd_3186088] using wordTrace_append hprefix tailTrace_3186088
  have hstable : (prefixWord ++ tailWord_3186088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186088).length < 2 ^ (prefixWord ++ tailWord_3186088).sum := by decide
  have hdescent : baseEnd_3186088 < baseStart_3186088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3186089 : Nat := 118140960795 + 3186089 * 2 ^ 59
def prefixEnd_3186089 : Nat := 4983230072969 + 3 ^ 40 * 3186089 * 2
def baseEnd_3186089 : Nat := 1635995065002890145834949

theorem tailTrace_3186089 : CollatzResearch.WordTrace tailWord_3186089 prefixEnd_3186089 1635995065002890145834949 := by
  unfold tailWord_3186089
  simp only [CollatzResearch.WordTrace]
  refine ⟨116206212554351168525057321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77470808369567445683371547 116206212554351168525057321)
  ·
    refine ⟨87154659415763376393792991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116206212554351168525057321 87154659415763376393792991)
    ·
      refine ⟨130731989123645064590689487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87154659415763376393792991 130731989123645064590689487)
      ·
        refine ⟨196097983685467596886034231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130731989123645064590689487 196097983685467596886034231)
        ·
          refine ⟨294146975528201395329051347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196097983685467596886034231 294146975528201395329051347)
          ·
            refine ⟨441220463292302092993577021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294146975528201395329051347 441220463292302092993577021)
            ·
              refine ⟨165457673734613284872591383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441220463292302092993577021 165457673734613284872591383)
              ·
                refine ⟨248186510601919927308887075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165457673734613284872591383 248186510601919927308887075)
                ·
                  refine ⟨372279765902879890963330613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248186510601919927308887075 372279765902879890963330613)
                  ·
                    refine ⟨34901228053394989777812245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 372279765902879890963330613 34901228053394989777812245)
                    ·
                      refine ⟨1635995065002890145834949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34901228053394989777812245 1635995065002890145834949)
                      ·
                        rfl

theorem cell23_3186089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3186089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186089 prefixEnd_3186089 := by exact prefixLift 3186089
  have htrace : WordTrace (prefixWord ++ tailWord_3186089) baseStart_3186089 baseEnd_3186089 := by
    simpa [prefixWord, tailWord_3186089, baseEnd_3186089] using wordTrace_append hprefix tailTrace_3186089
  have hstable : (prefixWord ++ tailWord_3186089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186089).length < 2 ^ (prefixWord ++ tailWord_3186089).sum := by decide
  have hdescent : baseEnd_3186089 < baseStart_3186089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186093 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3186093 : Nat := 118140960795 + 3186093 * 2 ^ 59
def prefixEnd_3186093 : Nat := 4983230072969 + 3 ^ 40 * 3186093 * 2
def baseEnd_3186093 : Nat := 1635997118925508130184931

theorem tailTrace_3186093 : CollatzResearch.WordTrace tailWord_3186093 prefixEnd_3186093 1635997118925508130184931 := by
  unfold tailWord_3186093
  simp only [CollatzResearch.WordTrace]
  refine ⟨116206358446336677208202933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77470905630891118138801955 116206358446336677208202933)
  ·
    refine ⟨10894346104344063488269025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116206358446336677208202933 10894346104344063488269025)
    ·
      refine ⟨8170759578258047616201769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10894346104344063488269025 8170759578258047616201769)
      ·
        refine ⟨6128069683693535712151327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8170759578258047616201769 6128069683693535712151327)
        ·
          refine ⟨9192104525540303568226991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6128069683693535712151327 9192104525540303568226991)
          ·
            refine ⟨13788156788310455352340487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192104525540303568226991 13788156788310455352340487)
            ·
              refine ⟨20682235182465683028510731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13788156788310455352340487 20682235182465683028510731)
              ·
                refine ⟨31023352773698524542766097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20682235182465683028510731 31023352773698524542766097)
                ·
                  refine ⟨23267514580273893407074573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31023352773698524542766097 23267514580273893407074573)
                  ·
                    refine ⟨8725317967602710027652965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23267514580273893407074573 8725317967602710027652965)
                    ·
                      refine ⟨1635997118925508130184931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725317967602710027652965 1635997118925508130184931)
                      ·
                        rfl

theorem cell23_3186093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3186093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186093 prefixEnd_3186093 := by exact prefixLift 3186093
  have htrace : WordTrace (prefixWord ++ tailWord_3186093) baseStart_3186093 baseEnd_3186093 := by
    simpa [prefixWord, tailWord_3186093, baseEnd_3186093] using wordTrace_append hprefix tailTrace_3186093
  have hstable : (prefixWord ++ tailWord_3186093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186093).length < 2 ^ (prefixWord ++ tailWord_3186093).sum := by decide
  have hdescent : baseEnd_3186093 < baseStart_3186093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186099 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 11]
def baseStart_3186099 : Nat := 118140960795 + 3186099 * 2 ^ 59
def prefixEnd_3186099 : Nat := 4983230072969 + 3 ^ 40 * 3186099 * 2
def baseEnd_3186099 : Nat := 181777799978826122967767

theorem tailTrace_3186099 : CollatzResearch.WordTrace tailWord_3186099 prefixEnd_3186099 181777799978826122967767 := by
  unfold tailWord_3186099
  simp only [CollatzResearch.WordTrace]
  refine ⟨116206577284314940232921351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77471051522876626821947567 116206577284314940232921351)
  ·
    refine ⟨174309865926472410349382027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116206577284314940232921351 174309865926472410349382027)
    ·
      refine ⟨261464798889708615524073041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174309865926472410349382027 261464798889708615524073041)
      ·
        refine ⟨196098599167281461643054781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261464798889708615524073041 196098599167281461643054781)
        ·
          refine ⟨73536974687730548116145543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196098599167281461643054781 73536974687730548116145543)
          ·
            refine ⟨110305462031595822174218315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73536974687730548116145543 110305462031595822174218315)
            ·
              refine ⟨165458193047393733261327473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110305462031595822174218315 165458193047393733261327473)
              ·
                refine ⟨124093644785545299945995605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165458193047393733261327473 124093644785545299945995605)
                ·
                  refine ⟨181777799978826122967767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 124093644785545299945995605 181777799978826122967767)
                  ·
                    rfl

theorem cell23_3186099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 11].length) (baseStart_3186099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186099 prefixEnd_3186099 := by exact prefixLift 3186099
  have htrace : WordTrace (prefixWord ++ tailWord_3186099) baseStart_3186099 baseEnd_3186099 := by
    simpa [prefixWord, tailWord_3186099, baseEnd_3186099] using wordTrace_append hprefix tailTrace_3186099
  have hstable : (prefixWord ++ tailWord_3186099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186099).length < 2 ^ (prefixWord ++ tailWord_3186099).sum := by decide
  have hdescent : baseEnd_3186099 < baseStart_3186099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186110 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_3186110 : Nat := 118140960795 + 3186110 * 2 ^ 59
def prefixEnd_3186110 : Nat := 4983230072969 + 3 ^ 40 * 3186110 * 2
def baseEnd_3186110 : Nat := 1636005848096634563672353

theorem tailTrace_3186110 : CollatzResearch.WordTrace tailWord_3186110 prefixEnd_3186110 1636005848096634563672353 := by
  unfold tailWord_3186110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525872310909386138946473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77471318991516726074381189 14525872310909386138946473)
  ·
    refine ⟨10894404233182039604209855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14525872310909386138946473 10894404233182039604209855)
    ·
      refine ⟨16341606349773059406314783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894404233182039604209855 16341606349773059406314783)
      ·
        refine ⟨24512409524659589109472175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16341606349773059406314783 24512409524659589109472175)
        ·
          refine ⟨36768614286989383664208263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24512409524659589109472175 36768614286989383664208263)
          ·
            refine ⟨55152921430484075496312395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36768614286989383664208263 55152921430484075496312395)
            ·
              refine ⟨82729382145726113244468593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55152921430484075496312395 82729382145726113244468593)
              ·
                refine ⟨62047036609294584933351445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82729382145726113244468593 62047036609294584933351445)
                ·
                  refine ⟨2908454841060683668750849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62047036609294584933351445 2908454841060683668750849)
                  ·
                    refine ⟨2181341130795512751563137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908454841060683668750849 2181341130795512751563137)
                    ·
                      refine ⟨1636005848096634563672353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181341130795512751563137 1636005848096634563672353)
                      ·
                        rfl

theorem cell23_3186110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_3186110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186110 prefixEnd_3186110 := by exact prefixLift 3186110
  have htrace : WordTrace (prefixWord ++ tailWord_3186110) baseStart_3186110 baseEnd_3186110 := by
    simpa [prefixWord, tailWord_3186110, baseEnd_3186110] using wordTrace_append hprefix tailTrace_3186110
  have hstable : (prefixWord ++ tailWord_3186110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186110).length < 2 ^ (prefixWord ++ tailWord_3186110).sum := by decide
  have hdescent : baseEnd_3186110 < baseStart_3186110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186183 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3186183 : Nat := 118140960795 + 3186183 * 2 ^ 59
def prefixEnd_3186183 : Nat := 4983230072969 + 3 ^ 40 * 3186183 * 2
def baseEnd_3186183 : Nat := 1636043332184412778059517

theorem tailTrace_3186183 : CollatzResearch.WordTrace tailWord_3186183 prefixEnd_3186183 1636043332184412778059517 := by
  unfold tailWord_3186183
  simp only [CollatzResearch.WordTrace]
  refine ⟨116209641016010622578979203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77473094010673748385986135 116209641016010622578979203)
  ·
    refine ⟨174314461524015933868468805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116209641016010622578979203 174314461524015933868468805)
    ·
      refine ⟨32683961535752987600337901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174314461524015933868468805 32683961535752987600337901)
      ·
        refine ⟨12256485575907370350126713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32683961535752987600337901 12256485575907370350126713)
        ·
          refine ⟨9192364181930527762595035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12256485575907370350126713 9192364181930527762595035)
          ·
            refine ⟨13788546272895791643892553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192364181930527762595035 13788546272895791643892553)
            ·
              refine ⟨10341409704671843732919415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13788546272895791643892553 10341409704671843732919415)
              ·
                refine ⟨15512114557007765599379123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341409704671843732919415 15512114557007765599379123)
                ·
                  refine ⟨23268171835511648399068685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15512114557007765599379123 23268171835511648399068685)
                  ·
                    refine ⟨8725564438316868149650757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23268171835511648399068685 8725564438316868149650757)
                    ·
                      refine ⟨1636043332184412778059517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725564438316868149650757 1636043332184412778059517)
                      ·
                        rfl

theorem cell23_3186183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3186183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186183 prefixEnd_3186183 := by exact prefixLift 3186183
  have htrace : WordTrace (prefixWord ++ tailWord_3186183) baseStart_3186183 baseEnd_3186183 := by
    simpa [prefixWord, tailWord_3186183, baseEnd_3186183] using wordTrace_append hprefix tailTrace_3186183
  have hstable : (prefixWord ++ tailWord_3186183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186183).length < 2 ^ (prefixWord ++ tailWord_3186183).sum := by decide
  have hdescent : baseEnd_3186183 < baseStart_3186183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186200 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3186200 : Nat := 118140960795 + 3186200 * 2 ^ 59
def prefixEnd_3186200 : Nat := 4983230072969 + 3 ^ 40 * 3186200 * 2
def baseEnd_3186200 : Nat := 1636052061355539211546939

theorem tailTrace_3186200 : CollatzResearch.WordTrace tailWord_3186200 prefixEnd_3186200 1636052061355539211546939 := by
  unfold tailWord_3186200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58105130528474517241174027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77473507371299356321565369 58105130528474517241174027)
  ·
    refine ⟨87157695792711775861761041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58105130528474517241174027 87157695792711775861761041)
    ·
      refine ⟨65368271844533831896320781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87157695792711775861761041 65368271844533831896320781)
      ·
        refine ⟨24513101941700186961120293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65368271844533831896320781 24513101941700186961120293)
        ·
          refine ⟨4596206614068785055210055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24513101941700186961120293 4596206614068785055210055)
          ·
            refine ⟨6894309921103177582815083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596206614068785055210055 6894309921103177582815083)
            ·
              refine ⟨10341464881654766374222625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6894309921103177582815083 10341464881654766374222625)
              ·
                refine ⟨7756098661241074780666969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10341464881654766374222625 7756098661241074780666969)
                ·
                  refine ⟨5817073995930806085500227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756098661241074780666969 5817073995930806085500227)
                  ·
                    refine ⟨8725610993896209128250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817073995930806085500227 8725610993896209128250341)
                    ·
                      refine ⟨1636052061355539211546939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725610993896209128250341 1636052061355539211546939)
                      ·
                        rfl

theorem cell23_3186200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3186200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186200 prefixEnd_3186200 := by exact prefixLift 3186200
  have htrace : WordTrace (prefixWord ++ tailWord_3186200) baseStart_3186200 baseEnd_3186200 := by
    simpa [prefixWord, tailWord_3186200, baseEnd_3186200] using wordTrace_append hprefix tailTrace_3186200
  have hstable : (prefixWord ++ tailWord_3186200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186200).length < 2 ^ (prefixWord ++ tailWord_3186200).sum := by decide
  have hdescent : baseEnd_3186200 < baseStart_3186200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186210 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3186210 : Nat := 118140960795 + 3186210 * 2 ^ 59
def prefixEnd_3186210 : Nat := 4983230072969 + 3 ^ 40 * 3186210 * 2
def baseEnd_3186210 : Nat := 545352398720694724140631

theorem tailTrace_3186210 : CollatzResearch.WordTrace tailWord_3186210 prefixEnd_3186210 545352398720694724140631 := by
  unfold tailWord_3186210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29052656446728201547553021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77473750524608537460141389 29052656446728201547553021)
  ·
    refine ⟨10894746167523075580332383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29052656446728201547553021 10894746167523075580332383)
    ·
      refine ⟨16342119251284613370498575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894746167523075580332383 16342119251284613370498575)
      ·
        refine ⟨24513178876926920055747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16342119251284613370498575 24513178876926920055747863)
        ·
          refine ⟨36769768315390380083621795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24513178876926920055747863 36769768315390380083621795)
          ·
            refine ⟨55154652473085570125432693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36769768315390380083621795 55154652473085570125432693)
            ·
              refine ⟨5170748669351772199259315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55154652473085570125432693 5170748669351772199259315)
              ·
                refine ⟨7756123004027658298888973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170748669351772199259315 7756123004027658298888973)
                ·
                  refine ⟨2908546126510371862083365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7756123004027658298888973 2908546126510371862083365)
                  ·
                    refine ⟨545352398720694724140631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2908546126510371862083365 545352398720694724140631)
                    ·
                      rfl

theorem cell23_3186210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3186210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186210 prefixEnd_3186210 := by exact prefixLift 3186210
  have htrace : WordTrace (prefixWord ++ tailWord_3186210) baseStart_3186210 baseEnd_3186210 := by
    simpa [prefixWord, tailWord_3186210, baseEnd_3186210] using wordTrace_append hprefix tailTrace_3186210
  have hstable : (prefixWord ++ tailWord_3186210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186210).length < 2 ^ (prefixWord ++ tailWord_3186210).sum := by decide
  have hdescent : baseEnd_3186210 < baseStart_3186210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186237 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3186237 : Nat := 118140960795 + 3186237 * 2 ^ 59
def prefixEnd_3186237 : Nat := 4983230072969 + 3 ^ 40 * 3186237 * 2
def baseEnd_3186237 : Nat := 1636071060139755566784269

theorem tailTrace_3186237 : CollatzResearch.WordTrace tailWord_3186237 prefixEnd_3186237 1636071060139755566784269 := by
  unfold tailWord_3186237
  simp only [CollatzResearch.WordTrace]
  refine ⟨116211610557814989801444965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77474407038543326534296643 116211610557814989801444965)
  ·
    refine ⟨21789676979590310587770931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116211610557814989801444965 21789676979590310587770931)
    ·
      refine ⟨32684515469385465881656397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21789676979590310587770931 32684515469385465881656397)
      ·
        refine ⟨12256693301019549705621149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32684515469385465881656397 12256693301019549705621149)
        ·
          refine ⟨4596259987882331139607931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12256693301019549705621149 4596259987882331139607931)
          ·
            refine ⟨6894389981823496709411897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596259987882331139607931 6894389981823496709411897)
            ·
              refine ⟨5170792486367622532058923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894389981823496709411897 5170792486367622532058923)
              ·
                refine ⟨7756188729551433798088385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170792486367622532058923 7756188729551433798088385)
                ·
                  refine ⟨5817141547163575348566289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756188729551433798088385 5817141547163575348566289)
                  ·
                    refine ⟨4362856160372681511424717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5817141547163575348566289 4362856160372681511424717)
                    ·
                      refine ⟨1636071060139755566784269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4362856160372681511424717 1636071060139755566784269)
                      ·
                        rfl

theorem cell23_3186237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3186237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186237 prefixEnd_3186237 := by exact prefixLift 3186237
  have htrace : WordTrace (prefixWord ++ tailWord_3186237) baseStart_3186237 baseEnd_3186237 := by
    simpa [prefixWord, tailWord_3186237, baseEnd_3186237] using wordTrace_append hprefix tailTrace_3186237
  have hstable : (prefixWord ++ tailWord_3186237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186237).length < 2 ^ (prefixWord ++ tailWord_3186237).sum := by decide
  have hdescent : baseEnd_3186237 < baseStart_3186237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186273 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3186273 : Nat := 118140960795 + 3186273 * 2 ^ 59
def prefixEnd_3186273 : Nat := 4983230072969 + 3 ^ 40 * 3186273 * 2
def baseEnd_3186273 : Nat := 1636089545443317425934103

theorem tailTrace_3186273 : CollatzResearch.WordTrace tailWord_3186273 prefixEnd_3186273 1636089545443317425934103 := by
  unfold tailWord_3186273
  simp only [CollatzResearch.WordTrace]
  refine ⟨116212923585684567949755473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77475282390456378633170315 116212923585684567949755473)
  ·
    refine ⟨87159692689263425962316605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116212923585684567949755473 87159692689263425962316605)
    ·
      refine ⟨32684884758473784735868727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87159692689263425962316605 32684884758473784735868727)
      ·
        refine ⟨49027327137710677103803091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32684884758473784735868727 49027327137710677103803091)
        ·
          refine ⟨73540990706566015655704637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49027327137710677103803091 73540990706566015655704637)
          ·
            refine ⟨27577871514962255870889239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73540990706566015655704637 27577871514962255870889239)
            ·
              refine ⟨41366807272443383806333859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27577871514962255870889239 41366807272443383806333859)
              ·
                refine ⟨62050210908665075709500789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41366807272443383806333859 62050210908665075709500789)
                ·
                  refine ⟨5817207272687350847765699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62050210908665075709500789 5817207272687350847765699)
                  ·
                    refine ⟨8725810909031026271648549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817207272687350847765699 8725810909031026271648549)
                    ·
                      refine ⟨1636089545443317425934103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725810909031026271648549 1636089545443317425934103)
                      ·
                        rfl

theorem cell23_3186273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3186273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186273 prefixEnd_3186273 := by exact prefixLift 3186273
  have htrace : WordTrace (prefixWord ++ tailWord_3186273) baseStart_3186273 baseEnd_3186273 := by
    simpa [prefixWord, tailWord_3186273, baseEnd_3186273] using wordTrace_append hprefix tailTrace_3186273
  have hstable : (prefixWord ++ tailWord_3186273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186273).length < 2 ^ (prefixWord ++ tailWord_3186273).sum := by decide
  have hdescent : baseEnd_3186273 < baseStart_3186273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186290 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3186290 : Nat := 118140960795 + 3186290 * 2 ^ 59
def prefixEnd_3186290 : Nat := 4983230072969 + 3 ^ 40 * 3186290 * 2
def baseEnd_3186290 : Nat := 1636098274614443859421525

theorem tailTrace_3186290 : CollatzResearch.WordTrace tailWord_3186290 prefixEnd_3186290 1636098274614443859421525 := by
  unfold tailWord_3186290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053385906655744963281081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77475695751081986568749549 29053385906655744963281081)
  ·
    refine ⟨21790039429991808722460811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29053385906655744963281081 21790039429991808722460811)
    ·
      refine ⟨32685059144987713083691217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21790039429991808722460811 32685059144987713083691217)
      ·
        refine ⟨24513794358740784812768413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32685059144987713083691217 24513794358740784812768413)
        ·
          refine ⟨9192672884527794304788155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24513794358740784812768413 9192672884527794304788155)
          ·
            refine ⟨13789009326791691457182233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192672884527794304788155 13789009326791691457182233)
            ·
              refine ⟨10341756995093768592886675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13789009326791691457182233 10341756995093768592886675)
              ·
                refine ⟨15512635492640652889330013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10341756995093768592886675 15512635492640652889330013)
                ·
                  refine ⟨5817238309740244833498755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15512635492640652889330013 5817238309740244833498755)
                  ·
                    refine ⟨8725857464610367250248133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5817238309740244833498755 8725857464610367250248133)
                    ·
                      refine ⟨1636098274614443859421525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725857464610367250248133 1636098274614443859421525)
                      ·
                        rfl

theorem cell23_3186290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3186290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186290 prefixEnd_3186290 := by exact prefixLift 3186290
  have htrace : WordTrace (prefixWord ++ tailWord_3186290) baseStart_3186290 baseEnd_3186290 := by
    simpa [prefixWord, tailWord_3186290, baseEnd_3186290] using wordTrace_append hprefix tailTrace_3186290
  have hstable : (prefixWord ++ tailWord_3186290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186290).length < 2 ^ (prefixWord ++ tailWord_3186290).sum := by decide
  have hdescent : baseEnd_3186290 < baseStart_3186290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186294 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3186294 : Nat := 118140960795 + 3186294 * 2 ^ 59
def prefixEnd_3186294 : Nat := 4983230072969 + 3 ^ 40 * 3186294 * 2
def baseEnd_3186294 : Nat := 1636100328537061843771507

theorem tailTrace_3186294 : CollatzResearch.WordTrace tailWord_3186294 prefixEnd_3186294 1636100328537061843771507 := by
  unfold tailWord_3186294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263355594913030533516871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77475793012405659024179957 7263355594913030533516871)
  ·
    refine ⟨10895033392369545800275307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263355594913030533516871 10895033392369545800275307)
    ·
      refine ⟨16342550088554318700412961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895033392369545800275307 16342550088554318700412961)
      ·
        refine ⟨12256912566415739025309721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16342550088554318700412961 12256912566415739025309721)
        ·
          refine ⟨9192684424811804268982291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12256912566415739025309721 9192684424811804268982291)
          ·
            refine ⟨13789026637217706403473437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9192684424811804268982291 13789026637217706403473437)
            ·
              refine ⟨5170884988956639901302539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13789026637217706403473437 5170884988956639901302539)
              ·
                refine ⟨7756327483434959851953809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170884988956639901302539 7756327483434959851953809)
                ·
                  refine ⟨5817245612576219888965357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7756327483434959851953809 5817245612576219888965357)
                  ·
                    refine ⟨2181467104716082458362009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5817245612576219888965357 2181467104716082458362009)
                    ·
                      refine ⟨1636100328537061843771507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181467104716082458362009 1636100328537061843771507)
                      ·
                        rfl

theorem cell23_3186294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3186294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186294 prefixEnd_3186294 := by exact prefixLift 3186294
  have htrace : WordTrace (prefixWord ++ tailWord_3186294) baseStart_3186294 baseEnd_3186294 := by
    simpa [prefixWord, tailWord_3186294, baseEnd_3186294] using wordTrace_append hprefix tailTrace_3186294
  have hstable : (prefixWord ++ tailWord_3186294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186294).length < 2 ^ (prefixWord ++ tailWord_3186294).sum := by decide
  have hdescent : baseEnd_3186294 < baseStart_3186294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186337 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3186337 : Nat := 118140960795 + 3186337 * 2 ^ 59
def prefixEnd_3186337 : Nat := 4983230072969 + 3 ^ 40 * 3186337 * 2
def baseEnd_3186337 : Nat := 1636122408205205175533809

theorem tailTrace_3186337 : CollatzResearch.WordTrace tailWord_3186337 prefixEnd_3186337 1636122408205205175533809 := by
  unfold tailWord_3186337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116215257857452706880085265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77476838571635137920056843 116215257857452706880085265)
  ·
    refine ⟨87161443393089530160063949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116215257857452706880085265 87161443393089530160063949)
    ·
      refine ⟨32685541272408573810023981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87161443393089530160063949 32685541272408573810023981)
      ·
        refine ⟨12257077977153215178758993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32685541272408573810023981 12257077977153215178758993)
        ·
          refine ⟨9192808482864911384069245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12257077977153215178758993 9192808482864911384069245)
          ·
            refine ⟨3447303181074341769025967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9192808482864911384069245 3447303181074341769025967)
            ·
              refine ⟨5170954771611512653538951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447303181074341769025967 5170954771611512653538951)
              ·
                refine ⟨7756432157417268980308427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170954771611512653538951 7756432157417268980308427)
                ·
                  refine ⟨11634648236125903470462641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7756432157417268980308427 11634648236125903470462641)
                  ·
                    refine ⟨8725986177094427602846981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11634648236125903470462641 8725986177094427602846981)
                    ·
                      refine ⟨1636122408205205175533809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8725986177094427602846981 1636122408205205175533809)
                      ·
                        rfl

theorem cell23_3186337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3186337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186337 prefixEnd_3186337 := by exact prefixLift 3186337
  have htrace : WordTrace (prefixWord ++ tailWord_3186337) baseStart_3186337 baseEnd_3186337 := by
    simpa [prefixWord, tailWord_3186337, baseEnd_3186337] using wordTrace_append hprefix tailTrace_3186337
  have hstable : (prefixWord ++ tailWord_3186337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186337).length < 2 ^ (prefixWord ++ tailWord_3186337).sum := by decide
  have hdescent : baseEnd_3186337 < baseStart_3186337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186367 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 1, 3, 2]
def baseStart_3186367 : Nat := 118140960795 + 3186367 * 2 ^ 59
def prefixEnd_3186367 : Nat := 4983230072969 + 3 ^ 40 * 3186367 * 2
def baseEnd_3186367 : Nat := 1636137812624840058158671

theorem tailTrace_3186367 : CollatzResearch.WordTrace tailWord_3186367 prefixEnd_3186367 1636137812624840058158671 := by
  unfold tailWord_3186367
  simp only [CollatzResearch.WordTrace]
  refine ⟨116216352047344022003677355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77477568031562681335784903 116216352047344022003677355)
  ·
    refine ⟨174324528071016033005516033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116216352047344022003677355 174324528071016033005516033)
    ·
      refine ⟨130743396053262024754137025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174324528071016033005516033 130743396053262024754137025)
      ·
        refine ⟨98057547039946518565602769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130743396053262024754137025 98057547039946518565602769)
        ·
          refine ⟨73543160279959888924202077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98057547039946518565602769 73543160279959888924202077)
          ·
            refine ⟨27578685104984958346575779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73543160279959888924202077 27578685104984958346575779)
            ·
              refine ⟨41368027657477437519863669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27578685104984958346575779 41368027657477437519863669)
              ·
                refine ⟨3878252592888509767487219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41368027657477437519863669 3878252592888509767487219)
                ·
                  refine ⟨5817378889332764651230829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878252592888509767487219 5817378889332764651230829)
                  ·
                    refine ⟨2181517083499786744211561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5817378889332764651230829 2181517083499786744211561)
                    ·
                      refine ⟨1636137812624840058158671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181517083499786744211561 1636137812624840058158671)
                      ·
                        rfl

theorem cell23_3186367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_3186367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186367 prefixEnd_3186367 := by exact prefixLift 3186367
  have htrace : WordTrace (prefixWord ++ tailWord_3186367) baseStart_3186367 baseEnd_3186367 := by
    simpa [prefixWord, tailWord_3186367, baseEnd_3186367] using wordTrace_append hprefix tailTrace_3186367
  have hstable : (prefixWord ++ tailWord_3186367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186367).length < 2 ^ (prefixWord ++ tailWord_3186367).sum := by decide
  have hdescent : baseEnd_3186367 < baseStart_3186367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186401 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_3186401 : Nat := 118140960795 + 3186401 * 2 ^ 59
def prefixEnd_3186401 : Nat := 4983230072969 + 3 ^ 40 * 3186401 * 2
def baseEnd_3186401 : Nat := 1636155270967092925133515

theorem tailTrace_3186401 : CollatzResearch.WordTrace tailWord_3186401 prefixEnd_3186401 1636155270967092925133515 := by
  unfold tailWord_3186401
  simp only [CollatzResearch.WordTrace]
  refine ⟨116217592129220845810415057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77478394752813897206943371 116217592129220845810415057)
  ·
    refine ⟨87163194096915634357811293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116217592129220845810415057 87163194096915634357811293)
    ·
      refine ⟨32686197786343362884179235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87163194096915634357811293 32686197786343362884179235)
      ·
        refine ⟨49029296679515044326268853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32686197786343362884179235 49029296679515044326268853)
        ·
          refine ⟨4596496563704535405587705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49029296679515044326268853 4596496563704535405587705)
          ·
            refine ⟨3447372422778401554190779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596496563704535405587705 3447372422778401554190779)
            ·
              refine ⟨5171058634167602331286169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447372422778401554190779 5171058634167602331286169)
              ·
                refine ⟨3878293975625701748464627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5171058634167602331286169 3878293975625701748464627)
                ·
                  refine ⟨5817440963438552622696941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878293975625701748464627 5817440963438552622696941)
                  ·
                    refine ⟨2181540361289457233511353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5817440963438552622696941 2181540361289457233511353)
                    ·
                      refine ⟨1636155270967092925133515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181540361289457233511353 1636155270967092925133515)
                      ·
                        rfl

theorem cell23_3186401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_3186401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186401 prefixEnd_3186401 := by exact prefixLift 3186401
  have htrace : WordTrace (prefixWord ++ tailWord_3186401) baseStart_3186401 baseEnd_3186401 := by
    simpa [prefixWord, tailWord_3186401, baseEnd_3186401] using wordTrace_append hprefix tailTrace_3186401
  have hstable : (prefixWord ++ tailWord_3186401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186401).length < 2 ^ (prefixWord ++ tailWord_3186401).sum := by decide
  have hdescent : baseEnd_3186401 < baseStart_3186401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186473 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3186473 : Nat := 118140960795 + 3186473 * 2 ^ 59
def prefixEnd_3186473 : Nat := 4983230072969 + 3 ^ 40 * 3186473 * 2
def baseEnd_3186473 : Nat := 1636192241574216643433183

theorem tailTrace_3186473 : CollatzResearch.WordTrace tailWord_3186473 prefixEnd_3186473 1636192241574216643433183 := by
  unfold tailWord_3186473
  simp only [CollatzResearch.WordTrace]
  refine ⟨116220218184960002107036073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77480145456640001404690715 116220218184960002107036073)
  ·
    refine ⟨87165163638720001580277055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116220218184960002107036073 87165163638720001580277055)
    ·
      refine ⟨130747745458080002370415583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87165163638720001580277055 130747745458080002370415583)
      ·
        refine ⟨196121618187120003555623375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130747745458080002370415583 196121618187120003555623375)
        ·
          refine ⟨294182427280680005333435063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196121618187120003555623375 294182427280680005333435063)
          ·
            refine ⟨441273640921020008000152595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294182427280680005333435063 441273640921020008000152595)
            ·
              refine ⟨661910461381530012000228893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441273640921020008000152595 661910461381530012000228893)
              ·
                refine ⟨248216423018073754500085835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661910461381530012000228893 248216423018073754500085835)
                ·
                  refine ⟨372324634527110631750128753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248216423018073754500085835 372324634527110631750128753)
                  ·
                    refine ⟨279243475895332973812596565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372324634527110631750128753 279243475895332973812596565)
                    ·
                      refine ⟨1636192241574216643433183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 279243475895332973812596565 1636192241574216643433183)
                      ·
                        rfl

theorem cell23_3186473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3186473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186473 prefixEnd_3186473 := by exact prefixLift 3186473
  have htrace : WordTrace (prefixWord ++ tailWord_3186473) baseStart_3186473 baseEnd_3186473 := by
    simpa [prefixWord, tailWord_3186473, baseEnd_3186473] using wordTrace_append hprefix tailTrace_3186473
  have hstable : (prefixWord ++ tailWord_3186473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186473).length < 2 ^ (prefixWord ++ tailWord_3186473).sum := by decide
  have hdescent : baseEnd_3186473 < baseStart_3186473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186537 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_3186537 : Nat := 118140960795 + 3186537 * 2 ^ 59
def prefixEnd_3186537 : Nat := 4983230072969 + 3 ^ 40 * 3186537 * 2
def baseEnd_3186537 : Nat := 1636225104336104393032889

theorem tailTrace_3186537 : CollatzResearch.WordTrace tailWord_3186537 prefixEnd_3186537 1636225104336104393032889 := by
  unfold tailWord_3186537
  simp only [CollatzResearch.WordTrace]
  refine ⟨116222552456728141037365865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77481701637818760691577243 116222552456728141037365865)
  ·
    refine ⟨87166914342546105778024399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116222552456728141037365865 87166914342546105778024399)
    ·
      refine ⟨130750371513819158667036599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87166914342546105778024399 130750371513819158667036599)
      ·
        refine ⟨196125557270728738000554899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130750371513819158667036599 196125557270728738000554899)
        ·
          refine ⟨294188335906093107000832349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196125557270728738000554899 294188335906093107000832349)
          ·
            refine ⟨110320625964784915125312131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294188335906093107000832349 110320625964784915125312131)
            ·
              refine ⟨165480938947177372687968197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110320625964784915125312131 165480938947177372687968197)
              ·
                refine ⟨31027676052595757378994037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165480938947177372687968197 31027676052595757378994037)
                ·
                  refine ⟨2908844629930852254280691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31027676052595757378994037 2908844629930852254280691)
                  ·
                    refine ⟨4363266944896278381421037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908844629930852254280691 4363266944896278381421037)
                    ·
                      refine ⟨1636225104336104393032889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363266944896278381421037 1636225104336104393032889)
                      ·
                        rfl

theorem cell23_3186537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_3186537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186537 prefixEnd_3186537 := by exact prefixLift 3186537
  have htrace : WordTrace (prefixWord ++ tailWord_3186537) baseStart_3186537 baseEnd_3186537 := by
    simpa [prefixWord, tailWord_3186537, baseEnd_3186537] using wordTrace_append hprefix tailTrace_3186537
  have hstable : (prefixWord ++ tailWord_3186537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186537).length < 2 ^ (prefixWord ++ tailWord_3186537).sum := by decide
  have hdescent : baseEnd_3186537 < baseStart_3186537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186554 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_3186554 : Nat := 118140960795 + 3186554 * 2 ^ 59
def prefixEnd_3186554 : Nat := 4983230072969 + 3 ^ 40 * 3186554 * 2
def baseEnd_3186554 : Nat := 1636233833507230826520311

theorem tailTrace_3186554 : CollatzResearch.WordTrace tailWord_3186554 prefixEnd_3186554 1636233833507230826520311 := by
  unfold tailWord_3186554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055793124416638235183679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77482114998444368627156477 29055793124416638235183679)
  ·
    refine ⟨43583689686624957352775519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29055793124416638235183679 43583689686624957352775519)
    ·
      refine ⟨65375534529937436029163279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43583689686624957352775519 65375534529937436029163279)
      ·
        refine ⟨98063301794906154043744919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65375534529937436029163279 98063301794906154043744919)
        ·
          refine ⟨147094952692359231065617379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98063301794906154043744919 147094952692359231065617379)
          ·
            refine ⟨220642429038538846598426069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147094952692359231065617379 220642429038538846598426069)
            ·
              refine ⟨5171306930590754217150611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220642429038538846598426069 5171306930590754217150611)
              ·
                refine ⟨7756960395886131325725917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171306930590754217150611 7756960395886131325725917)
                ·
                  refine ⟨2908860148457299247147219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7756960395886131325725917 2908860148457299247147219)
                  ·
                    refine ⟨4363290222685948870720829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2908860148457299247147219 4363290222685948870720829)
                    ·
                      refine ⟨1636233833507230826520311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363290222685948870720829 1636233833507230826520311)
                      ·
                        rfl

theorem cell23_3186554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_3186554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186554 prefixEnd_3186554 := by exact prefixLift 3186554
  have htrace : WordTrace (prefixWord ++ tailWord_3186554) baseStart_3186554 baseEnd_3186554 := by
    simpa [prefixWord, tailWord_3186554, baseEnd_3186554] using wordTrace_append hprefix tailTrace_3186554
  have hstable : (prefixWord ++ tailWord_3186554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186554).length < 2 ^ (prefixWord ++ tailWord_3186554).sum := by decide
  have hdescent : baseEnd_3186554 < baseStart_3186554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186577 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_3186577 : Nat := 118140960795 + 3186577 * 2 ^ 59
def prefixEnd_3186577 : Nat := 4983230072969 + 3 ^ 40 * 3186577 * 2
def baseEnd_3186577 : Nat := 1636245643562284236532705

theorem tailTrace_3186577 : CollatzResearch.WordTrace tailWord_3186577 prefixEnd_3186577 1636245643562284236532705 := by
  unfold tailWord_3186577
  simp only [CollatzResearch.WordTrace]
  refine ⟨116224011376583227868821985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77482674251055485245881323 116224011376583227868821985)
  ·
    refine ⟨87168008532437420901616489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116224011376583227868821985 87168008532437420901616489)
    ·
      refine ⟨65376006399328065676212367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87168008532437420901616489 65376006399328065676212367)
      ·
        refine ⟨98064009598992098514318551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65376006399328065676212367 98064009598992098514318551)
        ·
          refine ⟨147096014398488147771477827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98064009598992098514318551 147096014398488147771477827)
          ·
            refine ⟨220644021597732221657216741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147096014398488147771477827 220644021597732221657216741)
            ·
              refine ⟨41370754049574791560728139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220644021597732221657216741 41370754049574791560728139)
              ·
                refine ⟨62056131074362187341092209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41370754049574791560728139 62056131074362187341092209)
                ·
                  refine ⟨46542098305771640505819157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62056131074362187341092209 46542098305771640505819157)
                  ·
                    refine ⟨2181660858083045648710273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46542098305771640505819157 2181660858083045648710273)
                    ·
                      refine ⟨1636245643562284236532705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181660858083045648710273 1636245643562284236532705)
                      ·
                        rfl

theorem cell23_3186577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_3186577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186577 prefixEnd_3186577 := by exact prefixLift 3186577
  have htrace : WordTrace (prefixWord ++ tailWord_3186577) baseStart_3186577 baseEnd_3186577 := by
    simpa [prefixWord, tailWord_3186577, baseEnd_3186577] using wordTrace_append hprefix tailTrace_3186577
  have hstable : (prefixWord ++ tailWord_3186577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186577).length < 2 ^ (prefixWord ++ tailWord_3186577).sum := by decide
  have hdescent : baseEnd_3186577 < baseStart_3186577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
