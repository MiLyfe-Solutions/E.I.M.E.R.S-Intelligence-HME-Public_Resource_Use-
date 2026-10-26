import V185TrunkScan22Chunk368

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3291654 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3291654 : Nat := 118140960795 + 3291654 * 2 ^ 59
def prefixEnd_3291654 : Nat := 4983230072969 + 3 ^ 40 * 3291654 * 2
def baseEnd_3291654 : Nat := 375600144509948804952659

theorem tailTrace_3291654 : CollatzResearch.WordTrace tailWord_3291654 prefixEnd_3291654 375600144509948804952659 := by
  unfold tailWord_3291654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751765138028350080990313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80037656277938135061126677 3751765138028350080990313)
  ·
    refine ⟨2813823853521262560742735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751765138028350080990313 2813823853521262560742735)
    ·
      refine ⟨4220735780281893841114103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813823853521262560742735 4220735780281893841114103)
      ·
        refine ⟨6331103670422840761671155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220735780281893841114103 6331103670422840761671155)
        ·
          refine ⟨9496655505634261142506733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331103670422840761671155 9496655505634261142506733)
          ·
            refine ⟨3561245814612847928440025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9496655505634261142506733 3561245814612847928440025)
            ·
              refine ⟨2670934360959635946330019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3561245814612847928440025 2670934360959635946330019)
              ·
                refine ⟨4006401541439453919495029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670934360959635946330019 4006401541439453919495029)
                ·
                  refine ⟨375600144509948804952659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4006401541439453919495029 375600144509948804952659)
                  ·
                    rfl

theorem cell22_3291654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3291654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291654 prefixEnd_3291654 := by exact prefixLift 3291654
  have htrace : WordTrace (prefixWord ++ tailWord_3291654) baseStart_3291654 baseEnd_3291654 := by
    simpa [prefixWord, tailWord_3291654, baseEnd_3291654] using wordTrace_append hprefix tailTrace_3291654
  have hstable : (prefixWord ++ tailWord_3291654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291654).length < 2 ^ (prefixWord ++ tailWord_3291654).sum := by decide
  have hdescent : baseEnd_3291654 < baseStart_3291654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291659 : List Nat := [1, 1, 1, 1, 7, 1, 1, 9]
def baseStart_3291659 : Nat := 118140960795 + 3291659 * 2 ^ 59
def prefixEnd_3291659 : Nat := 4983230072969 + 3 ^ 40 * 3291659 * 2
def baseEnd_3291659 : Nat := 125200238348003118720329

theorem tailTrace_3291659 : CollatzResearch.WordTrace tailWord_3291659 prefixEnd_3291659 125200238348003118720329 := by
  unfold tailWord_3291659
  simp only [CollatzResearch.WordTrace]
  refine ⟨120056666781889088445622031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80037777854592725630414687 120056666781889088445622031)
  ·
    refine ⟨180085000172833632668433047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120056666781889088445622031 180085000172833632668433047)
    ·
      refine ⟨270127500259250449002649571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180085000172833632668433047 270127500259250449002649571)
      ·
        refine ⟨405191250388875673503974357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270127500259250449002649571 405191250388875673503974357)
        ·
          refine ⟨9496669930989273597749399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 405191250388875673503974357 9496669930989273597749399)
          ·
            refine ⟨14245004896483910396624099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9496669930989273597749399 14245004896483910396624099)
            ·
              refine ⟨21367507344725865594936149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14245004896483910396624099 21367507344725865594936149)
              ·
                refine ⟨125200238348003118720329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21367507344725865594936149 125200238348003118720329)
                ·
                  rfl

theorem cell22_3291659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_3291659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291659 prefixEnd_3291659 := by exact prefixLift 3291659
  have htrace : WordTrace (prefixWord ++ tailWord_3291659) baseStart_3291659 baseEnd_3291659 := by
    simpa [prefixWord, tailWord_3291659, baseEnd_3291659] using wordTrace_append hprefix tailTrace_3291659
  have hstable : (prefixWord ++ tailWord_3291659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291659).length < 2 ^ (prefixWord ++ tailWord_3291659).sum := by decide
  have hdescent : baseEnd_3291659 < baseStart_3291659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291674 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_3291674 : Nat := 118140960795 + 3291674 * 2 ^ 59
def prefixEnd_3291674 : Nat := 4983230072969 + 3 ^ 40 * 3291674 * 2
def baseEnd_3291674 : Nat := 1126807279938573029357915

theorem tailTrace_3291674 : CollatzResearch.WordTrace tailWord_3291674 prefixEnd_3291674 1126807279938573029357915 := by
  unfold tailWord_3291674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014303469208686501854519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80038142584556497338278717 30014303469208686501854519)
  ·
    refine ⟨45021455203813029752781779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30014303469208686501854519 45021455203813029752781779)
    ·
      refine ⟨67532182805719544629172669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45021455203813029752781779 67532182805719544629172669)
      ·
        refine ⟨25324568552144829235939751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67532182805719544629172669 25324568552144829235939751)
        ·
          refine ⟨37986852828217243853909627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25324568552144829235939751 37986852828217243853909627)
          ·
            refine ⟨56980279242325865780864441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37986852828217243853909627 56980279242325865780864441)
            ·
              refine ⟨42735209431744399335648331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56980279242325865780864441 42735209431744399335648331)
              ·
                refine ⟨64102814147616599003472497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42735209431744399335648331 64102814147616599003472497)
                ·
                  refine ⟨48077110610712449252604373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64102814147616599003472497 48077110610712449252604373)
                  ·
                    refine ⟨1126807279938573029357915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48077110610712449252604373 1126807279938573029357915)
                    ·
                      rfl

theorem cell22_3291674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_3291674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291674 prefixEnd_3291674 := by exact prefixLift 3291674
  have htrace : WordTrace (prefixWord ++ tailWord_3291674) baseStart_3291674 baseEnd_3291674 := by
    simpa [prefixWord, tailWord_3291674, baseEnd_3291674] using wordTrace_append hprefix tailTrace_3291674
  have hstable : (prefixWord ++ tailWord_3291674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291674).length < 2 ^ (prefixWord ++ tailWord_3291674).sum := by decide
  have hdescent : baseEnd_3291674 < baseStart_3291674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291693 : List Nat := [1, 5, 4, 1, 11]
def baseStart_3291693 : Nat := 118140960795 + 3291693 * 2 ^ 59
def prefixEnd_3291693 : Nat := 4983230072969 + 3 ^ 40 * 3291693 * 2
def baseEnd_3291693 : Nat := 4637093761427421041699

theorem tailTrace_3291693 : CollatzResearch.WordTrace tailWord_3291693 prefixEnd_3291693 4637093761427421041699 := by
  unfold tailWord_3291693
  simp only [CollatzResearch.WordTrace]
  refine ⟨120057906863765912252359733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80038604575843941501573155 120057906863765912252359733)
  ·
    refine ⟨11255428768478054273658725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120057906863765912252359733 11255428768478054273658725)
    ·
      refine ⟨2110392894089635176311011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11255428768478054273658725 2110392894089635176311011)
      ·
        refine ⟨3165589341134452764466517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110392894089635176311011 3165589341134452764466517)
        ·
          refine ⟨4637093761427421041699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3165589341134452764466517 4637093761427421041699)
          ·
            rfl

theorem cell22_3291693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 11].length) (baseStart_3291693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291693 prefixEnd_3291693 := by exact prefixLift 3291693
  have htrace : WordTrace (prefixWord ++ tailWord_3291693) baseStart_3291693 baseEnd_3291693 := by
    simpa [prefixWord, tailWord_3291693, baseEnd_3291693] using wordTrace_append hprefix tailTrace_3291693
  have hstable : (prefixWord ++ tailWord_3291693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291693).length < 2 ^ (prefixWord ++ tailWord_3291693).sum := by decide
  have hdescent : baseEnd_3291693 < baseStart_3291693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291710 : List Nat := [4, 2, 1, 4, 1, 2, 1, 7]
def baseStart_3291710 : Nat := 118140960795 + 3291710 * 2 ^ 59
def prefixEnd_3291710 : Nat := 4983230072969 + 3 ^ 40 * 3291710 * 2
def baseEnd_3291710 : Nat := 125202178163808992828645

theorem tailTrace_3291710 : CollatzResearch.WordTrace tailWord_3291710 prefixEnd_3291710 125202178163808992828645 := by
  unfold tailWord_3291710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007315863088040519466073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80039017936469549437152389 15007315863088040519466073)
  ·
    refine ⟨11255486897316030389599555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15007315863088040519466073 11255486897316030389599555)
    ·
      refine ⟨16883230345974045584399333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11255486897316030389599555 16883230345974045584399333)
      ·
        refine ⟨3165605689870133547074875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16883230345974045584399333 3165605689870133547074875)
        ·
          refine ⟨4748408534805200320612313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165605689870133547074875 4748408534805200320612313)
          ·
            refine ⟨3561306401103900240459235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4748408534805200320612313 3561306401103900240459235)
            ·
              refine ⟨5341959601655850360688853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561306401103900240459235 5341959601655850360688853)
              ·
                refine ⟨125202178163808992828645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5341959601655850360688853 125202178163808992828645)
                ·
                  rfl

theorem cell22_3291710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_3291710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291710 prefixEnd_3291710 := by exact prefixLift 3291710
  have htrace : WordTrace (prefixWord ++ tailWord_3291710) baseStart_3291710 baseEnd_3291710 := by
    simpa [prefixWord, tailWord_3291710, baseEnd_3291710] using wordTrace_append hprefix tailTrace_3291710
  have hstable : (prefixWord ++ tailWord_3291710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291710).length < 2 ^ (prefixWord ++ tailWord_3291710).sum := by decide
  have hdescent : baseEnd_3291710 < baseStart_3291710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291725 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3291725 : Nat := 118140960795 + 3291725 * 2 ^ 59
def prefixEnd_3291725 : Nat := 4983230072969 + 3 ^ 40 * 3291725 * 2
def baseEnd_3291725 : Nat := 1126824738280825896332759

theorem tailTrace_3291725 : CollatzResearch.WordTrace tailWord_3291725 prefixEnd_3291725 1126824738280825896332759 := by
  unfold tailWord_3291725
  simp only [CollatzResearch.WordTrace]
  refine ⟨120059073999649981717524629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80039382666433321145016419 120059073999649981717524629)
  ·
    refine ⟨5627769093733592893008967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120059073999649981717524629 5627769093733592893008967)
    ·
      refine ⟨8441653640600389339513451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627769093733592893008967 8441653640600389339513451)
      ·
        refine ⟨12662480460900584009270177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441653640600389339513451 12662480460900584009270177)
        ·
          refine ⟨9496860345675438006952633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12662480460900584009270177 9496860345675438006952633)
          ·
            refine ⟨7122645259256578505214475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496860345675438006952633 7122645259256578505214475)
            ·
              refine ⟨10683967888884867757821713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122645259256578505214475 10683967888884867757821713)
              ·
                refine ⟨8012975916663650818366285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10683967888884867757821713 8012975916663650818366285)
                ·
                  refine ⟨3004865968748869056887357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8012975916663650818366285 3004865968748869056887357)
                  ·
                    refine ⟨1126824738280825896332759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3004865968748869056887357 1126824738280825896332759)
                    ·
                      rfl

theorem cell22_3291725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3291725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291725 prefixEnd_3291725 := by exact prefixLift 3291725
  have htrace : WordTrace (prefixWord ++ tailWord_3291725) baseStart_3291725 baseEnd_3291725 := by
    simpa [prefixWord, tailWord_3291725, baseEnd_3291725] using wordTrace_append hprefix tailTrace_3291725
  have hstable : (prefixWord ++ tailWord_3291725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291725).length < 2 ^ (prefixWord ++ tailWord_3291725).sum := by decide
  have hdescent : baseEnd_3291725 < baseStart_3291725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291873 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 5]
def baseStart_3291873 : Nat := 118140960795 + 3291873 * 2 ^ 59
def prefixEnd_3291873 : Nat := 4983230072969 + 3 ^ 40 * 3291873 * 2
def baseEnd_3291873 : Nat := 375625133901800947877435

theorem tailTrace_3291873 : CollatzResearch.WordTrace tailWord_3291873 prefixEnd_3291873 375625133901800947877435 := by
  unfold tailWord_3291873
  simp only [CollatzResearch.WordTrace]
  refine ⟨120064472003113802993912273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80042981335409201995941515 120064472003113802993912273)
  ·
    refine ⟨90048354002335352245434205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120064472003113802993912273 90048354002335352245434205)
    ·
      refine ⟨33768132750875757092037827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90048354002335352245434205 33768132750875757092037827)
      ·
        refine ⟨50652199126313635638056741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33768132750875757092037827 50652199126313635638056741)
        ·
          refine ⟨9497287336183806682135639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50652199126313635638056741 9497287336183806682135639)
          ·
            refine ⟨14245931004275710023203459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9497287336183806682135639 14245931004275710023203459)
            ·
              refine ⟨21368896506413565034805189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14245931004275710023203459 21368896506413565034805189)
              ·
                refine ⟨4006668094952543444025973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21368896506413565034805189 4006668094952543444025973)
                ·
                  refine ⟨375625133901800947877435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4006668094952543444025973 375625133901800947877435)
                  ·
                    rfl

theorem cell22_3291873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_3291873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291873 prefixEnd_3291873 := by exact prefixLift 3291873
  have htrace : WordTrace (prefixWord ++ tailWord_3291873) baseStart_3291873 baseEnd_3291873 := by
    simpa [prefixWord, tailWord_3291873, baseEnd_3291873] using wordTrace_append hprefix tailTrace_3291873
  have hstable : (prefixWord ++ tailWord_3291873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291873).length < 2 ^ (prefixWord ++ tailWord_3291873).sum := by decide
  have hdescent : baseEnd_3291873 < baseStart_3291873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291877 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_3291877 : Nat := 118140960795 + 3291877 * 2 ^ 59
def prefixEnd_3291877 : Nat := 4983230072969 + 3 ^ 40 * 3291877 * 2
def baseEnd_3291877 : Nat := 1126876770987148166532293

theorem tailTrace_3291877 : CollatzResearch.WordTrace tailWord_3291877 prefixEnd_3291877 1126876770987148166532293 := by
  unfold tailWord_3291877
  simp only [CollatzResearch.WordTrace]
  refine ⟨120064617895099311677057885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80043078596732874451371923 120064617895099311677057885)
  ·
    refine ⟨45024231710662241878896707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120064617895099311677057885 45024231710662241878896707)
    ·
      refine ⟨67536347565993362818345061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45024231710662241878896707 67536347565993362818345061)
      ·
        refine ⟨12663065168623755528439699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67536347565993362818345061 12663065168623755528439699)
        ·
          refine ⟨18994597752935633292659549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12663065168623755528439699 18994597752935633292659549)
          ·
            refine ⟨7122974157350862484747331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18994597752935633292659549 7122974157350862484747331)
            ·
              refine ⟨10684461236026293727120997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122974157350862484747331 10684461236026293727120997)
              ·
                refine ⟨2003336481754930073835187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10684461236026293727120997 2003336481754930073835187)
                ·
                  refine ⟨3005004722632395110752781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003336481754930073835187 3005004722632395110752781)
                  ·
                    refine ⟨1126876770987148166532293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005004722632395110752781 1126876770987148166532293)
                    ·
                      rfl

theorem cell22_3291877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_3291877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291877 prefixEnd_3291877 := by exact prefixLift 3291877
  have htrace : WordTrace (prefixWord ++ tailWord_3291877) baseStart_3291877 baseEnd_3291877 := by
    simpa [prefixWord, tailWord_3291877, baseEnd_3291877] using wordTrace_append hprefix tailTrace_3291877
  have hstable : (prefixWord ++ tailWord_3291877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291877).length < 2 ^ (prefixWord ++ tailWord_3291877).sum := by decide
  have hdescent : baseEnd_3291877 < baseStart_3291877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291903 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 1, 4]
def baseStart_3291903 : Nat := 118140960795 + 3291903 * 2 ^ 59
def prefixEnd_3291903 : Nat := 4983230072969 + 3 ^ 40 * 3291903 * 2
def baseEnd_3291903 : Nat := 1126885671318492765382213

theorem tailTrace_3291903 : CollatzResearch.WordTrace tailWord_3291903 prefixEnd_3291903 1126885671318492765382213 := by
  unfold tailWord_3291903
  simp only [CollatzResearch.WordTrace]
  refine ⟨120065566193005118117504363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80043710795336745411669575 120065566193005118117504363)
  ·
    refine ⟨180098349289507677176256545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120065566193005118117504363 180098349289507677176256545)
    ·
      refine ⟨135073761967130757882192409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180098349289507677176256545 135073761967130757882192409)
      ·
        refine ⟨101305321475348068411644307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135073761967130757882192409 101305321475348068411644307)
        ·
          refine ⟨151957982213022102617466461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101305321475348068411644307 151957982213022102617466461)
          ·
            refine ⟨56984243329883288481549923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151957982213022102617466461 56984243329883288481549923)
            ·
              refine ⟨85476364994824932722324885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56984243329883288481549923 85476364994824932722324885)
              ·
                refine ⟨4006704609132418721358979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85476364994824932722324885 4006704609132418721358979)
                ·
                  refine ⟨6010056913698628082038469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006704609132418721358979 6010056913698628082038469)
                  ·
                    refine ⟨1126885671318492765382213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010056913698628082038469 1126885671318492765382213)
                    ·
                      rfl

theorem cell22_3291903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_3291903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291903 prefixEnd_3291903 := by exact prefixLift 3291903
  have htrace : WordTrace (prefixWord ++ tailWord_3291903) baseStart_3291903 baseEnd_3291903 := by
    simpa [prefixWord, tailWord_3291903, baseEnd_3291903] using wordTrace_append hprefix tailTrace_3291903
  have hstable : (prefixWord ++ tailWord_3291903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291903).length < 2 ^ (prefixWord ++ tailWord_3291903).sum := by decide
  have hdescent : baseEnd_3291903 < baseStart_3291903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291931 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_3291931 : Nat := 118140960795 + 3291931 * 2 ^ 59
def prefixEnd_3291931 : Nat := 4983230072969 + 3 ^ 40 * 3291931 * 2
def baseEnd_3291931 : Nat := 1126895256290710025682127

theorem tailTrace_3291931 : CollatzResearch.WordTrace tailWord_3291931 prefixEnd_3291931 1126895256290710025682127 := by
  unfold tailWord_3291931
  simp only [CollatzResearch.WordTrace]
  refine ⟨120066587436903678899523647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80044391624602452599682431 120066587436903678899523647)
  ·
    refine ⟨180099881155355518349285471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120066587436903678899523647 180099881155355518349285471)
    ·
      refine ⟨270149821733033277523928207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180099881155355518349285471 270149821733033277523928207)
      ·
        refine ⟨405224732599549916285892311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270149821733033277523928207 405224732599549916285892311)
        ·
          refine ⟨607837098899324874428838467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405224732599549916285892311 607837098899324874428838467)
          ·
            refine ⟨911755648348987311643257701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607837098899324874428838467 911755648348987311643257701)
            ·
              refine ⟨170954184065435120933110819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 911755648348987311643257701 170954184065435120933110819)
              ·
                refine ⟨256431276098152681399666229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170954184065435120933110819 256431276098152681399666229)
                ·
                  refine ⟨24040432134201813881218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256431276098152681399666229 24040432134201813881218709)
                  ·
                    refine ⟨1126895256290710025682127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24040432134201813881218709 1126895256290710025682127)
                    ·
                      rfl

theorem cell22_3291931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_3291931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291931 prefixEnd_3291931 := by exact prefixLift 3291931
  have htrace : WordTrace (prefixWord ++ tailWord_3291931) baseStart_3291931 baseEnd_3291931 := by
    simpa [prefixWord, tailWord_3291931, baseEnd_3291931] using wordTrace_append hprefix tailTrace_3291931
  have hstable : (prefixWord ++ tailWord_3291931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291931).length < 2 ^ (prefixWord ++ tailWord_3291931).sum := by decide
  have hdescent : baseEnd_3291931 < baseStart_3291931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3291935 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 4]
def baseStart_3291935 : Nat := 118140960795 + 3291935 * 2 ^ 59
def prefixEnd_3291935 : Nat := 4983230072969 + 3 ^ 40 * 3291935 * 2
def baseEnd_3291935 : Nat := 375632208524151782860705

theorem tailTrace_3291935 : CollatzResearch.WordTrace tailWord_3291935 prefixEnd_3291935 375632208524151782860705 := by
  unfold tailWord_3291935
  simp only [CollatzResearch.WordTrace]
  refine ⟨120066733328889187582669259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80044488885926125055112839 120066733328889187582669259)
  ·
    refine ⟨180100099993333781374003889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120066733328889187582669259 180100099993333781374003889)
    ·
      refine ⟨135075074995000336030502917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180100099993333781374003889 135075074995000336030502917)
      ·
        refine ⟨25326576561562563005719297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135075074995000336030502917 25326576561562563005719297)
        ·
          refine ⟨18994932421171922254289473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25326576561562563005719297 18994932421171922254289473)
          ·
            refine ⟨14246199315878941690717105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18994932421171922254289473 14246199315878941690717105)
            ·
              refine ⟨10684649486909206268037829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14246199315878941690717105 10684649486909206268037829)
              ·
                refine ⟨2003371778795476175257093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10684649486909206268037829 2003371778795476175257093)
                ·
                  refine ⟨375632208524151782860705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003371778795476175257093 375632208524151782860705)
                  ·
                    rfl

theorem cell22_3291935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 4].length) (baseStart_3291935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3291935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3291935 prefixEnd_3291935 := by exact prefixLift 3291935
  have htrace : WordTrace (prefixWord ++ tailWord_3291935) baseStart_3291935 baseEnd_3291935 := by
    simpa [prefixWord, tailWord_3291935, baseEnd_3291935] using wordTrace_append hprefix tailTrace_3291935
  have hstable : (prefixWord ++ tailWord_3291935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3291935).length < 2 ^ (prefixWord ++ tailWord_3291935).sum := by decide
  have hdescent : baseEnd_3291935 < baseStart_3291935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3291935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292042 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_3292042 : Nat := 118140960795 + 3292042 * 2 ^ 59
def prefixEnd_3292042 : Nat := 4983230072969 + 3 ^ 40 * 3292042 * 2
def baseEnd_3292042 : Nat := 375644417953047578718929

theorem tailTrace_3292042 : CollatzResearch.WordTrace tailWord_3292042 prefixEnd_3292042 375644417953047578718929 := by
  unfold tailWord_3292042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017658984875386214203595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80047090626334363237876253 30017658984875386214203595)
  ·
    refine ⟨45026488477313079321305393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30017658984875386214203595 45026488477313079321305393)
    ·
      refine ⟨33769866357984809490979045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45026488477313079321305393 33769866357984809490979045)
      ·
        refine ⟨6331849942122151779558571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33769866357984809490979045 6331849942122151779558571)
        ·
          refine ⟨9497774913183227669337857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331849942122151779558571 9497774913183227669337857)
          ·
            refine ⟨7123331184887420752003393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9497774913183227669337857 7123331184887420752003393)
            ·
              refine ⟨5342498388665565564002545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7123331184887420752003393 5342498388665565564002545)
              ·
                refine ⟨4006873791499174173001909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5342498388665565564002545 4006873791499174173001909)
                ·
                  refine ⟨375644417953047578718929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4006873791499174173001909 375644417953047578718929)
                  ·
                    rfl

theorem cell22_3292042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_3292042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292042 prefixEnd_3292042 := by exact prefixLift 3292042
  have htrace : WordTrace (prefixWord ++ tailWord_3292042) baseStart_3292042 baseEnd_3292042 := by
    simpa [prefixWord, tailWord_3292042, baseEnd_3292042] using wordTrace_append hprefix tailTrace_3292042
  have hstable : (prefixWord ++ tailWord_3292042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292042).length < 2 ^ (prefixWord ++ tailWord_3292042).sum := by decide
  have hdescent : baseEnd_3292042 < baseStart_3292042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292085 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3292085 : Nat := 118140960795 + 3292085 * 2 ^ 59
def prefixEnd_3292085 : Nat := 4983230072969 + 3 ^ 40 * 3292085 * 2
def baseEnd_3292085 : Nat := 1126947973637904957331655

theorem tailTrace_3292085 : CollatzResearch.WordTrace tailWord_3292085 prefixEnd_3292085 1126947973637904957331655 := by
  unfold tailWord_3292085
  simp only [CollatzResearch.WordTrace]
  refine ⟨120072204278345763200629709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80048136185563842133753139 120072204278345763200629709)
  ·
    refine ⟨45027076604379661200236141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120072204278345763200629709 45027076604379661200236141)
    ·
      refine ⟨16885153726642372950088553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45027076604379661200236141 16885153726642372950088553)
      ·
        refine ⟨12663865294981779712566415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16885153726642372950088553 12663865294981779712566415)
        ·
          refine ⟨18995797942472669568849623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12663865294981779712566415 18995797942472669568849623)
          ·
            refine ⟨28493696913709004353274435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18995797942472669568849623 28493696913709004353274435)
            ·
              refine ⟨42740545370563506529911653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28493696913709004353274435 42740545370563506529911653)
              ·
                refine ⟨8013852256980657474358435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42740545370563506529911653 8013852256980657474358435)
                ·
                  refine ⟨12020778385470986211537653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8013852256980657474358435 12020778385470986211537653)
                  ·
                    refine ⟨1126947973637904957331655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12020778385470986211537653 1126947973637904957331655)
                    ·
                      rfl

theorem cell22_3292085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3292085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292085 prefixEnd_3292085 := by exact prefixLift 3292085
  have htrace : WordTrace (prefixWord ++ tailWord_3292085) baseStart_3292085 baseEnd_3292085 := by
    simpa [prefixWord, tailWord_3292085, baseEnd_3292085] using wordTrace_append hprefix tailTrace_3292085
  have hstable : (prefixWord ++ tailWord_3292085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292085).length < 2 ^ (prefixWord ++ tailWord_3292085).sum := by decide
  have hdescent : baseEnd_3292085 < baseStart_3292085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292089 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_3292089 : Nat := 118140960795 + 3292089 * 2 ^ 59
def prefixEnd_3292089 : Nat := 4983230072969 + 3 ^ 40 * 3292089 * 2
def baseEnd_3292089 : Nat := 1126949342919650280231643

theorem tailTrace_3292089 : CollatzResearch.WordTrace tailWord_3292089 prefixEnd_3292089 1126949342919650280231643 := by
  unfold tailWord_3292089
  simp only [CollatzResearch.WordTrace]
  refine ⟨120072350170331271883775321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80048233446887514589183547 120072350170331271883775321)
  ·
    refine ⟨90054262627748453912831491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120072350170331271883775321 90054262627748453912831491)
    ·
      refine ⟨135081393941622680869247237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90054262627748453912831491 135081393941622680869247237)
      ·
        refine ⟨25327761364054252662983857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135081393941622680869247237 25327761364054252662983857)
        ·
          refine ⟨18995821023040689497237893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25327761364054252662983857 18995821023040689497237893)
          ·
            refine ⟨3561716441820129280732105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18995821023040689497237893 3561716441820129280732105)
            ·
              refine ⟨2671287331365096960549079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3561716441820129280732105 2671287331365096960549079)
              ·
                refine ⟨4006930997047645440823619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671287331365096960549079 4006930997047645440823619)
                ·
                  refine ⟨6010396495571468161235429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006930997047645440823619 6010396495571468161235429)
                  ·
                    refine ⟨1126949342919650280231643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010396495571468161235429 1126949342919650280231643)
                    ·
                      rfl

theorem cell22_3292089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_3292089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292089 prefixEnd_3292089 := by exact prefixLift 3292089
  have htrace : WordTrace (prefixWord ++ tailWord_3292089) baseStart_3292089 baseEnd_3292089 := by
    simpa [prefixWord, tailWord_3292089, baseEnd_3292089] using wordTrace_append hprefix tailTrace_3292089
  have hstable : (prefixWord ++ tailWord_3292089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292089).length < 2 ^ (prefixWord ++ tailWord_3292089).sum := by decide
  have hdescent : baseEnd_3292089 < baseStart_3292089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292149 : List Nat := [1, 3, 5, 2, 1, 2, 8]
def baseStart_3292149 : Nat := 118140960795 + 3292149 * 2 ^ 59
def prefixEnd_3292149 : Nat := 4983230072969 + 3 ^ 40 * 3292149 * 2
def baseEnd_3292149 : Nat := 41739625264660374953017

theorem tailTrace_3292149 : CollatzResearch.WordTrace tailWord_3292149 prefixEnd_3292149 41739625264660374953017 := by
  unfold tailWord_3292149
  simp only [CollatzResearch.WordTrace]
  refine ⟨120074538550113902130959501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80049692366742601420639667 120074538550113902130959501)
  ·
    refine ⟨45027951956292713299109813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120074538550113902130959501 45027951956292713299109813)
    ·
      refine ⟨4221370495902441871791545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45027951956292713299109813 4221370495902441871791545)
      ·
        refine ⟨3166027871926831403843659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4221370495902441871791545 3166027871926831403843659)
        ·
          refine ⟨4749041807890247105765489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166027871926831403843659 4749041807890247105765489)
          ·
            refine ⟨3561781355917685329324117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749041807890247105765489 3561781355917685329324117)
            ·
              refine ⟨41739625264660374953017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3561781355917685329324117 41739625264660374953017)
              ·
                rfl

theorem cell22_3292149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 8].length) (baseStart_3292149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292149 prefixEnd_3292149 := by exact prefixLift 3292149
  have htrace : WordTrace (prefixWord ++ tailWord_3292149) baseStart_3292149 baseEnd_3292149 := by
    simpa [prefixWord, tailWord_3292149, baseEnd_3292149] using wordTrace_append hprefix tailTrace_3292149
  have hstable : (prefixWord ++ tailWord_3292149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292149).length < 2 ^ (prefixWord ++ tailWord_3292149).sum := by decide
  have hdescent : baseEnd_3292149 < baseStart_3292149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292252 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3292252 : Nat := 118140960795 + 3292252 * 2 ^ 59
def prefixEnd_3292252 : Nat := 4983230072969 + 3 ^ 40 * 3292252 * 2
def baseEnd_3292252 : Nat := 1127005141150772188406143

theorem tailTrace_3292252 : CollatzResearch.WordTrace tailWord_3292252 prefixEnd_3292252 1127005141150772188406143 := by
  unfold tailWord_3292252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60039147634370375360979505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80052196845827167147972673 60039147634370375360979505)
  ·
    refine ⟨45029360725777781520734629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60039147634370375360979505 45029360725777781520734629)
    ·
      refine ⟨8443005136083334035137743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45029360725777781520734629 8443005136083334035137743)
      ·
        refine ⟨12664507704125001052706615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443005136083334035137743 12664507704125001052706615)
        ·
          refine ⟨18996761556187501579059923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664507704125001052706615 18996761556187501579059923)
          ·
            refine ⟨28495142334281252368589885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18996761556187501579059923 28495142334281252368589885)
            ·
              refine ⟨10685678375355469638221207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28495142334281252368589885 10685678375355469638221207)
              ·
                refine ⟨16028517563033204457331811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10685678375355469638221207 16028517563033204457331811)
                ·
                  refine ⟨24042776344549806685997717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16028517563033204457331811 24042776344549806685997717)
                  ·
                    refine ⟨1127005141150772188406143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24042776344549806685997717 1127005141150772188406143)
                    ·
                      rfl

theorem cell22_3292252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3292252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292252 prefixEnd_3292252 := by exact prefixLift 3292252
  have htrace : WordTrace (prefixWord ++ tailWord_3292252) baseStart_3292252 baseEnd_3292252 := by
    simpa [prefixWord, tailWord_3292252, baseEnd_3292252] using wordTrace_append hprefix tailTrace_3292252
  have hstable : (prefixWord ++ tailWord_3292252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292252).length < 2 ^ (prefixWord ++ tailWord_3292252).sum := by decide
  have hdescent : baseEnd_3292252 < baseStart_3292252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292258 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3292258 : Nat := 118140960795 + 3292258 * 2 ^ 59
def prefixEnd_3292258 : Nat := 4983230072969 + 3 ^ 40 * 3292258 * 2
def baseEnd_3292258 : Nat := 1127007195073390172756125

theorem tailTrace_3292258 : CollatzResearch.WordTrace tailWord_3292258 prefixEnd_3292258 1127007195073390172756125 := by
  unfold tailWord_3292258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019628526679753436669357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80052342737812675831118285 30019628526679753436669357)
  ·
    refine ⟨11257360697504907538751009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30019628526679753436669357 11257360697504907538751009)
    ·
      refine ⟨8443020523128680654063257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11257360697504907538751009 8443020523128680654063257)
      ·
        refine ⟨6332265392346510490547443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8443020523128680654063257 6332265392346510490547443)
        ·
          refine ⟨9498398088519765735821165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6332265392346510490547443 9498398088519765735821165)
          ·
            refine ⟨3561899283194912150932937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9498398088519765735821165 3561899283194912150932937)
            ·
              refine ⟨2671424462396184113199703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3561899283194912150932937 2671424462396184113199703)
              ·
                refine ⟨4007136693594276169799555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671424462396184113199703 4007136693594276169799555)
                ·
                  refine ⟨6010705040391414254699333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007136693594276169799555 6010705040391414254699333)
                  ·
                    refine ⟨1127007195073390172756125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6010705040391414254699333 1127007195073390172756125)
                    ·
                      rfl

theorem cell22_3292258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3292258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292258 prefixEnd_3292258 := by exact prefixLift 3292258
  have htrace : WordTrace (prefixWord ++ tailWord_3292258) baseStart_3292258 baseEnd_3292258 := by
    simpa [prefixWord, tailWord_3292258, baseEnd_3292258] using wordTrace_append hprefix tailTrace_3292258
  have hstable : (prefixWord ++ tailWord_3292258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292258).length < 2 ^ (prefixWord ++ tailWord_3292258).sum := by decide
  have hdescent : baseEnd_3292258 < baseStart_3292258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292280 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3292280 : Nat := 118140960795 + 3292280 * 2 ^ 59
def prefixEnd_3292280 : Nat := 4983230072969 + 3 ^ 40 * 3292280 * 2
def baseEnd_3292280 : Nat := 1127014726122989448706057

theorem tailTrace_3292280 : CollatzResearch.WordTrace tailWord_3292280 prefixEnd_3292280 1127014726122989448706057 := by
  unfold tailWord_3292280
  simp only [CollatzResearch.WordTrace]
  refine ⟨60039658256319655751989147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80052877675092874335985529 60039658256319655751989147)
  ·
    refine ⟨90059487384479483627983721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60039658256319655751989147 90059487384479483627983721)
    ·
      refine ⟨67544615538359612720987791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90059487384479483627983721 67544615538359612720987791)
      ·
        refine ⟨101316923307539419081481687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67544615538359612720987791 101316923307539419081481687)
        ·
          refine ⟨151975384961309128622222531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101316923307539419081481687 151975384961309128622222531)
          ·
            refine ⟨227963077441963692933333797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151975384961309128622222531 227963077441963692933333797)
            ·
              refine ⟨42743077020368192425000087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227963077441963692933333797 42743077020368192425000087)
              ·
                refine ⟨64114615530552288637500131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42743077020368192425000087 64114615530552288637500131)
                ·
                  refine ⟨96171923295828432956250197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64114615530552288637500131 96171923295828432956250197)
                  ·
                    refine ⟨1127014726122989448706057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96171923295828432956250197 1127014726122989448706057)
                    ·
                      rfl

theorem cell22_3292280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3292280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292280 prefixEnd_3292280 := by exact prefixLift 3292280
  have htrace : WordTrace (prefixWord ++ tailWord_3292280) baseStart_3292280 baseEnd_3292280 := by
    simpa [prefixWord, tailWord_3292280, baseEnd_3292280] using wordTrace_append hprefix tailTrace_3292280
  have hstable : (prefixWord ++ tailWord_3292280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292280).length < 2 ^ (prefixWord ++ tailWord_3292280).sum := by decide
  have hdescent : baseEnd_3292280 < baseStart_3292280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292312 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_3292312 : Nat := 118140960795 + 3292312 * 2 ^ 59
def prefixEnd_3292312 : Nat := 4983230072969 + 3 ^ 40 * 3292312 * 2
def baseEnd_3292312 : Nat := 375675226792317343968653

theorem tailTrace_3292312 : CollatzResearch.WordTrace tailWord_3292312 prefixEnd_3292312 375675226792317343968653 := by
  unfold tailWord_3292312
  simp only [CollatzResearch.WordTrace]
  refine ⟨60040241824261690484571595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80053655765682253979428793 60040241824261690484571595)
  ·
    refine ⟨90060362736392535726857393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60040241824261690484571595 90060362736392535726857393)
    ·
      refine ⟨67545272052294401795143045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90060362736392535726857393 67545272052294401795143045)
      ·
        refine ⟨12664738509805200336589321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67545272052294401795143045 12664738509805200336589321)
        ·
          refine ⟨9498553882353900252441991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12664738509805200336589321 9498553882353900252441991)
          ·
            refine ⟨14247830823530850378662987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498553882353900252441991 14247830823530850378662987)
            ·
              refine ⟨21371746235296275567994481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14247830823530850378662987 21371746235296275567994481)
              ·
                refine ⟨16028809676472206675995861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21371746235296275567994481 16028809676472206675995861)
                ·
                  refine ⟨375675226792317343968653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16028809676472206675995861 375675226792317343968653)
                  ·
                    rfl

theorem cell22_3292312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_3292312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292312 prefixEnd_3292312 := by exact prefixLift 3292312
  have htrace : WordTrace (prefixWord ++ tailWord_3292312) baseStart_3292312 baseEnd_3292312 := by
    simpa [prefixWord, tailWord_3292312, baseEnd_3292312] using wordTrace_append hprefix tailTrace_3292312
  have hstable : (prefixWord ++ tailWord_3292312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292312).length < 2 ^ (prefixWord ++ tailWord_3292312).sum := by decide
  have hdescent : baseEnd_3292312 < baseStart_3292312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292333 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3292333 : Nat := 118140960795 + 3292333 * 2 ^ 59
def prefixEnd_3292333 : Nat := 4983230072969 + 3 ^ 40 * 3292333 * 2
def baseEnd_3292333 : Nat := 1127032869106114977130895

theorem tailTrace_3292333 : CollatzResearch.WordTrace tailWord_3292333 prefixEnd_3292333 1127032869106114977130895 := by
  unfold tailWord_3292333
  simp only [CollatzResearch.WordTrace]
  refine ⟨120081249581447301555657653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80054166387631534370438435 120081249581447301555657653)
  ·
    refine ⟨11257617148260684520842905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120081249581447301555657653 11257617148260684520842905)
    ·
      refine ⟨8443212861195513390632179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11257617148260684520842905 8443212861195513390632179)
      ·
        refine ⟨12664819291793270085948269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443212861195513390632179 12664819291793270085948269)
        ·
          refine ⟨4749307234422476282230601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12664819291793270085948269 4749307234422476282230601)
          ·
            refine ⟨3561980425816857211672951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749307234422476282230601 3561980425816857211672951)
            ·
              refine ⟨5342970638725285817509427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561980425816857211672951 5342970638725285817509427)
              ·
                refine ⟨8014455958087928726264141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342970638725285817509427 8014455958087928726264141)
                ·
                  refine ⟨3005420984282973272349053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014455958087928726264141 3005420984282973272349053)
                  ·
                    refine ⟨1127032869106114977130895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005420984282973272349053 1127032869106114977130895)
                    ·
                      rfl

theorem cell22_3292333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3292333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292333 prefixEnd_3292333 := by exact prefixLift 3292333
  have htrace : WordTrace (prefixWord ++ tailWord_3292333) baseStart_3292333 baseEnd_3292333 := by
    simpa [prefixWord, tailWord_3292333, baseEnd_3292333] using wordTrace_append hprefix tailTrace_3292333
  have hstable : (prefixWord ++ tailWord_3292333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292333).length < 2 ^ (prefixWord ++ tailWord_3292333).sum := by decide
  have hdescent : baseEnd_3292333 < baseStart_3292333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292419 : List Nat := [1, 1, 1, 3, 2, 5, 3, 6]
def baseStart_3292419 : Nat := 118140960795 + 3292419 * 2 ^ 59
def prefixEnd_3292419 : Nat := 4983230072969 + 3 ^ 40 * 3292419 * 2
def baseEnd_3292419 : Nat := 125229145407071046608959

theorem tailTrace_3292419 : CollatzResearch.WordTrace tailWord_3292419 prefixEnd_3292419 125229145407071046608959 := by
  unfold tailWord_3292419
  simp only [CollatzResearch.WordTrace]
  refine ⟨120084386259135738243288311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80056257506090492162192207 120084386259135738243288311)
  ·
    refine ⟨180126579388703607364932467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120084386259135738243288311 180126579388703607364932467)
    ·
      refine ⟨270189869083055411047398701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180126579388703607364932467 270189869083055411047398701)
      ·
        refine ⟨101321200906145779142774513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270189869083055411047398701 101321200906145779142774513)
        ·
          refine ⟨75990900679609334357080885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101321200906145779142774513 75990900679609334357080885)
          ·
            refine ⟨7124146938713375095976333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75990900679609334357080885 7124146938713375095976333)
            ·
              refine ⟨2671555102017515660991125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124146938713375095976333 2671555102017515660991125)
              ·
                refine ⟨125229145407071046608959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2671555102017515660991125 125229145407071046608959)
                ·
                  rfl

theorem cell22_3292419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 6].length) (baseStart_3292419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292419 prefixEnd_3292419 := by exact prefixLift 3292419
  have htrace : WordTrace (prefixWord ++ tailWord_3292419) baseStart_3292419 baseEnd_3292419 := by
    simpa [prefixWord, tailWord_3292419, baseEnd_3292419] using wordTrace_append hprefix tailTrace_3292419
  have hstable : (prefixWord ++ tailWord_3292419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292419).length < 2 ^ (prefixWord ++ tailWord_3292419).sum := by decide
  have hdescent : baseEnd_3292419 < baseStart_3292419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292451 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 3, 3]
def baseStart_3292451 : Nat := 118140960795 + 3292451 * 2 ^ 59
def prefixEnd_3292451 : Nat := 4983230072969 + 3 ^ 40 * 3292451 * 2
def baseEnd_3292451 : Nat := 1127073262917602002680533

theorem tailTrace_3292451 : CollatzResearch.WordTrace tailWord_3292451 prefixEnd_3292451 1127073262917602002680533 := by
  unfold tailWord_3292451
  simp only [CollatzResearch.WordTrace]
  refine ⟨120085553395019807708453207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80057035596679871805635471 120085553395019807708453207)
  ·
    refine ⟨180128330092529711562679811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120085553395019807708453207 180128330092529711562679811)
    ·
      refine ⟨270192495138794567344019717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180128330092529711562679811 270192495138794567344019717)
      ·
        refine ⟨50661092838523981377003697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270192495138794567344019717 50661092838523981377003697)
        ·
          refine ⟨37995819628892986032752773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50661092838523981377003697 37995819628892986032752773)
          ·
            refine ⟨7124216180417434881141145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37995819628892986032752773 7124216180417434881141145)
            ·
              refine ⟨5343162135313076160855859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124216180417434881141145 5343162135313076160855859)
              ·
                refine ⟨8014743202969614241283789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343162135313076160855859 8014743202969614241283789)
                ·
                  refine ⟨3005528701113605340481421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014743202969614241283789 3005528701113605340481421)
                  ·
                    refine ⟨1127073262917602002680533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005528701113605340481421 1127073262917602002680533)
                    ·
                      rfl

theorem cell22_3292451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].length) (baseStart_3292451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292451 prefixEnd_3292451 := by exact prefixLift 3292451
  have htrace : WordTrace (prefixWord ++ tailWord_3292451) baseStart_3292451 baseEnd_3292451 := by
    simpa [prefixWord, tailWord_3292451, baseEnd_3292451] using wordTrace_append hprefix tailTrace_3292451
  have hstable : (prefixWord ++ tailWord_3292451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292451).length < 2 ^ (prefixWord ++ tailWord_3292451).sum := by decide
  have hdescent : baseEnd_3292451 < baseStart_3292451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292470 : List Nat := [5, 1, 2, 3, 1, 2, 2, 6]
def baseStart_3292470 : Nat := 118140960795 + 3292470 * 2 ^ 59
def prefixEnd_3292470 : Nat := 4983230072969 + 3 ^ 40 * 3292470 * 2
def baseEnd_3292470 : Nat := 125231085222876920717275

theorem tailTrace_3292470 : CollatzResearch.WordTrace tailWord_3292470 prefixEnd_3292470 125231085222876920717275 := by
  unfold tailWord_3292470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505390398871935872087179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80057497587967315968929909 7505390398871935872087179)
  ·
    refine ⟨11258085598307903808130769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7505390398871935872087179 11258085598307903808130769)
    ·
      refine ⟨8443564198730927856098077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11258085598307903808130769 8443564198730927856098077)
      ·
        refine ⟨3166336574524097946036779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8443564198730927856098077 3166336574524097946036779)
        ·
          refine ⟨4749504861786146919055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166336574524097946036779 4749504861786146919055169)
          ·
            refine ⟨3562128646339610189291377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4749504861786146919055169 3562128646339610189291377)
            ·
              refine ⟨2671596484754707641968533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3562128646339610189291377 2671596484754707641968533)
              ·
                refine ⟨125231085222876920717275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2671596484754707641968533 125231085222876920717275)
                ·
                  rfl

theorem cell22_3292470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_3292470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292470 prefixEnd_3292470 := by exact prefixLift 3292470
  have htrace : WordTrace (prefixWord ++ tailWord_3292470) baseStart_3292470 baseEnd_3292470 := by
    simpa [prefixWord, tailWord_3292470, baseEnd_3292470] using wordTrace_append hprefix tailTrace_3292470
  have hstable : (prefixWord ++ tailWord_3292470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292470).length < 2 ^ (prefixWord ++ tailWord_3292470).sum := by decide
  have hdescent : baseEnd_3292470 < baseStart_3292470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292545 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3292545 : Nat := 118140960795 + 3292545 * 2 ^ 59
def prefixEnd_3292545 : Nat := 4983230072969 + 3 ^ 40 * 3292545 * 2
def baseEnd_3292545 : Nat := 1127105441038617090830245

theorem tailTrace_3292545 : CollatzResearch.WordTrace tailWord_3292545 prefixEnd_3292545 1127105441038617090830245 := by
  unfold tailWord_3292545
  simp only [CollatzResearch.WordTrace]
  refine ⟨120088981856679261762375089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80059321237786174508250059 120088981856679261762375089)
  ·
    refine ⟨90066736392509446321781317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120088981856679261762375089 90066736392509446321781317)
    ·
      refine ⟨16887513073595521185333997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90066736392509446321781317 16887513073595521185333997)
      ·
        refine ⟨6332817402598320444500249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16887513073595521185333997 6332817402598320444500249)
        ·
          refine ⟨4749613051948740333375187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6332817402598320444500249 4749613051948740333375187)
          ·
            refine ⟨7124419577923110500062781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4749613051948740333375187 7124419577923110500062781)
            ·
              refine ⟨2671657341721166437523543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124419577923110500062781 2671657341721166437523543)
              ·
                refine ⟨4007486012581749656285315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671657341721166437523543 4007486012581749656285315)
                ·
                  refine ⟨6011229018872624484427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4007486012581749656285315 6011229018872624484427973)
                  ·
                    refine ⟨1127105441038617090830245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011229018872624484427973 1127105441038617090830245)
                    ·
                      rfl

theorem cell22_3292545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3292545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292545 prefixEnd_3292545 := by exact prefixLift 3292545
  have htrace : WordTrace (prefixWord ++ tailWord_3292545) baseStart_3292545 baseEnd_3292545 := by
    simpa [prefixWord, tailWord_3292545, baseEnd_3292545] using wordTrace_append hprefix tailTrace_3292545
  have hstable : (prefixWord ++ tailWord_3292545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292545).length < 2 ^ (prefixWord ++ tailWord_3292545).sum := by decide
  have hdescent : baseEnd_3292545 < baseStart_3292545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292599 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 7]
def baseStart_3292599 : Nat := 118140960795 + 3292599 * 2 ^ 59
def prefixEnd_3292599 : Nat := 4983230072969 + 3 ^ 40 * 3292599 * 2
def baseEnd_3292599 : Nat := 375707975447392983326693

theorem tailTrace_3292599 : CollatzResearch.WordTrace tailWord_3292599 prefixEnd_3292599 375707975447392983326693 := by
  unfold tailWord_3292599
  simp only [CollatzResearch.WordTrace]
  refine ⟨120090951398483628984840851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80060634265655752656560567 120090951398483628984840851)
  ·
    refine ⟨180136427097725443477261277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120090951398483628984840851 180136427097725443477261277)
    ·
      refine ⟨67551160161647041303972979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180136427097725443477261277 67551160161647041303972979)
      ·
        refine ⟨101326740242470561955959469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67551160161647041303972979 101326740242470561955959469)
        ·
          refine ⟨37997527590926460733484801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101326740242470561955959469 37997527590926460733484801)
          ·
            refine ⟨28498145693194845550113601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37997527590926460733484801 28498145693194845550113601)
            ·
              refine ⟨21373609269896134162585201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28498145693194845550113601 21373609269896134162585201)
              ·
                refine ⟨16030206952422100621938901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21373609269896134162585201 16030206952422100621938901)
                ·
                  refine ⟨375707975447392983326693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16030206952422100621938901 375707975447392983326693)
                  ·
                    rfl

theorem cell22_3292599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_3292599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292599 prefixEnd_3292599 := by exact prefixLift 3292599
  have htrace : WordTrace (prefixWord ++ tailWord_3292599) baseStart_3292599 baseEnd_3292599 := by
    simpa [prefixWord, tailWord_3292599, baseEnd_3292599] using wordTrace_append hprefix tailTrace_3292599
  have hstable : (prefixWord ++ tailWord_3292599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292599).length < 2 ^ (prefixWord ++ tailWord_3292599).sum := by decide
  have hdescent : baseEnd_3292599 < baseStart_3292599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292620 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_3292620 : Nat := 118140960795 + 3292620 * 2 ^ 59
def prefixEnd_3292620 : Nat := 4983230072969 + 3 ^ 40 * 3292620 * 2
def baseEnd_3292620 : Nat := 1127131115071341895205015

theorem tailTrace_3292620 : CollatzResearch.WordTrace tailWord_3292620 prefixEnd_3292620 1127131115071341895205015 := by
  unfold tailWord_3292620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60045858665703774785677657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80061144887605033047570209 60045858665703774785677657)
  ·
    refine ⟨45034393999277831089258243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60045858665703774785677657 45034393999277831089258243)
    ·
      refine ⟨67551590998916746633887365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45034393999277831089258243 67551590998916746633887365)
      ·
        refine ⟨12665923312296889993853881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67551590998916746633887365 12665923312296889993853881)
        ·
          refine ⟨9499442484222667495390411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12665923312296889993853881 9499442484222667495390411)
          ·
            refine ⟨14249163726334001243085617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9499442484222667495390411 14249163726334001243085617)
            ·
              refine ⟨10686872794750500932314213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14249163726334001243085617 10686872794750500932314213)
              ·
                refine ⟨2003788649015718924808915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10686872794750500932314213 2003788649015718924808915)
                ·
                  refine ⟨3005682973523578387213373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003788649015718924808915 3005682973523578387213373)
                  ·
                    refine ⟨1127131115071341895205015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005682973523578387213373 1127131115071341895205015)
                    ·
                      rfl

theorem cell22_3292620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_3292620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292620 prefixEnd_3292620 := by exact prefixLift 3292620
  have htrace : WordTrace (prefixWord ++ tailWord_3292620) baseStart_3292620 baseEnd_3292620 := by
    simpa [prefixWord, tailWord_3292620, baseEnd_3292620] using wordTrace_append hprefix tailTrace_3292620
  have hstable : (prefixWord ++ tailWord_3292620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292620).length < 2 ^ (prefixWord ++ tailWord_3292620).sum := by decide
  have hdescent : baseEnd_3292620 < baseStart_3292620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292633 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 5]
def baseStart_3292633 : Nat := 118140960795 + 3292633 * 2 ^ 59
def prefixEnd_3292633 : Nat := 4983230072969 + 3 ^ 40 * 3292633 * 2
def baseEnd_3292633 : Nat := 375711855079004731543325

theorem tailTrace_3292633 : CollatzResearch.WordTrace tailWord_3292633 prefixEnd_3292633 375711855079004731543325 := by
  unfold tailWord_3292633
  simp only [CollatzResearch.WordTrace]
  refine ⟨120092191480360452791578553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80061460986906968527719035 120092191480360452791578553)
  ·
    refine ⟨90069143610270339593683915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120092191480360452791578553 90069143610270339593683915)
    ·
      refine ⟨135103715415405509390525873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90069143610270339593683915 135103715415405509390525873)
      ·
        refine ⟨101327786561554132042894405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135103715415405509390525873 101327786561554132042894405)
        ·
          refine ⟨18998959980291399758042701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101327786561554132042894405 18998959980291399758042701)
          ·
            refine ⟨7124609992609274909266013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18998959980291399758042701 7124609992609274909266013)
            ·
              refine ⟨2671728747228478090974755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124609992609274909266013 2671728747228478090974755)
              ·
                refine ⟨4007593120842717136462133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2671728747228478090974755 4007593120842717136462133)
                ·
                  refine ⟨375711855079004731543325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4007593120842717136462133 375711855079004731543325)
                  ·
                    rfl

theorem cell22_3292633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_3292633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292633 prefixEnd_3292633 := by exact prefixLift 3292633
  have htrace : WordTrace (prefixWord ++ tailWord_3292633) baseStart_3292633 baseEnd_3292633 := by
    simpa [prefixWord, tailWord_3292633, baseEnd_3292633] using wordTrace_append hprefix tailTrace_3292633
  have hstable : (prefixWord ++ tailWord_3292633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292633).length < 2 ^ (prefixWord ++ tailWord_3292633).sum := by decide
  have hdescent : baseEnd_3292633 < baseStart_3292633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292706 : List Nat := [3, 3, 1, 1, 1, 1, 4, 8]
def baseStart_3292706 : Nat := 118140960795 + 3292706 * 2 ^ 59
def prefixEnd_3292706 : Nat := 4983230072969 + 3 ^ 40 * 3292706 * 2
def baseEnd_3292706 : Nat := 125240061625429593061639

theorem tailTrace_3292706 : CollatzResearch.WordTrace tailWord_3292706 prefixEnd_3292706 125240061625429593061639 := by
  unfold tailWord_3292706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30023713502273996564746493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80063236006063990839323981 30023713502273996564746493)
  ·
    refine ⟨11258892563352748711779935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30023713502273996564746493 11258892563352748711779935)
    ·
      refine ⟨16888338845029123067669903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11258892563352748711779935 16888338845029123067669903)
      ·
        refine ⟨25332508267543684601504855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16888338845029123067669903 25332508267543684601504855)
        ·
          refine ⟨37998762401315526902257283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25332508267543684601504855 37998762401315526902257283)
          ·
            refine ⟨56998143601973290353385925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37998762401315526902257283 56998143601973290353385925)
            ·
              refine ⟨10687151925369991941259861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56998143601973290353385925 10687151925369991941259861)
              ·
                refine ⟨125240061625429593061639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10687151925369991941259861 125240061625429593061639)
                ·
                  rfl

theorem cell22_3292706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_3292706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292706 prefixEnd_3292706 := by exact prefixLift 3292706
  have htrace : WordTrace (prefixWord ++ tailWord_3292706) baseStart_3292706 baseEnd_3292706 := by
    simpa [prefixWord, tailWord_3292706, baseEnd_3292706] using wordTrace_append hprefix tailTrace_3292706
  have hstable : (prefixWord ++ tailWord_3292706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292706).length < 2 ^ (prefixWord ++ tailWord_3292706).sum := by decide
  have hdescent : baseEnd_3292706 < baseStart_3292706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292772 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_3292772 : Nat := 118140960795 + 3292772 * 2 ^ 59
def prefixEnd_3292772 : Nat := 4983230072969 + 3 ^ 40 * 3292772 * 2
def baseEnd_3292772 : Nat := 1127183147777664165404549

theorem tailTrace_3292772 : CollatzResearch.WordTrace tailWord_3292772 prefixEnd_3292772 1127183147777664165404549 := by
  unfold tailWord_3292772
  simp only [CollatzResearch.WordTrace]
  refine ⟨60048630613428439765444285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80064840817904586353925713 60048630613428439765444285)
  ·
    refine ⟨22518236480035664912041607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60048630613428439765444285 22518236480035664912041607)
    ·
      refine ⟨33777354720053497368062411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22518236480035664912041607 33777354720053497368062411)
      ·
        refine ⟨50666032080080246052093617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33777354720053497368062411 50666032080080246052093617)
        ·
          refine ⟨37999524060060184539070213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50666032080080246052093617 37999524060060184539070213)
          ·
            refine ⟨7124910761261284601075665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37999524060060184539070213 7124910761261284601075665)
            ·
              refine ⟨5343683070945963450806749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7124910761261284601075665 5343683070945963450806749)
              ·
                refine ⟨2003881151604736294052531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343683070945963450806749 2003881151604736294052531)
                ·
                  refine ⟨3005821727407104441078797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003881151604736294052531 3005821727407104441078797)
                  ·
                    refine ⟨1127183147777664165404549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005821727407104441078797 1127183147777664165404549)
                    ·
                      rfl

theorem cell22_3292772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_3292772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292772 prefixEnd_3292772 := by exact prefixLift 3292772
  have htrace : WordTrace (prefixWord ++ tailWord_3292772) baseStart_3292772 baseEnd_3292772 := by
    simpa [prefixWord, tailWord_3292772, baseEnd_3292772] using wordTrace_append hprefix tailTrace_3292772
  have hstable : (prefixWord ++ tailWord_3292772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292772).length < 2 ^ (prefixWord ++ tailWord_3292772).sum := by decide
  have hdescent : baseEnd_3292772 < baseStart_3292772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292845 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3292845 : Nat := 118140960795 + 3292845 * 2 ^ 59
def prefixEnd_3292845 : Nat := 4983230072969 + 3 ^ 40 * 3292845 * 2
def baseEnd_3292845 : Nat := 1127208137169516308329325

theorem tailTrace_3292845 : CollatzResearch.WordTrace tailWord_3292845 prefixEnd_3292845 1127208137169516308329325 := by
  unfold tailWord_3292845
  simp only [CollatzResearch.WordTrace]
  refine ⟨120099923755592412998295989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80066615837061608665530659 120099923755592412998295989)
  ·
    refine ⟨11259367852086788718590249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120099923755592412998295989 11259367852086788718590249)
    ·
      refine ⟨8444525889065091538942687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11259367852086788718590249 8444525889065091538942687)
      ·
        refine ⟨12666788833597637308414031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8444525889065091538942687 12666788833597637308414031)
        ·
          refine ⟨19000183250396455962621047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12666788833597637308414031 19000183250396455962621047)
          ·
            refine ⟨28500274875594683943931571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19000183250396455962621047 28500274875594683943931571)
            ·
              refine ⟨42750412313392025915897357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28500274875594683943931571 42750412313392025915897357)
              ·
                refine ⟨16031404617522009718461509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42750412313392025915897357 16031404617522009718461509)
                ·
                  refine ⟨3005888365785376822211533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16031404617522009718461509 3005888365785376822211533)
                  ·
                    refine ⟨1127208137169516308329325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005888365785376822211533 1127208137169516308329325)
                    ·
                      rfl

theorem cell22_3292845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3292845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292845 prefixEnd_3292845 := by exact prefixLift 3292845
  have htrace : WordTrace (prefixWord ++ tailWord_3292845) baseStart_3292845 baseEnd_3292845 := by
    simpa [prefixWord, tailWord_3292845, baseEnd_3292845] using wordTrace_append hprefix tailTrace_3292845
  have hstable : (prefixWord ++ tailWord_3292845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292845).length < 2 ^ (prefixWord ++ tailWord_3292845).sum := by decide
  have hdescent : baseEnd_3292845 < baseStart_3292845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292858 : List Nat := [3, 1, 1, 1, 2, 5, 2, 7]
def baseStart_3292858 : Nat := 118140960795 + 3292858 * 2 ^ 59
def prefixEnd_3292858 : Nat := 4983230072969 + 3 ^ 40 * 3292858 * 2
def baseEnd_3292858 : Nat := 125245843037243178639365

theorem tailTrace_3292858 : CollatzResearch.WordTrace tailWord_3292858 prefixEnd_3292858 125245843037243178639365 := by
  unfold tailWord_3292858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30025099476136329054629807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80066931936363544145679485 30025099476136329054629807)
  ·
    refine ⟨45037649214204493581944711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30025099476136329054629807 45037649214204493581944711)
    ·
      refine ⟨67556473821306740372917067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45037649214204493581944711 67556473821306740372917067)
      ·
        refine ⟨101334710731960110559375601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67556473821306740372917067 101334710731960110559375601)
        ·
          refine ⟨76001033048970082919531701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101334710731960110559375601 76001033048970082919531701)
          ·
            refine ⟨7125096848340945273706097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76001033048970082919531701 7125096848340945273706097)
            ·
              refine ⟨5343822636255708955279573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7125096848340945273706097 5343822636255708955279573)
              ·
                refine ⟨125245843037243178639365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5343822636255708955279573 125245843037243178639365)
                ·
                  rfl

theorem cell22_3292858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_3292858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292858 prefixEnd_3292858 := by exact prefixLift 3292858
  have htrace : WordTrace (prefixWord ++ tailWord_3292858) baseStart_3292858 baseEnd_3292858 := by
    simpa [prefixWord, tailWord_3292858, baseEnd_3292858] using wordTrace_append hprefix tailTrace_3292858
  have hstable : (prefixWord ++ tailWord_3292858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292858).length < 2 ^ (prefixWord ++ tailWord_3292858).sum := by decide
  have hdescent : baseEnd_3292858 < baseStart_3292858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292862 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3292862 : Nat := 118140960795 + 3292862 * 2 ^ 59
def prefixEnd_3292862 : Nat := 4983230072969 + 3 ^ 40 * 3292862 * 2
def baseEnd_3292862 : Nat := 1127213956616933930654273

theorem tailTrace_3292862 : CollatzResearch.WordTrace tailWord_3292862 prefixEnd_3292862 1127213956616933930654273 := by
  unfold tailWord_3292862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012567974566353112708105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80067029197687216601109893 15012567974566353112708105)
  ·
    refine ⟨11259425980924764834531079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15012567974566353112708105 11259425980924764834531079)
    ·
      refine ⟨16889138971387147251796619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259425980924764834531079 16889138971387147251796619)
      ·
        refine ⟨25333708457080720877694929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889138971387147251796619 25333708457080720877694929)
        ·
          refine ⟨19000281342810540658271197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25333708457080720877694929 19000281342810540658271197)
          ·
            refine ⟨7125105503553952746851699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19000281342810540658271197 7125105503553952746851699)
            ·
              refine ⟨10687658255330929120277549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125105503553952746851699 10687658255330929120277549)
              ·
                refine ⟨4007871845749098420104081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10687658255330929120277549 4007871845749098420104081)
                ·
                  refine ⟨3005903884311823815078061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4007871845749098420104081 3005903884311823815078061)
                  ·
                    refine ⟨1127213956616933930654273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3005903884311823815078061 1127213956616933930654273)
                    ·
                      rfl

theorem cell22_3292862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3292862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292862 prefixEnd_3292862 := by exact prefixLift 3292862
  have htrace : WordTrace (prefixWord ++ tailWord_3292862) baseStart_3292862 baseEnd_3292862 := by
    simpa [prefixWord, tailWord_3292862, baseEnd_3292862] using wordTrace_append hprefix tailTrace_3292862
  have hstable : (prefixWord ++ tailWord_3292862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292862).length < 2 ^ (prefixWord ++ tailWord_3292862).sum := by decide
  have hdescent : baseEnd_3292862 < baseStart_3292862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292877 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3292877 : Nat := 118140960795 + 3292877 * 2 ^ 59
def prefixEnd_3292877 : Nat := 4983230072969 + 3 ^ 40 * 3292877 * 2
def baseEnd_3292877 : Nat := 1127219091423478891529227

theorem tailTrace_3292877 : CollatzResearch.WordTrace tailWord_3292877 prefixEnd_3292877 1127219091423478891529227 := by
  unfold tailWord_3292877
  simp only [CollatzResearch.WordTrace]
  refine ⟨120101090891476482463460885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80067393927650988308973923 120101090891476482463460885)
  ·
    refine ⟨5629738635537960115474729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120101090891476482463460885 5629738635537960115474729)
    ·
      refine ⟨4222303976653470086606047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5629738635537960115474729 4222303976653470086606047)
      ·
        refine ⟨6333455964980205129909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222303976653470086606047 6333455964980205129909071)
        ·
          refine ⟨9500183947470307694863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333455964980205129909071 9500183947470307694863607)
          ·
            refine ⟨14250275921205461542295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9500183947470307694863607 14250275921205461542295411)
            ·
              refine ⟨21375413881808192313443117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14250275921205461542295411 21375413881808192313443117)
              ·
                refine ⟨8015780205678072117541169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21375413881808192313443117 8015780205678072117541169)
                ·
                  refine ⟨6011835154258554088155877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8015780205678072117541169 6011835154258554088155877)
                  ·
                    refine ⟨1127219091423478891529227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6011835154258554088155877 1127219091423478891529227)
                    ·
                      rfl

theorem cell22_3292877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3292877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292877 prefixEnd_3292877 := by exact prefixLift 3292877
  have htrace : WordTrace (prefixWord ++ tailWord_3292877) baseStart_3292877 baseEnd_3292877 := by
    simpa [prefixWord, tailWord_3292877, baseEnd_3292877] using wordTrace_append hprefix tailTrace_3292877
  have hstable : (prefixWord ++ tailWord_3292877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292877).length < 2 ^ (prefixWord ++ tailWord_3292877).sum := by decide
  have hdescent : baseEnd_3292877 < baseStart_3292877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292963 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_3292963 : Nat := 118140960795 + 3292963 * 2 ^ 59
def prefixEnd_3292963 : Nat := 4983230072969 + 3 ^ 40 * 3292963 * 2
def baseEnd_3292963 : Nat := 1127248530981003333878963

theorem tailTrace_3292963 : CollatzResearch.WordTrace tailWord_3292963 prefixEnd_3292963 1127248530981003333878963 := by
  unfold tailWord_3292963
  simp only [CollatzResearch.WordTrace]
  refine ⟨120104227569164919151091543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80069485046109946100727695 120104227569164919151091543)
  ·
    refine ⟨180156341353747378726637315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120104227569164919151091543 180156341353747378726637315)
    ·
      refine ⟨270234512030621068089955973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180156341353747378726637315 270234512030621068089955973)
      ·
        refine ⟨50668971005741450266866745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270234512030621068089955973 50668971005741450266866745)
        ·
          refine ⟨38001728254306087700150059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50668971005741450266866745 38001728254306087700150059)
          ·
            refine ⟨57002592381459131550225089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38001728254306087700150059 57002592381459131550225089)
            ·
              refine ⟨42751944286094348662668817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57002592381459131550225089 42751944286094348662668817)
              ·
                refine ⟨32063958214570761497001613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42751944286094348662668817 32063958214570761497001613)
                ·
                  refine ⟨12023984330464035561375605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32063958214570761497001613 12023984330464035561375605)
                  ·
                    refine ⟨1127248530981003333878963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12023984330464035561375605 1127248530981003333878963)
                    ·
                      rfl

theorem cell22_3292963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_3292963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292963 prefixEnd_3292963 := by exact prefixLift 3292963
  have htrace : WordTrace (prefixWord ++ tailWord_3292963) baseStart_3292963 baseEnd_3292963 := by
    simpa [prefixWord, tailWord_3292963, baseEnd_3292963] using wordTrace_append hprefix tailTrace_3292963
  have hstable : (prefixWord ++ tailWord_3292963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292963).length < 2 ^ (prefixWord ++ tailWord_3292963).sum := by decide
  have hdescent : baseEnd_3292963 < baseStart_3292963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292965 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3292965 : Nat := 118140960795 + 3292965 * 2 ^ 59
def prefixEnd_3292965 : Nat := 4983230072969 + 3 ^ 40 * 3292965 * 2
def baseEnd_3292965 : Nat := 375749738540625331776319

theorem tailTrace_3292965 : CollatzResearch.WordTrace tailWord_3292965 prefixEnd_3292965 375749738540625331776319 := by
  unfold tailWord_3292965
  simp only [CollatzResearch.WordTrace]
  refine ⟨120104300515157673492664349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80069533676771782328442899 120104300515157673492664349)
  ·
    refine ⟨45039112693184127559749131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120104300515157673492664349 45039112693184127559749131)
    ·
      refine ⟨67558669039776191339623697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45039112693184127559749131 67558669039776191339623697)
      ·
        refine ⟨50669001779832143504717773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67558669039776191339623697 50669001779832143504717773)
        ·
          refine ⟨19000875667437053814269165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50669001779832143504717773 19000875667437053814269165)
          ·
            refine ⟨7125328375288895180350937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19000875667437053814269165 7125328375288895180350937)
            ·
              refine ⟨5343996281466671385263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7125328375288895180350937 5343996281466671385263203)
              ·
                refine ⟨8015994422200007077894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5343996281466671385263203 8015994422200007077894805)
                ·
                  refine ⟨375749738540625331776319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8015994422200007077894805 375749738540625331776319)
                  ·
                    rfl

theorem cell22_3292965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3292965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292965 prefixEnd_3292965 := by exact prefixLift 3292965
  have htrace : WordTrace (prefixWord ++ tailWord_3292965) baseStart_3292965 baseEnd_3292965 := by
    simpa [prefixWord, tailWord_3292965, baseEnd_3292965] using wordTrace_append hprefix tailTrace_3292965
  have hstable : (prefixWord ++ tailWord_3292965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292965).length < 2 ^ (prefixWord ++ tailWord_3292965).sum := by decide
  have hdescent : baseEnd_3292965 < baseStart_3292965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3292982 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3292982 : Nat := 118140960795 + 3292982 * 2 ^ 59
def prefixEnd_3292982 : Nat := 4983230072969 + 3 ^ 40 * 3292982 * 2
def baseEnd_3292982 : Nat := 375751678356431205884635

theorem tailTrace_3292982 : CollatzResearch.WordTrace tailWord_3292982 prefixEnd_3292982 375751678356431205884635 := by
  unfold tailWord_3292982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506557534756005337252075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80069947037397390264022133 7506557534756005337252075)
  ·
    refine ⟨11259836302134008005878113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7506557534756005337252075 11259836302134008005878113)
    ·
      refine ⟨8444877226600506004408585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11259836302134008005878113 8444877226600506004408585)
      ·
        refine ⟨6333657919950379503306439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8444877226600506004408585 6333657919950379503306439)
        ·
          refine ⟨9500486879925569254959659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333657919950379503306439 9500486879925569254959659)
          ·
            refine ⟨14250730319888353882439489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9500486879925569254959659 14250730319888353882439489)
            ·
              refine ⟨10688047739916265411829617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14250730319888353882439489 10688047739916265411829617)
              ·
                refine ⟨8016035804937199058872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10688047739916265411829617 8016035804937199058872213)
                ·
                  refine ⟨375751678356431205884635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8016035804937199058872213 375751678356431205884635)
                  ·
                    rfl

theorem cell22_3292982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3292982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3292982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3292982 prefixEnd_3292982 := by exact prefixLift 3292982
  have htrace : WordTrace (prefixWord ++ tailWord_3292982) baseStart_3292982 baseEnd_3292982 := by
    simpa [prefixWord, tailWord_3292982, baseEnd_3292982] using wordTrace_append hprefix tailTrace_3292982
  have hstable : (prefixWord ++ tailWord_3292982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3292982).length < 2 ^ (prefixWord ++ tailWord_3292982).sum := by decide
  have hdescent : baseEnd_3292982 < baseStart_3292982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3292982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293010 : List Nat := [3, 2, 2, 1, 1, 5, 8]
def baseStart_3293010 : Nat := 118140960795 + 3293010 * 2 ^ 59
def prefixEnd_3293010 : Nat := 4983230072969 + 3 ^ 40 * 3293010 * 2
def baseEnd_3293010 : Nat := 41750541483018921405697

theorem tailTrace_3293010 : CollatzResearch.WordTrace tailWord_3293010 prefixEnd_3293010 41750541483018921405697 := by
  unfold tailWord_3293010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30026485449998661544513121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80070627866663097452034989 30026485449998661544513121)
  ·
    refine ⟨22519864087498996158384841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30026485449998661544513121 22519864087498996158384841)
    ·
      refine ⟨16889898065624247118788631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22519864087498996158384841 16889898065624247118788631)
      ·
        refine ⟨25334847098436370678182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889898065624247118788631 25334847098436370678182947)
        ·
          refine ⟨38002270647654556017274421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25334847098436370678182947 38002270647654556017274421)
          ·
            refine ⟨3562712873217614626619477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38002270647654556017274421 3562712873217614626619477)
            ·
              refine ⟨41750541483018921405697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3562712873217614626619477 41750541483018921405697)
              ·
                rfl

theorem cell22_3293010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 8].length) (baseStart_3293010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293010 prefixEnd_3293010 := by exact prefixLift 3293010
  have htrace : WordTrace (prefixWord ++ tailWord_3293010) baseStart_3293010 baseEnd_3293010 := by
    simpa [prefixWord, tailWord_3293010, baseEnd_3293010] using wordTrace_append hprefix tailTrace_3293010
  have hstable : (prefixWord ++ tailWord_3293010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293010).length < 2 ^ (prefixWord ++ tailWord_3293010).sum := by decide
  have hdescent : baseEnd_3293010 < baseStart_3293010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293012 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3293012 : Nat := 118140960795 + 3293012 * 2 ^ 59
def prefixEnd_3293012 : Nat := 4983230072969 + 3 ^ 40 * 3293012 * 2
def baseEnd_3293012 : Nat := 1127265304682383539403813

theorem tailTrace_3293012 : CollatzResearch.WordTrace tailWord_3293012 prefixEnd_3293012 1127265304682383539403813 := by
  unfold tailWord_3293012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60053007372993700259812645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80070676497324933679750193 60053007372993700259812645)
  ·
    refine ⟨11259938882436318798714871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60053007372993700259812645 11259938882436318798714871)
    ·
      refine ⟨16889908323654478198072307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259938882436318798714871 16889908323654478198072307)
      ·
        refine ⟨25334862485481717297108461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16889908323654478198072307 25334862485481717297108461)
        ·
          refine ⟨9500573432055643986415673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25334862485481717297108461 9500573432055643986415673)
          ·
            refine ⟨7125430074041732989811755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9500573432055643986415673 7125430074041732989811755)
            ·
              refine ⟨10688145111062599484717633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125430074041732989811755 10688145111062599484717633)
              ·
                refine ⟨8016108833296949613538225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10688145111062599484717633 8016108833296949613538225)
                ·
                  refine ⟨6012081624972712210153669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8016108833296949613538225 6012081624972712210153669)
                  ·
                    refine ⟨1127265304682383539403813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6012081624972712210153669 1127265304682383539403813)
                    ·
                      rfl

theorem cell22_3293012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3293012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293012 prefixEnd_3293012 := by exact prefixLift 3293012
  have htrace : WordTrace (prefixWord ++ tailWord_3293012) baseStart_3293012 baseEnd_3293012 := by
    simpa [prefixWord, tailWord_3293012, baseEnd_3293012] using wordTrace_append hprefix tailTrace_3293012
  have hstable : (prefixWord ++ tailWord_3293012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293012).length < 2 ^ (prefixWord ++ tailWord_3293012).sum := by decide
  have hdescent : baseEnd_3293012 < baseStart_3293012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293076 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3293076 : Nat := 118140960795 + 3293076 * 2 ^ 59
def prefixEnd_3293076 : Nat := 4983230072969 + 3 ^ 40 * 3293076 * 2
def baseEnd_3293076 : Nat := 1127287213190308705803617

theorem tailTrace_3293076 : CollatzResearch.WordTrace tailWord_3293076 prefixEnd_3293076 1127287213190308705803617 := by
  unfold tailWord_3293076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60054174508877769724977541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80072232678503692966636721 60054174508877769724977541)
  ·
    refine ⟨11260157720414581823433289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60054174508877769724977541 11260157720414581823433289)
    ·
      refine ⟨8445118290310936367574967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11260157720414581823433289 8445118290310936367574967)
      ·
        refine ⟨12667677435466404551362451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8445118290310936367574967 12667677435466404551362451)
        ·
          refine ⟨19001516153199606827043677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12667677435466404551362451 19001516153199606827043677)
          ·
            refine ⟨7125568557449852560141379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19001516153199606827043677 7125568557449852560141379)
            ·
              refine ⟨10688352836174778840212069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125568557449852560141379 10688352836174778840212069)
              ·
                refine ⟨2004066156782771032539763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10688352836174778840212069 2004066156782771032539763)
                ·
                  refine ⟨3006099235174156548809645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004066156782771032539763 3006099235174156548809645)
                  ·
                    refine ⟨1127287213190308705803617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006099235174156548809645 1127287213190308705803617)
                    ·
                      rfl

theorem cell22_3293076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3293076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293076 prefixEnd_3293076 := by exact prefixLift 3293076
  have htrace : WordTrace (prefixWord ++ tailWord_3293076) baseStart_3293076 baseEnd_3293076 := by
    simpa [prefixWord, tailWord_3293076, baseEnd_3293076] using wordTrace_append hprefix tailTrace_3293076
  have hstable : (prefixWord ++ tailWord_3293076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293076).length < 2 ^ (prefixWord ++ tailWord_3293076).sum := by decide
  have hdescent : baseEnd_3293076 < baseStart_3293076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293078 : List Nat := [5, 3, 1, 1, 3, 1, 1, 7]
def baseStart_3293078 : Nat := 118140960795 + 3293078 * 2 ^ 59
def prefixEnd_3293078 : Nat := 4983230072969 + 3 ^ 40 * 3293078 * 2
def baseEnd_3293078 : Nat := 125254210870131263028179

theorem tailTrace_3293078 : CollatzResearch.WordTrace tailWord_3293078 prefixEnd_3293078 125254210870131263028179 := by
  unfold tailWord_3293078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506776372734268361970493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80072281309165529194351925 7506776372734268361970493)
  ·
    refine ⟨2815041139775350635738935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7506776372734268361970493 2815041139775350635738935)
    ·
      refine ⟨4222561709663025953608403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815041139775350635738935 4222561709663025953608403)
      ·
        refine ⟨6333842564494538930412605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222561709663025953608403 6333842564494538930412605)
        ·
          refine ⟨2375190961685452098904727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6333842564494538930412605 2375190961685452098904727)
          ·
            refine ⟨3562786442528178148357091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375190961685452098904727 3562786442528178148357091)
            ·
              refine ⟨5344179663792267222535637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562786442528178148357091 5344179663792267222535637)
              ·
                refine ⟨125254210870131263028179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5344179663792267222535637 125254210870131263028179)
                ·
                  rfl

theorem cell22_3293078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_3293078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293078 prefixEnd_3293078 := by exact prefixLift 3293078
  have htrace : WordTrace (prefixWord ++ tailWord_3293078) baseStart_3293078 baseEnd_3293078 := by
    simpa [prefixWord, tailWord_3293078, baseEnd_3293078] using wordTrace_append hprefix tailTrace_3293078
  have hstable : (prefixWord ++ tailWord_3293078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293078).length < 2 ^ (prefixWord ++ tailWord_3293078).sum := by decide
  have hdescent : baseEnd_3293078 < baseStart_3293078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293087 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_3293087 : Nat := 118140960795 + 3293087 * 2 ^ 59
def prefixEnd_3293087 : Nat := 4983230072969 + 3 ^ 40 * 3293087 * 2
def baseEnd_3293087 : Nat := 1127290978715108343778583

theorem tailTrace_3293087 : CollatzResearch.WordTrace tailWord_3293087 prefixEnd_3293087 1127290978715108343778583 := by
  unfold tailWord_3293087
  simp only [CollatzResearch.WordTrace]
  refine ⟨120108750220715688328605515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80072500147143792219070343 120108750220715688328605515)
  ·
    refine ⟨180163125331073532492908273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120108750220715688328605515 180163125331073532492908273)
    ·
      refine ⟨135122343998305149369681205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180163125331073532492908273 135122343998305149369681205)
      ·
        refine ⟨12667719749841107753407613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135122343998305149369681205 12667719749841107753407613)
        ·
          refine ⟨4750394906190415407527855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12667719749841107753407613 4750394906190415407527855)
          ·
            refine ⟨7125592359285623111291783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750394906190415407527855 7125592359285623111291783)
            ·
              refine ⟨10688388538928434666937675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7125592359285623111291783 10688388538928434666937675)
              ·
                refine ⟨16032582808392652000406513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10688388538928434666937675 16032582808392652000406513)
                ·
                  refine ⟨12024437106294489000304885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16032582808392652000406513 12024437106294489000304885)
                  ·
                    refine ⟨1127290978715108343778583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12024437106294489000304885 1127290978715108343778583)
                    ·
                      rfl

theorem cell22_3293087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_3293087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293087 prefixEnd_3293087 := by exact prefixLift 3293087
  have htrace : WordTrace (prefixWord ++ tailWord_3293087) baseStart_3293087 baseEnd_3293087 := by
    simpa [prefixWord, tailWord_3293087, baseEnd_3293087] using wordTrace_append hprefix tailTrace_3293087
  have hstable : (prefixWord ++ tailWord_3293087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293087).length < 2 ^ (prefixWord ++ tailWord_3293087).sum := by decide
  have hdescent : baseEnd_3293087 < baseStart_3293087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293160 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3293160 : Nat := 118140960795 + 3293160 * 2 ^ 59
def prefixEnd_3293160 : Nat := 4983230072969 + 3 ^ 40 * 3293160 * 2
def baseEnd_3293160 : Nat := 1127315968106960486703359

theorem tailTrace_3293160 : CollatzResearch.WordTrace tailWord_3293160 prefixEnd_3293160 1127315968106960486703359 := by
  unfold tailWord_3293160
  simp only [CollatzResearch.WordTrace]
  refine ⟨60055706374725610898006467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80074275166300814530675289 60055706374725610898006467)
  ·
    refine ⟨90083559562088416347009701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60055706374725610898006467 90083559562088416347009701)
    ·
      refine ⟨16890667417891578065064319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90083559562088416347009701 16890667417891578065064319)
      ·
        refine ⟨25336001126837367097596479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16890667417891578065064319 25336001126837367097596479)
        ·
          refine ⟨38004001690256050646394719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25336001126837367097596479 38004001690256050646394719)
          ·
            refine ⟨57006002535384075969592079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38004001690256050646394719 57006002535384075969592079)
            ·
              refine ⟨85509003803076113954388119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57006002535384075969592079 85509003803076113954388119)
              ·
                refine ⟨128263505704614170931582179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85509003803076113954388119 128263505704614170931582179)
                ·
                  refine ⟨192395258556921256397373269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128263505704614170931582179 192395258556921256397373269)
                  ·
                    refine ⟨1127315968106960486703359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192395258556921256397373269 1127315968106960486703359)
                    ·
                      rfl

theorem cell22_3293160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3293160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293160 prefixEnd_3293160 := by exact prefixLift 3293160
  have htrace : WordTrace (prefixWord ++ tailWord_3293160) baseStart_3293160 baseEnd_3293160 := by
    simpa [prefixWord, tailWord_3293160, baseEnd_3293160] using wordTrace_append hprefix tailTrace_3293160
  have hstable : (prefixWord ++ tailWord_3293160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293160).length < 2 ^ (prefixWord ++ tailWord_3293160).sum := by decide
  have hdescent : baseEnd_3293160 < baseStart_3293160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293376 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_3293376 : Nat := 118140960795 + 3293376 * 2 ^ 59
def prefixEnd_3293376 : Nat := 4983230072969 + 3 ^ 40 * 3293376 * 2
def baseEnd_3293376 : Nat := 375796636440402641100899

theorem tailTrace_3293376 : CollatzResearch.WordTrace tailWord_3293376 prefixEnd_3293376 375796636440402641100899 := by
  unfold tailWord_3293376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60059645458334345342937991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80079527277779127123917321 60059645458334345342937991)
  ·
    refine ⟨90089468187501518014406987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60059645458334345342937991 90089468187501518014406987)
    ·
      refine ⟨135134202281252277021610481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90089468187501518014406987 135134202281252277021610481)
      ·
        refine ⟨101350651710939207766207861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135134202281252277021610481 101350651710939207766207861)
        ·
          refine ⟨9501623597900550728081987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101350651710939207766207861 9501623597900550728081987)
          ·
            refine ⟨14252435396850826092122981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501623597900550728081987 14252435396850826092122981)
            ·
              refine ⟨2672331636909529892273059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14252435396850826092122981 2672331636909529892273059)
              ·
                refine ⟨4008497455364294838409589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672331636909529892273059 4008497455364294838409589)
                ·
                  refine ⟨375796636440402641100899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4008497455364294838409589 375796636440402641100899)
                  ·
                    rfl

theorem cell22_3293376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_3293376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293376 prefixEnd_3293376 := by exact prefixLift 3293376
  have htrace : WordTrace (prefixWord ++ tailWord_3293376) baseStart_3293376 baseEnd_3293376 := by
    simpa [prefixWord, tailWord_3293376, baseEnd_3293376] using wordTrace_append hprefix tailTrace_3293376
  have hstable : (prefixWord ++ tailWord_3293376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293376).length < 2 ^ (prefixWord ++ tailWord_3293376).sum := by decide
  have hdescent : baseEnd_3293376 < baseStart_3293376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293387 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 8]
def baseStart_3293387 : Nat := 118140960795 + 3293387 * 2 ^ 59
def prefixEnd_3293387 : Nat := 4983230072969 + 3 ^ 40 * 3293387 * 2
def baseEnd_3293387 : Nat := 375797891615335853759221

theorem tailTrace_3293387 : CollatzResearch.WordTrace tailWord_3293387 prefixEnd_3293387 375797891615335853759221 := by
  unfold tailWord_3293387
  simp only [CollatzResearch.WordTrace]
  refine ⟨120119692119628839564526415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80079794746419226376350943 120119692119628839564526415)
  ·
    refine ⟨180179538179443259346789623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120119692119628839564526415 180179538179443259346789623)
    ·
      refine ⟨270269307269164889020184435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180179538179443259346789623 270269307269164889020184435)
      ·
        refine ⟨405403960903747333530276653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270269307269164889020184435 405403960903747333530276653)
        ·
          refine ⟨152026485338905250073853745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405403960903747333530276653 152026485338905250073853745)
          ·
            refine ⟨114019864004178937555390309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152026485338905250073853745 114019864004178937555390309)
            ·
              refine ⟨21378724500783550791635683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114019864004178937555390309 21378724500783550791635683)
              ·
                refine ⟨32068086751175326187453525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21378724500783550791635683 32068086751175326187453525)
                ·
                  refine ⟨375797891615335853759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32068086751175326187453525 375797891615335853759221)
                  ·
                    rfl

theorem cell22_3293387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_3293387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293387 prefixEnd_3293387 := by exact prefixLift 3293387
  have htrace : WordTrace (prefixWord ++ tailWord_3293387) baseStart_3293387 baseEnd_3293387 := by
    simpa [prefixWord, tailWord_3293387, baseEnd_3293387] using wordTrace_append hprefix tailTrace_3293387
  have hstable : (prefixWord ++ tailWord_3293387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293387).length < 2 ^ (prefixWord ++ tailWord_3293387).sum := by decide
  have hdescent : baseEnd_3293387 < baseStart_3293387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293436 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_3293436 : Nat := 118140960795 + 3293436 * 2 ^ 59
def prefixEnd_3293436 : Nat := 4983230072969 + 3 ^ 40 * 3293436 * 2
def baseEnd_3293436 : Nat := 1127410448547387766802513

theorem tailTrace_3293436 : CollatzResearch.WordTrace tailWord_3293436 prefixEnd_3293436 1127410448547387766802513 := by
  unfold tailWord_3293436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60060739648225660466530081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80080986197634213955373441 60060739648225660466530081)
  ·
    refine ⟨45045554736169245349897561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60060739648225660466530081 45045554736169245349897561)
    ·
      refine ⟨33784166052126934012423171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45045554736169245349897561 33784166052126934012423171)
      ·
        refine ⟨50676249078190401018634757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33784166052126934012423171 50676249078190401018634757)
        ·
          refine ⟨9501796702160700190994017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50676249078190401018634757 9501796702160700190994017)
          ·
            refine ⟨7126347526620525143245513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501796702160700190994017 7126347526620525143245513)
            ·
              refine ⟨5344760644965393857434135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126347526620525143245513 5344760644965393857434135)
              ·
                refine ⟨8017140967448090786151203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344760644965393857434135 8017140967448090786151203)
                ·
                  refine ⟨12025711451172136179226805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017140967448090786151203 12025711451172136179226805)
                  ·
                    refine ⟨1127410448547387766802513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12025711451172136179226805 1127410448547387766802513)
                    ·
                      rfl

theorem cell22_3293436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_3293436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293436 prefixEnd_3293436 := by exact prefixLift 3293436
  have htrace : WordTrace (prefixWord ++ tailWord_3293436) baseStart_3293436 baseEnd_3293436 := by
    simpa [prefixWord, tailWord_3293436, baseEnd_3293436] using wordTrace_append hprefix tailTrace_3293436
  have hstable : (prefixWord ++ tailWord_3293436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293436).length < 2 ^ (prefixWord ++ tailWord_3293436).sum := by decide
  have hdescent : baseEnd_3293436 < baseStart_3293436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293470 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3293470 : Nat := 118140960795 + 3293470 * 2 ^ 59
def prefixEnd_3293470 : Nat := 4983230072969 + 3 ^ 40 * 3293470 * 2
def baseEnd_3293470 : Nat := 1127422087442223011452409

theorem tailTrace_3293470 : CollatzResearch.WordTrace tailWord_3293470 prefixEnd_3293470 1127422087442223011452409 := by
  unfold tailWord_3293470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015339922291018092474733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80081812918885429826531909 15015339922291018092474733)
  ·
    refine ⟨5630752470859131784678025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15015339922291018092474733 5630752470859131784678025)
    ·
      refine ⟨4223064353144348838508519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5630752470859131784678025 4223064353144348838508519)
      ·
        refine ⟨6334596529716523257762779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4223064353144348838508519 6334596529716523257762779)
        ·
          refine ⟨9501894794574784886644169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334596529716523257762779 9501894794574784886644169)
          ·
            refine ⟨7126421095931088664983127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501894794574784886644169 7126421095931088664983127)
            ·
              refine ⟨10689631643896632997474691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7126421095931088664983127 10689631643896632997474691)
              ·
                refine ⟨16034447465844949496212037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10689631643896632997474691 16034447465844949496212037)
                ·
                  refine ⟨3006458899845928030539757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16034447465844949496212037 3006458899845928030539757)
                  ·
                    refine ⟨1127422087442223011452409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006458899845928030539757 1127422087442223011452409)
                    ·
                      rfl

theorem cell22_3293470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3293470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293470 prefixEnd_3293470 := by exact prefixLift 3293470
  have htrace : WordTrace (prefixWord ++ tailWord_3293470) baseStart_3293470 baseEnd_3293470 := by
    simpa [prefixWord, tailWord_3293470, baseEnd_3293470] using wordTrace_append hprefix tailTrace_3293470
  have hstable : (prefixWord ++ tailWord_3293470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293470).length < 2 ^ (prefixWord ++ tailWord_3293470).sum := by decide
  have hdescent : baseEnd_3293470 < baseStart_3293470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293532 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3293532 : Nat := 118140960795 + 3293532 * 2 ^ 59
def prefixEnd_3293532 : Nat := 4983230072969 + 3 ^ 40 * 3293532 * 2
def baseEnd_3293532 : Nat := 1127443311309275516402219

theorem tailTrace_3293532 : CollatzResearch.WordTrace tailWord_3293532 prefixEnd_3293532 1127443311309275516402219 := by
  unfold tailWord_3293532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60062490352051764664277425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80083320469402352885703233 60062490352051764664277425)
  ·
    refine ⟨45046867764038823498208069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60062490352051764664277425 45046867764038823498208069)
    ·
      refine ⟨8446287705757279405914013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45046867764038823498208069 8446287705757279405914013)
      ·
        refine ⟨3167357889658979777217755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8446287705757279405914013 3167357889658979777217755)
        ·
          refine ⟨4751036834488469665826633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167357889658979777217755 4751036834488469665826633)
          ·
            refine ⟨3563277625866352249369975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4751036834488469665826633 3563277625866352249369975)
            ·
              refine ⟨5344916438799528374054963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563277625866352249369975 5344916438799528374054963)
              ·
                refine ⟨8017374658199292561082445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344916438799528374054963 8017374658199292561082445)
                ·
                  refine ⟨3006515496824734710405917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8017374658199292561082445 3006515496824734710405917)
                  ·
                    refine ⟨1127443311309275516402219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006515496824734710405917 1127443311309275516402219)
                    ·
                      rfl

theorem cell22_3293532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3293532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293532 prefixEnd_3293532 := by exact prefixLift 3293532
  have htrace : WordTrace (prefixWord ++ tailWord_3293532) baseStart_3293532 baseEnd_3293532 := by
    simpa [prefixWord, tailWord_3293532, baseEnd_3293532] using wordTrace_append hprefix tailTrace_3293532
  have hstable : (prefixWord ++ tailWord_3293532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293532).length < 2 ^ (prefixWord ++ tailWord_3293532).sum := by decide
  have hdescent : baseEnd_3293532 < baseStart_3293532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293693 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_3293693 : Nat := 118140960795 + 3293693 * 2 ^ 59
def prefixEnd_3293693 : Nat := 4983230072969 + 3 ^ 40 * 3293693 * 2
def baseEnd_3293693 : Nat := 1127498424899524763126725

theorem tailTrace_3293693 : CollatzResearch.WordTrace tailWord_3293693 prefixEnd_3293693 1127498424899524763126725 := by
  unfold tailWord_3293693
  simp only [CollatzResearch.WordTrace]
  refine ⟨120130852856520253825165733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80087235237680169216777155 120130852856520253825165733)
  ·
    refine ⟨22524534910597547592218575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120130852856520253825165733 22524534910597547592218575)
    ·
      refine ⟨33786802365896321388327863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524534910597547592218575 33786802365896321388327863)
      ·
        refine ⟨50680203548844482082491795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33786802365896321388327863 50680203548844482082491795)
        ·
          refine ⟨76020305323266723123737693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50680203548844482082491795 76020305323266723123737693)
          ·
            refine ⟨28507614496225021171401635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76020305323266723123737693 28507614496225021171401635)
            ·
              refine ⟨42761421744337531757102453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28507614496225021171401635 42761421744337531757102453)
              ·
                refine ⟨4008883288531643602228355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42761421744337531757102453 4008883288531643602228355)
                ·
                  refine ⟨6013324932797465403342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4008883288531643602228355 6013324932797465403342533)
                  ·
                    refine ⟨1127498424899524763126725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013324932797465403342533 1127498424899524763126725)
                    ·
                      rfl

theorem cell22_3293693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_3293693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293693 prefixEnd_3293693 := by exact prefixLift 3293693
  have htrace : WordTrace (prefixWord ++ tailWord_3293693) baseStart_3293693 baseEnd_3293693 := by
    simpa [prefixWord, tailWord_3293693, baseEnd_3293693] using wordTrace_append hprefix tailTrace_3293693
  have hstable : (prefixWord ++ tailWord_3293693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293693).length < 2 ^ (prefixWord ++ tailWord_3293693).sum := by decide
  have hdescent : baseEnd_3293693 < baseStart_3293693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293708 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_3293708 : Nat := 118140960795 + 3293708 * 2 ^ 59
def prefixEnd_3293708 : Nat := 4983230072969 + 3 ^ 40 * 3293708 * 2
def baseEnd_3293708 : Nat := 375834519902023241333893

theorem tailTrace_3293708 : CollatzResearch.WordTrace tailWord_3293708 prefixEnd_3293708 375834519902023241333893 := by
  unfold tailWord_3293708
  simp only [CollatzResearch.WordTrace]
  refine ⟨60065699975732955693480889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80087599967643940924641185 60065699975732955693480889)
  ·
    refine ⟨45049274981799716770110667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60065699975732955693480889 45049274981799716770110667)
    ·
      refine ⟨67573912472699575155166001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45049274981799716770110667 67573912472699575155166001)
      ·
        refine ⟨50680434354524681366374501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67573912472699575155166001 50680434354524681366374501)
        ·
          refine ⟨9502581441473377756195219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50680434354524681366374501 9502581441473377756195219)
          ·
            refine ⟨14253872162210066634292829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9502581441473377756195219 14253872162210066634292829)
            ·
              refine ⟨5345202060828774987859811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14253872162210066634292829 5345202060828774987859811)
              ·
                refine ⟨8017803091243162481789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345202060828774987859811 8017803091243162481789717)
                ·
                  refine ⟨375834519902023241333893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017803091243162481789717 375834519902023241333893)
                  ·
                    rfl

theorem cell22_3293708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_3293708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293708 prefixEnd_3293708 := by exact prefixLift 3293708
  have htrace : WordTrace (prefixWord ++ tailWord_3293708) baseStart_3293708 baseEnd_3293708 := by
    simpa [prefixWord, tailWord_3293708, baseEnd_3293708] using wordTrace_append hprefix tailTrace_3293708
  have hstable : (prefixWord ++ tailWord_3293708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293708).length < 2 ^ (prefixWord ++ tailWord_3293708).sum := by decide
  have hdescent : baseEnd_3293708 < baseStart_3293708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293757 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_3293757 : Nat := 118140960795 + 3293757 * 2 ^ 59
def prefixEnd_3293757 : Nat := 4983230072969 + 3 ^ 40 * 3293757 * 2
def baseEnd_3293757 : Nat := 1127520333407449929526529

theorem tailTrace_3293757 : CollatzResearch.WordTrace tailWord_3293757 prefixEnd_3293757 1127520333407449929526529 := by
  unfold tailWord_3293757
  simp only [CollatzResearch.WordTrace]
  refine ⟨120133187128288392755495525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80088791418858928503663683 120133187128288392755495525)
  ·
    refine ⟨22524972586554073641655411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120133187128288392755495525 22524972586554073641655411)
    ·
      refine ⟨33787458879831110462483117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524972586554073641655411 33787458879831110462483117)
      ·
        refine ⟨12670297079936666423431169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33787458879831110462483117 12670297079936666423431169)
        ·
          refine ⟨9502722809952499817573377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12670297079936666423431169 9502722809952499817573377)
          ·
            refine ⟨7127042107464374863180033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9502722809952499817573377 7127042107464374863180033)
            ·
              refine ⟨5345281580598281147385025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7127042107464374863180033 5345281580598281147385025)
              ·
                refine ⟨4008961185448710860538769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5345281580598281147385025 4008961185448710860538769)
                ·
                  refine ⟨3006720889086533145404077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4008961185448710860538769 3006720889086533145404077)
                  ·
                    refine ⟨1127520333407449929526529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006720889086533145404077 1127520333407449929526529)
                    ·
                      rfl

theorem cell22_3293757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_3293757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293757 prefixEnd_3293757 := by exact prefixLift 3293757
  have htrace : WordTrace (prefixWord ++ tailWord_3293757) baseStart_3293757 baseEnd_3293757 := by
    simpa [prefixWord, tailWord_3293757, baseEnd_3293757] using wordTrace_append hprefix tailTrace_3293757
  have hstable : (prefixWord ++ tailWord_3293757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293757).length < 2 ^ (prefixWord ++ tailWord_3293757).sum := by decide
  have hdescent : baseEnd_3293757 < baseStart_3293757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293768 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3293768 : Nat := 118140960795 + 3293768 * 2 ^ 59
def prefixEnd_3293768 : Nat := 4983230072969 + 3 ^ 40 * 3293768 * 2
def baseEnd_3293768 : Nat := 1127524098932249567501495

theorem tailTrace_3293768 : CollatzResearch.WordTrace tailWord_3293768 prefixEnd_3293768 1127524098932249567501495 := by
  unfold tailWord_3293768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60066794165624270817072979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80089058887499027756097305 60066794165624270817072979)
  ·
    refine ⟨90100191248436406225609469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60066794165624270817072979 90100191248436406225609469)
    ·
      refine ⟨33787571718163652334603551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90100191248436406225609469 33787571718163652334603551)
      ·
        refine ⟨50681357577245478501905327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33787571718163652334603551 50681357577245478501905327)
        ·
          refine ⟨76022036365868217752857991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50681357577245478501905327 76022036365868217752857991)
          ·
            refine ⟨114033054548802326629286987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76022036365868217752857991 114033054548802326629286987)
            ·
              refine ⟨171049581823203489943930481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114033054548802326629286987 171049581823203489943930481)
              ·
                refine ⟨128287186367402617457947861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171049581823203489943930481 128287186367402617457947861)
                ·
                  refine ⟨3006730930485998846670653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128287186367402617457947861 3006730930485998846670653)
                  ·
                    refine ⟨1127524098932249567501495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006730930485998846670653 1127524098932249567501495)
                    ·
                      rfl

theorem cell22_3293768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3293768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293768 prefixEnd_3293768 := by exact prefixLift 3293768
  have htrace : WordTrace (prefixWord ++ tailWord_3293768) baseStart_3293768 baseEnd_3293768 := by
    simpa [prefixWord, tailWord_3293768, baseEnd_3293768] using wordTrace_append hprefix tailTrace_3293768
  have hstable : (prefixWord ++ tailWord_3293768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293768).length < 2 ^ (prefixWord ++ tailWord_3293768).sum := by decide
  have hdescent : baseEnd_3293768 < baseStart_3293768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293875 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 4, 3]
def baseStart_3293875 : Nat := 118140960795 + 3293875 * 2 ^ 59
def prefixEnd_3293875 : Nat := 4983230072969 + 3 ^ 40 * 3293875 * 2
def baseEnd_3293875 : Nat := 1127560727218936955076167

theorem tailTrace_3293875 : CollatzResearch.WordTrace tailWord_3293875 prefixEnd_3293875 1127560727218936955076167 := by
  unfold tailWord_3293875
  simp only [CollatzResearch.WordTrace]
  refine ⟨120137490941860898908291079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80091660627907265938860719 120137490941860898908291079)
  ·
    refine ⟨180206236412791348362436619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120137490941860898908291079 180206236412791348362436619)
    ·
      refine ⟨270309354619187022543654929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180206236412791348362436619 270309354619187022543654929)
      ·
        refine ⟨202732015964390266907741197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270309354619187022543654929 202732015964390266907741197)
        ·
          refine ⟨76024505986646350090402949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202732015964390266907741197 76024505986646350090402949)
          ·
            refine ⟨14254594872496190641950553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76024505986646350090402949 14254594872496190641950553)
            ·
              refine ⟨10690946154372142981462915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14254594872496190641950553 10690946154372142981462915)
              ·
                refine ⟨16036419231558214472194373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10690946154372142981462915 16036419231558214472194373)
                ·
                  refine ⟨3006828605917165213536445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16036419231558214472194373 3006828605917165213536445)
                  ·
                    refine ⟨1127560727218936955076167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006828605917165213536445 1127560727218936955076167)
                    ·
                      rfl

theorem cell22_3293875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].length) (baseStart_3293875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293875 prefixEnd_3293875 := by exact prefixLift 3293875
  have htrace : WordTrace (prefixWord ++ tailWord_3293875) baseStart_3293875 baseEnd_3293875 := by
    simpa [prefixWord, tailWord_3293875, baseEnd_3293875] using wordTrace_append hprefix tailTrace_3293875
  have hstable : (prefixWord ++ tailWord_3293875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293875).length < 2 ^ (prefixWord ++ tailWord_3293875).sum := by decide
  have hdescent : baseEnd_3293875 < baseStart_3293875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293877 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 6]
def baseStart_3293877 : Nat := 118140960795 + 3293877 * 2 ^ 59
def prefixEnd_3293877 : Nat := 4983230072969 + 3 ^ 40 * 3293877 * 2
def baseEnd_3293877 : Nat := 375853803953269872175387

theorem tailTrace_3293877 : CollatzResearch.WordTrace tailWord_3293877 prefixEnd_3293877 375853803953269872175387 := by
  unfold tailWord_3293877
  simp only [CollatzResearch.WordTrace]
  refine ⟨120137563887853653249863885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80091709258569102166575923 120137563887853653249863885)
  ·
    refine ⟨45051586457945119968698957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120137563887853653249863885 45051586457945119968698957)
    ·
      refine ⟨16894344921729419988262109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45051586457945119968698957 16894344921729419988262109)
      ·
        refine ⟨6335379345648532495598291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16894344921729419988262109 6335379345648532495598291)
        ·
          refine ⟨9503069018472798743397437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335379345648532495598291 9503069018472798743397437)
          ·
            refine ⟨3563650881927299528774039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9503069018472798743397437 3563650881927299528774039)
            ·
              refine ⟨5345476322890949293161059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563650881927299528774039 5345476322890949293161059)
              ·
                refine ⟨8018214484336423939741589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345476322890949293161059 8018214484336423939741589)
                ·
                  refine ⟨375853803953269872175387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8018214484336423939741589 375853803953269872175387)
                  ·
                    rfl

theorem cell22_3293877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_3293877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293877 prefixEnd_3293877 := by exact prefixLift 3293877
  have htrace : WordTrace (prefixWord ++ tailWord_3293877) baseStart_3293877 baseEnd_3293877 := by
    simpa [prefixWord, tailWord_3293877, baseEnd_3293877] using wordTrace_append hprefix tailTrace_3293877
  have hstable : (prefixWord ++ tailWord_3293877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293877).length < 2 ^ (prefixWord ++ tailWord_3293877).sum := by decide
  have hdescent : baseEnd_3293877 < baseStart_3293877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293888 : List Nat := [2, 1, 1, 2, 4, 2, 1, 9]
def baseStart_3293888 : Nat := 118140960795 + 3293888 * 2 ^ 59
def prefixEnd_3293888 : Nat := 4983230072969 + 3 ^ 40 * 3293888 * 2
def baseEnd_3293888 : Nat := 125285019709401028277903

theorem tailTrace_3293888 : CollatzResearch.WordTrace tailWord_3293888 prefixEnd_3293888 125285019709401028277903 := by
  unfold tailWord_3293888
  simp only [CollatzResearch.WordTrace]
  refine ⟨60068982545406901064257159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80091976727209201419009545 60068982545406901064257159)
  ·
    refine ⟨90103473818110351596385739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60068982545406901064257159 90103473818110351596385739)
    ·
      refine ⟨135155210727165527394578609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90103473818110351596385739 135155210727165527394578609)
      ·
        refine ⟨101366408045374145545933957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135155210727165527394578609 101366408045374145545933957)
        ·
          refine ⟨19006201508507652289862617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101366408045374145545933957 19006201508507652289862617)
          ·
            refine ⟨14254651131380739217396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19006201508507652289862617 14254651131380739217396963)
            ·
              refine ⟨21381976697071108826095445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14254651131380739217396963 21381976697071108826095445)
              ·
                refine ⟨125285019709401028277903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21381976697071108826095445 125285019709401028277903)
                ·
                  rfl

theorem cell22_3293888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_3293888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293888 prefixEnd_3293888 := by exact prefixLift 3293888
  have htrace : WordTrace (prefixWord ++ tailWord_3293888) baseStart_3293888 baseEnd_3293888 := by
    simpa [prefixWord, tailWord_3293888, baseEnd_3293888] using wordTrace_append hprefix tailTrace_3293888
  have hstable : (prefixWord ++ tailWord_3293888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293888).length < 2 ^ (prefixWord ++ tailWord_3293888).sum := by decide
  have hdescent : baseEnd_3293888 < baseStart_3293888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3293954 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3293954 : Nat := 118140960795 + 3293954 * 2 ^ 59
def prefixEnd_3293954 : Nat := 4983230072969 + 3 ^ 40 * 3293954 * 2
def baseEnd_3293954 : Nat := 1127587770533407082350925

theorem tailTrace_3293954 : CollatzResearch.WordTrace tailWord_3293954 prefixEnd_3293954 1127587770533407082350925 := by
  unfold tailWord_3293954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035093077143673850104229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80093581539049796933611277 30035093077143673850104229)
  ·
    refine ⟨5631579951964438846894543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30035093077143673850104229 5631579951964438846894543)
    ·
      refine ⟨8447369927946658270341815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631579951964438846894543 8447369927946658270341815)
      ·
        refine ⟨12671054891919987405512723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8447369927946658270341815 12671054891919987405512723)
        ·
          refine ⟨19006582337879981108269085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671054891919987405512723 19006582337879981108269085)
          ·
            refine ⟨7127468376704992915600907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19006582337879981108269085 7127468376704992915600907)
            ·
              refine ⟨10691202565057489373401361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127468376704992915600907 10691202565057489373401361)
              ·
                refine ⟨8018401923793117030051021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10691202565057489373401361 8018401923793117030051021)
                ·
                  refine ⟨3006900721422418886269133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8018401923793117030051021 3006900721422418886269133)
                  ·
                    refine ⟨1127587770533407082350925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006900721422418886269133 1127587770533407082350925)
                    ·
                      rfl

theorem cell22_3293954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3293954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3293954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3293954 prefixEnd_3293954 := by exact prefixLift 3293954
  have htrace : WordTrace (prefixWord ++ tailWord_3293954) baseStart_3293954 baseEnd_3293954 := by
    simpa [prefixWord, tailWord_3293954, baseEnd_3293954] using wordTrace_append hprefix tailTrace_3293954
  have hstable : (prefixWord ++ tailWord_3293954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3293954).length < 2 ^ (prefixWord ++ tailWord_3293954).sum := by decide
  have hdescent : baseEnd_3293954 < baseStart_3293954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3293954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294022 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3294022 : Nat := 118140960795 + 3294022 * 2 ^ 59
def prefixEnd_3294022 : Nat := 4983230072969 + 3 ^ 40 * 3294022 * 2
def baseEnd_3294022 : Nat := 1127611048323077571650717

theorem tailTrace_3294022 : CollatzResearch.WordTrace tailWord_3294022 prefixEnd_3294022 1127611048323077571650717 := by
  unfold tailWord_3294022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754464139760260719184135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80095234981552228675928213 3754464139760260719184135)
  ·
    refine ⟨5631696209640391078776203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3754464139760260719184135 5631696209640391078776203)
    ·
      refine ⟨8447544314460586618164305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631696209640391078776203 8447544314460586618164305)
      ·
        refine ⟨6335658235845439963623229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8447544314460586618164305 6335658235845439963623229)
        ·
          refine ⟨2375871838442039986358711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6335658235845439963623229 2375871838442039986358711)
          ·
            refine ⟨3563807757663059979538067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375871838442039986358711 3563807757663059979538067)
            ·
              refine ⟨5345711636494589969307101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563807757663059979538067 5345711636494589969307101)
              ·
                refine ⟨2004641863685471238490163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5345711636494589969307101 2004641863685471238490163)
                ·
                  refine ⟨3006962795528206857735245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004641863685471238490163 3006962795528206857735245)
                  ·
                    refine ⟨1127611048323077571650717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006962795528206857735245 1127611048323077571650717)
                    ·
                      rfl

theorem cell22_3294022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3294022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294022 prefixEnd_3294022 := by exact prefixLift 3294022
  have htrace : WordTrace (prefixWord ++ tailWord_3294022) baseStart_3294022 baseEnd_3294022 := by
    simpa [prefixWord, tailWord_3294022, baseEnd_3294022] using wordTrace_append hprefix tailTrace_3294022
  have hstable : (prefixWord ++ tailWord_3294022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294022).length < 2 ^ (prefixWord ++ tailWord_3294022).sum := by decide
  have hdescent : baseEnd_3294022 < baseStart_3294022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294025 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_3294025 : Nat := 118140960795 + 3294025 * 2 ^ 59
def prefixEnd_3294025 : Nat := 4983230072969 + 3 ^ 40 * 3294025 * 2
def baseEnd_3294025 : Nat := 1127612075284386563825707

theorem tailTrace_3294025 : CollatzResearch.WordTrace tailWord_3294025 prefixEnd_3294025 1127612075284386563825707 := by
  unfold tailWord_3294025
  simp only [CollatzResearch.WordTrace]
  refine ⟨120142961891317474526251529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80095307927544983017501019 120142961891317474526251529)
  ·
    refine ⟨90107221418488105894688647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120142961891317474526251529 90107221418488105894688647)
    ·
      refine ⟨135160832127732158842032971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90107221418488105894688647 135160832127732158842032971)
      ·
        refine ⟨202741248191598238263049457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135160832127732158842032971 202741248191598238263049457)
        ·
          refine ⟨152055936143698678697287093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202741248191598238263049457 152055936143698678697287093)
          ·
            refine ⟨14255244013471751127870665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152055936143698678697287093 14255244013471751127870665)
            ·
              refine ⟨10691433010103813345902999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14255244013471751127870665 10691433010103813345902999)
              ·
                refine ⟨16037149515155720018854499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691433010103813345902999 16037149515155720018854499)
                ·
                  refine ⟨24055724272733580028281749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16037149515155720018854499 24055724272733580028281749)
                  ·
                    refine ⟨1127612075284386563825707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24055724272733580028281749 1127612075284386563825707)
                    ·
                      rfl

theorem cell22_3294025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_3294025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294025 prefixEnd_3294025 := by exact prefixLift 3294025
  have htrace : WordTrace (prefixWord ++ tailWord_3294025) baseStart_3294025 baseEnd_3294025 := by
    simpa [prefixWord, tailWord_3294025, baseEnd_3294025] using wordTrace_append hprefix tailTrace_3294025
  have hstable : (prefixWord ++ tailWord_3294025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294025).length < 2 ^ (prefixWord ++ tailWord_3294025).sum := by decide
  have hdescent : baseEnd_3294025 < baseStart_3294025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294042 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_3294042 : Nat := 118140960795 + 3294042 * 2 ^ 59
def prefixEnd_3294042 : Nat := 4983230072969 + 3 ^ 40 * 3294042 * 2
def baseEnd_3294042 : Nat := 1127617894731804186150655

theorem tailTrace_3294042 : CollatzResearch.WordTrace tailWord_3294042 prefixEnd_3294042 1127617894731804186150655 := by
  unfold tailWord_3294042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035895483063971607405095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80095721288170590953080253 30035895483063971607405095)
  ·
    refine ⟨45053843224595957411107643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30035895483063971607405095 45053843224595957411107643)
    ·
      refine ⟨67580764836893936116661465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45053843224595957411107643 67580764836893936116661465)
      ·
        refine ⟨50685573627670452087496099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67580764836893936116661465 50685573627670452087496099)
        ·
          refine ⟨76028360441505678131244149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50685573627670452087496099 76028360441505678131244149)
          ·
            refine ⟨7127658791391157324804139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76028360441505678131244149 7127658791391157324804139)
            ·
              refine ⟨10691488187086735987206209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127658791391157324804139 10691488187086735987206209)
              ·
                refine ⟨8018616140315051990404657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10691488187086735987206209 8018616140315051990404657)
                ·
                  refine ⟨6013962105236288992803493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8018616140315051990404657 6013962105236288992803493)
                  ·
                    refine ⟨1127617894731804186150655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6013962105236288992803493 1127617894731804186150655)
                    ·
                      rfl

theorem cell22_3294042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_3294042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294042 prefixEnd_3294042 := by exact prefixLift 3294042
  have htrace : WordTrace (prefixWord ++ tailWord_3294042) baseStart_3294042 baseEnd_3294042 := by
    simpa [prefixWord, tailWord_3294042, baseEnd_3294042] using wordTrace_append hprefix tailTrace_3294042
  have hstable : (prefixWord ++ tailWord_3294042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294042).length < 2 ^ (prefixWord ++ tailWord_3294042).sum := by decide
  have hdescent : baseEnd_3294042 < baseStart_3294042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294044 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3294044 : Nat := 118140960795 + 3294044 * 2 ^ 59
def prefixEnd_3294044 : Nat := 4983230072969 + 3 ^ 40 * 3294044 * 2
def baseEnd_3294044 : Nat := 1127618579372676847600649

theorem tailTrace_3294044 : CollatzResearch.WordTrace tailWord_3294044 prefixEnd_3294044 1127618579372676847600649 := by
  unfold tailWord_3294044
  simp only [CollatzResearch.WordTrace]
  refine ⟨60071827439124320385596593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80095769918832427180795457 60071827439124320385596593)
  ·
    refine ⟨45053870579343240289197445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60071827439124320385596593 45053870579343240289197445)
    ·
      refine ⟨8447600733626857554224521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45053870579343240289197445 8447600733626857554224521)
      ·
        refine ⟨6335700550220143165668391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8447600733626857554224521 6335700550220143165668391)
        ·
          refine ⟨9503550825330214748502587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335700550220143165668391 9503550825330214748502587)
          ·
            refine ⟨14255326237995322122753881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503550825330214748502587 14255326237995322122753881)
            ·
              refine ⟨10691494678496491592065411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14255326237995322122753881 10691494678496491592065411)
              ·
                refine ⟨16037242017744737388098117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10691494678496491592065411 16037242017744737388098117)
                ·
                  refine ⟨3006982878327138260268397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16037242017744737388098117 3006982878327138260268397)
                  ·
                    refine ⟨1127618579372676847600649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3006982878327138260268397 1127618579372676847600649)
                    ·
                      rfl

theorem cell22_3294044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3294044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294044 prefixEnd_3294044 := by exact prefixLift 3294044
  have htrace : WordTrace (prefixWord ++ tailWord_3294044) baseStart_3294044 baseEnd_3294044 := by
    simpa [prefixWord, tailWord_3294044, baseEnd_3294044] using wordTrace_append hprefix tailTrace_3294044
  have hstable : (prefixWord ++ tailWord_3294044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294044).length < 2 ^ (prefixWord ++ tailWord_3294044).sum := by decide
  have hdescent : baseEnd_3294044 < baseStart_3294044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294164 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3294164 : Nat := 118140960795 + 3294164 * 2 ^ 59
def prefixEnd_3294164 : Nat := 4983230072969 + 3 ^ 40 * 3294164 * 2
def baseEnd_3294164 : Nat := 375886552608345511533427

theorem tailTrace_3294164 : CollatzResearch.WordTrace tailWord_3294164 prefixEnd_3294164 375886552608345511533427 := by
  unfold tailWord_3294164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60074015818906950632780773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80098687758542600843707697 60074015818906950632780773)
  ·
    refine ⟨11263877966045053243646395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60074015818906950632780773 11263877966045053243646395)
    ·
      refine ⟨16895816949067579865469593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263877966045053243646395 16895816949067579865469593)
      ·
        refine ⟨12671862711800684899102195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16895816949067579865469593 12671862711800684899102195)
        ·
          refine ⟨19007794067701027348653293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671862711800684899102195 19007794067701027348653293)
          ·
            refine ⟨7127922775387885255744985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19007794067701027348653293 7127922775387885255744985)
            ·
              refine ⟨5345942081540913941808739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7127922775387885255744985 5345942081540913941808739)
              ·
                refine ⟨8018913122311370912713109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345942081540913941808739 8018913122311370912713109)
                ·
                  refine ⟨375886552608345511533427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8018913122311370912713109 375886552608345511533427)
                  ·
                    rfl

theorem cell22_3294164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3294164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294164 prefixEnd_3294164 := by exact prefixLift 3294164
  have htrace : WordTrace (prefixWord ++ tailWord_3294164) baseStart_3294164 baseEnd_3294164 := by
    simpa [prefixWord, tailWord_3294164, baseEnd_3294164] using wordTrace_append hprefix tailTrace_3294164
  have hstable : (prefixWord ++ tailWord_3294164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294164).length < 2 ^ (prefixWord ++ tailWord_3294164).sum := by decide
  have hdescent : baseEnd_3294164 < baseStart_3294164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294198 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_3294198 : Nat := 118140960795 + 3294198 * 2 ^ 59
def prefixEnd_3294198 : Nat := 4983230072969 + 3 ^ 40 * 3294198 * 2
def baseEnd_3294198 : Nat := 375890432239957259750059

theorem tailTrace_3294198 : CollatzResearch.WordTrace tailWord_3294198 prefixEnd_3294198 375890432239957259750059 := by
  unfold tailWord_3294198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509329482480670317018703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80099514479793816714866165 7509329482480670317018703)
  ·
    refine ⟨11263994223721005475528055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509329482480670317018703 11263994223721005475528055)
    ·
      refine ⟨16895991335581508213292083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263994223721005475528055 16895991335581508213292083)
      ·
        refine ⟨25343987003372262319938125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16895991335581508213292083 25343987003372262319938125)
        ·
          refine ⟨9503995126264598369976797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25343987003372262319938125 9503995126264598369976797)
          ·
            refine ⟨3563998172349224388741299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9503995126264598369976797 3563998172349224388741299)
            ·
              refine ⟨5345997258523836583111949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563998172349224388741299 5345997258523836583111949)
              ·
                refine ⟨2004748971946438718666981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5345997258523836583111949 2004748971946438718666981)
                ·
                  refine ⟨375890432239957259750059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004748971946438718666981 375890432239957259750059)
                  ·
                    rfl

theorem cell22_3294198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_3294198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294198 prefixEnd_3294198 := by exact prefixLift 3294198
  have htrace : WordTrace (prefixWord ++ tailWord_3294198) baseStart_3294198 baseEnd_3294198 := by
    simpa [prefixWord, tailWord_3294198, baseEnd_3294198] using wordTrace_append hprefix tailTrace_3294198
  have hstable : (prefixWord ++ tailWord_3294198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294198).length < 2 ^ (prefixWord ++ tailWord_3294198).sum := by decide
  have hdescent : baseEnd_3294198 < baseStart_3294198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294267 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_3294267 : Nat := 118140960795 + 3294267 * 2 ^ 59
def prefixEnd_3294267 : Nat := 4983230072969 + 3 ^ 40 * 3294267 * 2
def baseEnd_3294267 : Nat := 1127694916829978599274965

theorem tailTrace_3294267 : CollatzResearch.WordTrace tailWord_3294267 prefixEnd_3294267 1127694916829978599274965 := by
  unfold tailWord_3294267
  simp only [CollatzResearch.WordTrace]
  refine ⟨120151788356440749856561055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80101192237627166571040703 120151788356440749856561055)
  ·
    refine ⟨180227682534661124784841583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120151788356440749856561055 180227682534661124784841583)
    ·
      refine ⟨270341523801991687177262375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180227682534661124784841583 270341523801991687177262375)
      ·
        refine ⟨405512285702987530765893563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270341523801991687177262375 405512285702987530765893563)
        ·
          refine ⟨608268428554481296148840345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405512285702987530765893563 608268428554481296148840345)
          ·
            refine ⟨456201321415860972111630259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608268428554481296148840345 456201321415860972111630259)
            ·
              refine ⟨684301982123791458167445389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456201321415860972111630259 684301982123791458167445389)
              ·
                refine ⟨256613243296421796812792021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684301982123791458167445389 256613243296421796812792021)
                ·
                  refine ⟨6014372889759885862799813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 256613243296421796812792021 6014372889759885862799813)
                  ·
                    refine ⟨1127694916829978599274965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014372889759885862799813 1127694916829978599274965)
                    ·
                      rfl

theorem cell22_3294267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_3294267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294267 prefixEnd_3294267 := by exact prefixLift 3294267
  have htrace : WordTrace (prefixWord ++ tailWord_3294267) baseStart_3294267 baseEnd_3294267 := by
    simpa [prefixWord, tailWord_3294267, baseEnd_3294267] using wordTrace_append hprefix tailTrace_3294267
  have hstable : (prefixWord ++ tailWord_3294267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294267).length < 2 ^ (prefixWord ++ tailWord_3294267).sum := by decide
  have hdescent : baseEnd_3294267 < baseStart_3294267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294316 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_3294316 : Nat := 118140960795 + 3294316 * 2 ^ 59
def prefixEnd_3294316 : Nat := 4983230072969 + 3 ^ 40 * 3294316 * 2
def baseEnd_3294316 : Nat := 375903896843786268266605

theorem tailTrace_3294316 : CollatzResearch.WordTrace tailWord_3294316 prefixEnd_3294316 375903896843786268266605 := by
  unfold tailWord_3294316
  simp only [CollatzResearch.WordTrace]
  refine ⟨60076787766631615612547401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80102383688842154150063201 60076787766631615612547401)
  ·
    refine ⟨45057590824973711709410551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60076787766631615612547401 45057590824973711709410551)
    ·
      refine ⟨67586386237460567564115827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45057590824973711709410551 67586386237460567564115827)
      ·
        refine ⟨101379579356190851346173741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67586386237460567564115827 101379579356190851346173741)
        ·
          refine ⟨38017342258571569254815153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101379579356190851346173741 38017342258571569254815153)
          ·
            refine ⟨28513006693928676941111365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38017342258571569254815153 28513006693928676941111365)
            ·
              refine ⟨5346188755111626926458381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28513006693928676941111365 5346188755111626926458381)
              ·
                refine ⟨2004820783166860097421893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5346188755111626926458381 2004820783166860097421893)
                ·
                  refine ⟨375903896843786268266605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004820783166860097421893 375903896843786268266605)
                  ·
                    rfl

theorem cell22_3294316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_3294316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294316 prefixEnd_3294316 := by exact prefixLift 3294316
  have htrace : WordTrace (prefixWord ++ tailWord_3294316) baseStart_3294316 baseEnd_3294316 := by
    simpa [prefixWord, tailWord_3294316, baseEnd_3294316] using wordTrace_append hprefix tailTrace_3294316
  have hstable : (prefixWord ++ tailWord_3294316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294316).length < 2 ^ (prefixWord ++ tailWord_3294316).sum := by decide
  have hdescent : baseEnd_3294316 < baseStart_3294316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294318 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3294318 : Nat := 118140960795 + 3294318 * 2 ^ 59
def prefixEnd_3294318 : Nat := 4983230072969 + 3 ^ 40 * 3294318 * 2
def baseEnd_3294318 : Nat := 1127712375172231466249809

theorem tailTrace_3294318 : CollatzResearch.WordTrace tailWord_3294318 prefixEnd_3294318 1127712375172231466249809 := by
  unfold tailWord_3294318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019206059906998195833451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80102432319503990377778405 15019206059906998195833451)
  ·
    refine ⟨22528809089860497293750177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019206059906998195833451 22528809089860497293750177)
    ·
      refine ⟨16896606817395372970312633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22528809089860497293750177 16896606817395372970312633)
      ·
        refine ⟨12672455113046529727734475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16896606817395372970312633 12672455113046529727734475)
        ·
          refine ⟨19008682669569794591601713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12672455113046529727734475 19008682669569794591601713)
          ·
            refine ⟨14256512002177345943701285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19008682669569794591601713 14256512002177345943701285)
            ·
              refine ⟨2673096000408252364443991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14256512002177345943701285 2673096000408252364443991)
              ·
                refine ⟨4009644000612378546665987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673096000408252364443991 4009644000612378546665987)
                ·
                  refine ⟨6014466000918567819998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009644000612378546665987 6014466000918567819998981)
                  ·
                    refine ⟨1127712375172231466249809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014466000918567819998981 1127712375172231466249809)
                    ·
                      rfl

theorem cell22_3294318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3294318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294318 prefixEnd_3294318 := by exact prefixLift 3294318
  have htrace : WordTrace (prefixWord ++ tailWord_3294318) baseStart_3294318 baseEnd_3294318 := by
    simpa [prefixWord, tailWord_3294318, baseEnd_3294318] using wordTrace_append hprefix tailTrace_3294318
  have hstable : (prefixWord ++ tailWord_3294318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294318).length < 2 ^ (prefixWord ++ tailWord_3294318).sum := by decide
  have hdescent : baseEnd_3294318 < baseStart_3294318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294327 : List Nat := [1, 1, 3, 1, 1, 4, 11]
def baseStart_3294327 : Nat := 118140960795 + 3294327 * 2 ^ 59
def prefixEnd_3294327 : Nat := 4983230072969 + 3 ^ 40 * 3294327 * 2
def baseEnd_3294327 : Nat := 41767239113191053436103

theorem tailTrace_3294327 : CollatzResearch.WordTrace tailWord_3294327 prefixEnd_3294327 41767239113191053436103 := by
  unfold tailWord_3294327
  simp only [CollatzResearch.WordTrace]
  refine ⟨120153976736223380103745235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80102651157482253402496823 120153976736223380103745235)
  ·
    refine ⟨180230965104335070155617853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120153976736223380103745235 180230965104335070155617853)
    ·
      refine ⟨67586611914125651308356695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180230965104335070155617853 67586611914125651308356695)
      ·
        refine ⟨101379917871188476962535043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67586611914125651308356695 101379917871188476962535043)
        ·
          refine ⟨152069876806782715443802565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101379917871188476962535043 152069876806782715443802565)
          ·
            refine ⟨28513101901271759145712981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152069876806782715443802565 28513101901271759145712981)
            ·
              refine ⟨41767239113191053436103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28513101901271759145712981 41767239113191053436103)
              ·
                rfl

theorem cell22_3294327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 11].length) (baseStart_3294327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294327 prefixEnd_3294327 := by exact prefixLift 3294327
  have htrace : WordTrace (prefixWord ++ tailWord_3294327) baseStart_3294327 baseEnd_3294327 := by
    simpa [prefixWord, tailWord_3294327, baseEnd_3294327] using wordTrace_append hprefix tailTrace_3294327
  have hstable : (prefixWord ++ tailWord_3294327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294327).length < 2 ^ (prefixWord ++ tailWord_3294327).sum := by decide
  have hdescent : baseEnd_3294327 < baseStart_3294327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294393 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_3294393 : Nat := 118140960795 + 3294393 * 2 ^ 59
def prefixEnd_3294393 : Nat := 4983230072969 + 3 ^ 40 * 3294393 * 2
def baseEnd_3294393 : Nat := 1127738049204956270624579

theorem tailTrace_3294393 : CollatzResearch.WordTrace tailWord_3294393 prefixEnd_3294393 1127738049204956270624579 := by
  unfold tailWord_3294393
  simp only [CollatzResearch.WordTrace]
  refine ⟨120156383953984273375647833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80104255969322848917098555 120156383953984273375647833)
  ·
    refine ⟨90117287965488205031735875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120156383953984273375647833 90117287965488205031735875)
    ·
      refine ⟨135175931948232307547603813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90117287965488205031735875 135175931948232307547603813)
      ·
        refine ⟨25345487240293557665175715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135175931948232307547603813 25345487240293557665175715)
        ·
          refine ⟨38018230860440336497763573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25345487240293557665175715 38018230860440336497763573)
          ·
            refine ⟨3564209143166281546665335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38018230860440336497763573 3564209143166281546665335)
            ·
              refine ⟨5346313714749422319998003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564209143166281546665335 5346313714749422319998003)
              ·
                refine ⟨8019470572124133479997005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5346313714749422319998003 8019470572124133479997005)
                ·
                  refine ⟨3007301464546550054998877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8019470572124133479997005 3007301464546550054998877)
                  ·
                    refine ⟨1127738049204956270624579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3007301464546550054998877 1127738049204956270624579)
                    ·
                      rfl

theorem cell22_3294393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_3294393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294393 prefixEnd_3294393 := by exact prefixLift 3294393
  have htrace : WordTrace (prefixWord ++ tailWord_3294393) baseStart_3294393 baseEnd_3294393 := by
    simpa [prefixWord, tailWord_3294393, baseEnd_3294393] using wordTrace_append hprefix tailTrace_3294393
  have hstable : (prefixWord ++ tailWord_3294393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294393).length < 2 ^ (prefixWord ++ tailWord_3294393).sum := by decide
  have hdescent : baseEnd_3294393 < baseStart_3294393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294419 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_3294419 : Nat := 118140960795 + 3294419 * 2 ^ 59
def prefixEnd_3294419 : Nat := 4983230072969 + 3 ^ 40 * 3294419 * 2
def baseEnd_3294419 : Nat := 1127746949536300869474499

theorem tailTrace_3294419 : CollatzResearch.WordTrace tailWord_3294419 prefixEnd_3294419 1127746949536300869474499 := by
  unfold tailWord_3294419
  simp only [CollatzResearch.WordTrace]
  refine ⟨120157332251890079816094311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80104888167926719877396207 120157332251890079816094311)
  ·
    refine ⟨180235998377835119724141467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120157332251890079816094311 180235998377835119724141467)
    ·
      refine ⟨270353997566752679586212201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180235998377835119724141467 270353997566752679586212201)
      ·
        refine ⟨202765498175064509689659151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270353997566752679586212201 202765498175064509689659151)
        ·
          refine ⟨304148247262596764534488727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202765498175064509689659151 304148247262596764534488727)
          ·
            refine ⟨456222370893895146801733091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304148247262596764534488727 456222370893895146801733091)
            ·
              refine ⟨684333556340842720202599637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456222370893895146801733091 684333556340842720202599637)
              ·
                refine ⟨16039067726738501254748429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 684333556340842720202599637 16039067726738501254748429)
                ·
                  refine ⟨6014650397526937970530661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16039067726738501254748429 6014650397526937970530661)
                  ·
                    refine ⟨1127746949536300869474499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014650397526937970530661 1127746949536300869474499)
                    ·
                      rfl

theorem cell22_3294419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_3294419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294419 prefixEnd_3294419 := by exact prefixLift 3294419
  have htrace : WordTrace (prefixWord ++ tailWord_3294419) baseStart_3294419 baseEnd_3294419 := by
    simpa [prefixWord, tailWord_3294419, baseEnd_3294419] using wordTrace_append hprefix tailTrace_3294419
  have hstable : (prefixWord ++ tailWord_3294419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294419).length < 2 ^ (prefixWord ++ tailWord_3294419).sum := by decide
  have hdescent : baseEnd_3294419 < baseStart_3294419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294436 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3294436 : Nat := 118140960795 + 3294436 * 2 ^ 59
def prefixEnd_3294436 : Nat := 4983230072969 + 3 ^ 40 * 3294436 * 2
def baseEnd_3294436 : Nat := 1127752768983718491799447

theorem tailTrace_3294436 : CollatzResearch.WordTrace tailWord_3294436 prefixEnd_3294436 1127752768983718491799447 := by
  unfold tailWord_3294436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60078976146414245859731581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80105301528552327812975441 60078976146414245859731581)
  ·
    refine ⟨22529616054905342197399343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60078976146414245859731581 22529616054905342197399343)
    ·
      refine ⟨33794424082358013296099015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529616054905342197399343 33794424082358013296099015)
      ·
        refine ⟨50691636123537019944148523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33794424082358013296099015 50691636123537019944148523)
        ·
          refine ⟨76037454185305529916222785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50691636123537019944148523 76037454185305529916222785)
          ·
            refine ⟨57028090638979147437167089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76037454185305529916222785 57028090638979147437167089)
            ·
              refine ⟨42771067979234360577875317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57028090638979147437167089 42771067979234360577875317)
              ·
                refine ⟨4009787623053221304175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42771067979234360577875317 4009787623053221304175811)
                ·
                  refine ⟨6014681434579831956263717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009787623053221304175811 6014681434579831956263717)
                  ·
                    refine ⟨1127752768983718491799447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6014681434579831956263717 1127752768983718491799447)
                    ·
                      rfl

theorem cell22_3294436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3294436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294436 prefixEnd_3294436 := by exact prefixLift 3294436
  have htrace : WordTrace (prefixWord ++ tailWord_3294436) baseStart_3294436 baseEnd_3294436 := by
    simpa [prefixWord, tailWord_3294436, baseEnd_3294436] using wordTrace_append hprefix tailTrace_3294436
  have hstable : (prefixWord ++ tailWord_3294436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294436).length < 2 ^ (prefixWord ++ tailWord_3294436).sum := by decide
  have hdescent : baseEnd_3294436 < baseStart_3294436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294449 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3294449 : Nat := 118140960795 + 3294449 * 2 ^ 59
def prefixEnd_3294449 : Nat := 4983230072969 + 3 ^ 40 * 3294449 * 2
def baseEnd_3294449 : Nat := 1127757219149390791224407

theorem tailTrace_3294449 : CollatzResearch.WordTrace tailWord_3294449 prefixEnd_3294449 1127757219149390791224407 := by
  unfold tailWord_3294449
  simp only [CollatzResearch.WordTrace]
  refine ⟨120158426441781394939686401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80105617627854263293124267 120158426441781394939686401)
  ·
    refine ⟨90118819831336046204764801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120158426441781394939686401 90118819831336046204764801)
    ·
      refine ⟨67589114873502034653573601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90118819831336046204764801 67589114873502034653573601)
      ·
        refine ⟨50691836155126525990180201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67589114873502034653573601 50691836155126525990180201)
        ·
          refine ⟨38018877116344894492635151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50691836155126525990180201 38018877116344894492635151)
          ·
            refine ⟨57028315674517341738952727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38018877116344894492635151 57028315674517341738952727)
            ·
              refine ⟨85542473511776012608429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57028315674517341738952727 85542473511776012608429091)
              ·
                refine ⟨128313710267664018912643637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85542473511776012608429091 128313710267664018912643637)
                ·
                  refine ⟨12029410337593501773060341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128313710267664018912643637 12029410337593501773060341)
                  ·
                    refine ⟨1127757219149390791224407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12029410337593501773060341 1127757219149390791224407)
                    ·
                      rfl

theorem cell22_3294449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3294449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294449 prefixEnd_3294449 := by exact prefixLift 3294449
  have htrace : WordTrace (prefixWord ++ tailWord_3294449) baseStart_3294449 baseEnd_3294449 := by
    simpa [prefixWord, tailWord_3294449, baseEnd_3294449] using wordTrace_append hprefix tailTrace_3294449
  have hstable : (prefixWord ++ tailWord_3294449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294449).length < 2 ^ (prefixWord ++ tailWord_3294449).sum := by decide
  have hdescent : baseEnd_3294449 < baseStart_3294449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294464 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_3294464 : Nat := 118140960795 + 3294464 * 2 ^ 59
def prefixEnd_3294464 : Nat := 4983230072969 + 3 ^ 40 * 3294464 * 2
def baseEnd_3294464 : Nat := 1127762353955935752099361

theorem tailTrace_3294464 : CollatzResearch.WordTrace tailWord_3294464 prefixEnd_3294464 1127762353955935752099361 := by
  unfold tailWord_3294464
  simp only [CollatzResearch.WordTrace]
  refine ⟨60079486768363526250741223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80105982357818035000988297 60079486768363526250741223)
  ·
    refine ⟨90119230152545289376111835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60079486768363526250741223 90119230152545289376111835)
    ·
      refine ⟨135178845228817934064167753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90119230152545289376111835 135178845228817934064167753)
      ·
        refine ⟨101384133921613450548125815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135178845228817934064167753 101384133921613450548125815)
        ·
          refine ⟨152076200882420175822188723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101384133921613450548125815 152076200882420175822188723)
          ·
            refine ⟨228114301323630263733283085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152076200882420175822188723 228114301323630263733283085)
            ·
              refine ⟨85542862996361348899981157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228114301323630263733283085 85542862996361348899981157)
              ·
                refine ⟨16039286811817752918746467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85542862996361348899981157 16039286811817752918746467)
                ·
                  refine ⟨24058930217726629378119701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16039286811817752918746467 24058930217726629378119701)
                  ·
                    refine ⟨1127762353955935752099361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24058930217726629378119701 1127762353955935752099361)
                    ·
                      rfl

theorem cell22_3294464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_3294464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294464 prefixEnd_3294464 := by exact prefixLift 3294464
  have htrace : WordTrace (prefixWord ++ tailWord_3294464) baseStart_3294464 baseEnd_3294464 := by
    simpa [prefixWord, tailWord_3294464, baseEnd_3294464] using wordTrace_append hprefix tailTrace_3294464
  have hstable : (prefixWord ++ tailWord_3294464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294464).length < 2 ^ (prefixWord ++ tailWord_3294464).sum := by decide
  have hdescent : baseEnd_3294464 < baseStart_3294464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294496 : List Nat := [2, 1, 1, 5, 3, 1, 9]
def baseStart_3294496 : Nat := 118140960795 + 3294496 * 2 ^ 59
def prefixEnd_3294496 : Nat := 4983230072969 + 3 ^ 40 * 3294496 * 2
def baseEnd_3294496 : Nat := 41769381785551790196269

theorem tailTrace_3294496 : CollatzResearch.WordTrace tailWord_3294496 prefixEnd_3294496 41769381785551790196269 := by
  unfold tailWord_3294496
  simp only [CollatzResearch.WordTrace]
  refine ⟨60080070336305560983323671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80106760448407414644431561 60080070336305560983323671)
  ·
    refine ⟨90120105504458341474985507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60080070336305560983323671 90120105504458341474985507)
    ·
      refine ⟨135180158256687512212478261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90120105504458341474985507 135180158256687512212478261)
      ·
        refine ⟨12673139836564454269919837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135180158256687512212478261 12673139836564454269919837)
        ·
          refine ⟨4752427438711670351219939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12673139836564454269919837 4752427438711670351219939)
          ·
            refine ⟨7128641158067505526829909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752427438711670351219939 7128641158067505526829909)
            ·
              refine ⟨41769381785551790196269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7128641158067505526829909 41769381785551790196269)
              ·
                rfl

theorem cell22_3294496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 9].length) (baseStart_3294496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294496 prefixEnd_3294496 := by exact prefixLift 3294496
  have htrace : WordTrace (prefixWord ++ tailWord_3294496) baseStart_3294496 baseEnd_3294496 := by
    simpa [prefixWord, tailWord_3294496, baseEnd_3294496] using wordTrace_append hprefix tailTrace_3294496
  have hstable : (prefixWord ++ tailWord_3294496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294496).length < 2 ^ (prefixWord ++ tailWord_3294496).sum := by decide
  have hdescent : baseEnd_3294496 < baseStart_3294496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294603 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 4]
def baseStart_3294603 : Nat := 118140960795 + 3294603 * 2 ^ 59
def prefixEnd_3294603 : Nat := 4983230072969 + 3 ^ 40 * 3294603 * 2
def baseEnd_3294603 : Nat := 375936645498861907624645

theorem tailTrace_3294603 : CollatzResearch.WordTrace tailWord_3294603 prefixEnd_3294603 375936645498861907624645 := by
  unfold tailWord_3294603
  simp only [CollatzResearch.WordTrace]
  refine ⟨120164043283223479240792463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80109362188815652827194975 120164043283223479240792463)
  ·
    refine ⟨180246064924835218861188695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120164043283223479240792463 180246064924835218861188695)
    ·
      refine ⟨270369097387252828291783043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180246064924835218861188695 270369097387252828291783043)
      ·
        refine ⟨405553646080879242437674565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270369097387252828291783043 405553646080879242437674565)
        ·
          refine ⟨76041308640164857957063981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405553646080879242437674565 76041308640164857957063981)
          ·
            refine ⟨28515490740061821733898993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76041308640164857957063981 28515490740061821733898993)
            ·
              refine ⟨21386618055046366300424245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28515490740061821733898993 21386618055046366300424245)
              ·
                refine ⟨2004995442660596840664773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21386618055046366300424245 2004995442660596840664773)
                ·
                  refine ⟨375936645498861907624645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2004995442660596840664773 375936645498861907624645)
                  ·
                    rfl

theorem cell22_3294603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 4].length) (baseStart_3294603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294603 prefixEnd_3294603 := by exact prefixLift 3294603
  have htrace : WordTrace (prefixWord ++ tailWord_3294603) baseStart_3294603 baseEnd_3294603 := by
    simpa [prefixWord, tailWord_3294603, baseEnd_3294603] using wordTrace_append hprefix tailTrace_3294603
  have hstable : (prefixWord ++ tailWord_3294603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294603).length < 2 ^ (prefixWord ++ tailWord_3294603).sum := by decide
  have hdescent : baseEnd_3294603 < baseStart_3294603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294663 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3294663 : Nat := 118140960795 + 3294663 * 2 ^ 59
def prefixEnd_3294663 : Nat := 4983230072969 + 3 ^ 40 * 3294663 * 2
def baseEnd_3294663 : Nat := 1127830475722765566373751

theorem tailTrace_3294663 : CollatzResearch.WordTrace tailWord_3294663 prefixEnd_3294663 1127830475722765566373751 := by
  unfold tailWord_3294663
  simp only [CollatzResearch.WordTrace]
  refine ⟨120166231663006109487976643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80110821108670739658651095 120166231663006109487976643)
  ·
    refine ⟨180249347494509164231964965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120166231663006109487976643 180249347494509164231964965)
    ·
      refine ⟨33796752655220468293493431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180249347494509164231964965 33796752655220468293493431)
      ·
        refine ⟨50695128982830702440240147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33796752655220468293493431 50695128982830702440240147)
        ·
          refine ⟨76042693474246053660360221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50695128982830702440240147 76042693474246053660360221)
          ·
            refine ⟨28516010052842270122635083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76042693474246053660360221 28516010052842270122635083)
            ·
              refine ⟨42774015079263405183952625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28516010052842270122635083 42774015079263405183952625)
              ·
                refine ⟨32080511309447553887964469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42774015079263405183952625 32080511309447553887964469)
                ·
                  refine ⟨3007547935260708176996669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32080511309447553887964469 3007547935260708176996669)
                  ·
                    refine ⟨1127830475722765566373751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3007547935260708176996669 1127830475722765566373751)
                    ·
                      rfl

theorem cell22_3294663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3294663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294663 prefixEnd_3294663 := by exact prefixLift 3294663
  have htrace : WordTrace (prefixWord ++ tailWord_3294663) baseStart_3294663 baseEnd_3294663 := by
    simpa [prefixWord, tailWord_3294663, baseEnd_3294663] using wordTrace_append hprefix tailTrace_3294663
  have hstable : (prefixWord ++ tailWord_3294663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294663).length < 2 ^ (prefixWord ++ tailWord_3294663).sum := by decide
  have hdescent : baseEnd_3294663 < baseStart_3294663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294744 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_3294744 : Nat := 118140960795 + 3294744 * 2 ^ 59
def prefixEnd_3294744 : Nat := 4983230072969 + 3 ^ 40 * 3294744 * 2
def baseEnd_3294744 : Nat := 375952734559369451699501

theorem tailTrace_3294744 : CollatzResearch.WordTrace tailWord_3294744 prefixEnd_3294744 375952734559369451699501 := by
  unfold tailWord_3294744
  simp only [CollatzResearch.WordTrace]
  refine ⟨60084592987856330160837643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80112790650475106881116857 60084592987856330160837643)
  ·
    refine ⟨90126889481784495241256465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60084592987856330160837643 90126889481784495241256465)
    ·
      refine ⟨67595167111338371430942349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90126889481784495241256465 67595167111338371430942349)
      ·
        refine ⟨25348187666751889286603381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67595167111338371430942349 25348187666751889286603381)
        ·
          refine ⟨2376392593757989620619067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25348187666751889286603381 2376392593757989620619067)
          ·
            refine ⟨3564588890636984430928601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376392593757989620619067 3564588890636984430928601)
            ·
              refine ⟨2673441667977738323196451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3564588890636984430928601 2673441667977738323196451)
              ·
                refine ⟨4010162501966607484794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673441667977738323196451 4010162501966607484794677)
                ·
                  refine ⟨375952734559369451699501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4010162501966607484794677 375952734559369451699501)
                  ·
                    rfl

theorem cell22_3294744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_3294744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294744 prefixEnd_3294744 := by exact prefixLift 3294744
  have htrace : WordTrace (prefixWord ++ tailWord_3294744) baseStart_3294744 baseEnd_3294744 := by
    simpa [prefixWord, tailWord_3294744, baseEnd_3294744] using wordTrace_append hprefix tailTrace_3294744
  have hstable : (prefixWord ++ tailWord_3294744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294744).length < 2 ^ (prefixWord ++ tailWord_3294744).sum := by decide
  have hdescent : baseEnd_3294744 < baseStart_3294744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294785 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3294785 : Nat := 118140960795 + 3294785 * 2 ^ 59
def prefixEnd_3294785 : Nat := 4983230072969 + 3 ^ 40 * 3294785 * 2
def baseEnd_3294785 : Nat := 1127872238815997914823377

theorem tailTrace_3294785 : CollatzResearch.WordTrace tailWord_3294785 prefixEnd_3294785 1127872238815997914823377 := by
  unfold tailWord_3294785
  simp only [CollatzResearch.WordTrace]
  refine ⟨120170681368564124323917809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80113787579042749549278539 120170681368564124323917809)
  ·
    refine ⟨90128011026423093242938357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120170681368564124323917809 90128011026423093242938357)
    ·
      refine ⟨8449501033727164991525471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90128011026423093242938357 8449501033727164991525471)
      ·
        refine ⟨12674251550590747487288207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449501033727164991525471 12674251550590747487288207)
        ·
          refine ⟨19011377325886121230932311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674251550590747487288207 19011377325886121230932311)
          ·
            refine ⟨28517065988829181846398467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19011377325886121230932311 28517065988829181846398467)
            ·
              refine ⟨42775598983243772769597701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28517065988829181846398467 42775598983243772769597701)
              ·
                refine ⟨8020424809358207394299569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42775598983243772769597701 8020424809358207394299569)
                ·
                  refine ⟨6015318607018655545724677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020424809358207394299569 6015318607018655545724677)
                  ·
                    refine ⟨1127872238815997914823377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015318607018655545724677 1127872238815997914823377)
                    ·
                      rfl

theorem cell22_3294785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3294785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294785 prefixEnd_3294785 := by exact prefixLift 3294785
  have htrace : WordTrace (prefixWord ++ tailWord_3294785) baseStart_3294785 baseEnd_3294785 := by
    simpa [prefixWord, tailWord_3294785, baseEnd_3294785] using wordTrace_append hprefix tailTrace_3294785
  have hstable : (prefixWord ++ tailWord_3294785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294785).length < 2 ^ (prefixWord ++ tailWord_3294785).sum := by decide
  have hdescent : baseEnd_3294785 < baseStart_3294785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294798 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3294798 : Nat := 118140960795 + 3294798 * 2 ^ 59
def prefixEnd_3294798 : Nat := 4983230072969 + 3 ^ 40 * 3294798 * 2
def baseEnd_3294798 : Nat := 1127876688981670214248337

theorem tailTrace_3294798 : CollatzResearch.WordTrace tailWord_3294798 prefixEnd_3294798 1127876688981670214248337 := by
  unfold tailWord_3294798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021394439689628443017631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80114103678344685029427365 15021394439689628443017631)
  ·
    refine ⟨22532091659534442664526447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15021394439689628443017631 22532091659534442664526447)
    ·
      refine ⟨33798137489301663996789671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22532091659534442664526447 33798137489301663996789671)
      ·
        refine ⟨50697206233952495995184507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798137489301663996789671 50697206233952495995184507)
        ·
          refine ⟨76045809350928743992776761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50697206233952495995184507 76045809350928743992776761)
          ·
            refine ⟨57034357013196557994582571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76045809350928743992776761 57034357013196557994582571)
            ·
              refine ⟨85551535519794836991873857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57034357013196557994582571 85551535519794836991873857)
              ·
                refine ⟨64163651639846127743905393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85551535519794836991873857 64163651639846127743905393)
                ·
                  refine ⟨48122738729884595807929045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64163651639846127743905393 48122738729884595807929045)
                  ·
                    refine ⟨1127876688981670214248337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48122738729884595807929045 1127876688981670214248337)
                    ·
                      rfl

theorem cell22_3294798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3294798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294798 prefixEnd_3294798 := by exact prefixLift 3294798
  have htrace : WordTrace (prefixWord ++ tailWord_3294798) baseStart_3294798 baseEnd_3294798 := by
    simpa [prefixWord, tailWord_3294798, baseEnd_3294798] using wordTrace_append hprefix tailTrace_3294798
  have hstable : (prefixWord ++ tailWord_3294798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294798).length < 2 ^ (prefixWord ++ tailWord_3294798).sum := by decide
  have hdescent : baseEnd_3294798 < baseStart_3294798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294828 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3294828 : Nat := 118140960795 + 3294828 * 2 ^ 59
def prefixEnd_3294828 : Nat := 4983230072969 + 3 ^ 40 * 3294828 * 2
def baseEnd_3294828 : Nat := 375962319531586711999415

theorem tailTrace_3294828 : CollatzResearch.WordTrace tailWord_3294828 prefixEnd_3294828 375962319531586711999415 := by
  unfold tailWord_3294828
  simp only [CollatzResearch.WordTrace]
  refine ⟨60086124853704171333866569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80114833138272228445155425 60086124853704171333866569)
  ·
    refine ⟨45064593640278128500399927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60086124853704171333866569 45064593640278128500399927)
    ·
      refine ⟨67596890460417192750599891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45064593640278128500399927 67596890460417192750599891)
      ·
        refine ⟨101395335690625789125899837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67596890460417192750599891 101395335690625789125899837)
        ·
          refine ⟨38023250883984670922212439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101395335690625789125899837 38023250883984670922212439)
          ·
            refine ⟨57034876325977006383318659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38023250883984670922212439 57034876325977006383318659)
            ·
              refine ⟨85552314488965509574977989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57034876325977006383318659 85552314488965509574977989)
              ·
                refine ⟨16041058966681033045308373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85552314488965509574977989 16041058966681033045308373)
                ·
                  refine ⟨375962319531586711999415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16041058966681033045308373 375962319531586711999415)
                  ·
                    rfl

theorem cell22_3294828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3294828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294828 prefixEnd_3294828 := by exact prefixLift 3294828
  have htrace : WordTrace (prefixWord ++ tailWord_3294828) baseStart_3294828 baseEnd_3294828 := by
    simpa [prefixWord, tailWord_3294828, baseEnd_3294828] using wordTrace_append hprefix tailTrace_3294828
  have hstable : (prefixWord ++ tailWord_3294828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294828).length < 2 ^ (prefixWord ++ tailWord_3294828).sum := by decide
  have hdescent : baseEnd_3294828 < baseStart_3294828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294843 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_3294843 : Nat := 118140960795 + 3294843 * 2 ^ 59
def prefixEnd_3294843 : Nat := 4983230072969 + 3 ^ 40 * 3294843 * 2
def baseEnd_3294843 : Nat := 1127892093401305096873199

theorem tailTrace_3294843 : CollatzResearch.WordTrace tailWord_3294843 prefixEnd_3294843 1127892093401305096873199 := by
  unfold tailWord_3294843
  simp only [CollatzResearch.WordTrace]
  refine ⟨120172796802354000229529183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80115197868236000153019455 120172796802354000229529183)
  ·
    refine ⟨180259195203531000344293775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120172796802354000229529183 180259195203531000344293775)
    ·
      refine ⟨270388792805296500516440663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180259195203531000344293775 270388792805296500516440663)
      ·
        refine ⟨405583189207944750774660995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270388792805296500516440663 405583189207944750774660995)
        ·
          refine ⟨608374783811917126161991493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405583189207944750774660995 608374783811917126161991493)
          ·
            refine ⟨114070271964734461155373405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 608374783811917126161991493 114070271964734461155373405)
            ·
              refine ⟨42776351986775422933265027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114070271964734461155373405 42776351986775422933265027)
              ·
                refine ⟨64164527980163134399897541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42776351986775422933265027 64164527980163134399897541)
                ·
                  refine ⟨12030848996280587699980789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64164527980163134399897541 12030848996280587699980789)
                  ·
                    refine ⟨1127892093401305096873199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12030848996280587699980789 1127892093401305096873199)
                    ·
                      rfl

theorem cell22_3294843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_3294843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294843 prefixEnd_3294843 := by exact prefixLift 3294843
  have htrace : WordTrace (prefixWord ++ tailWord_3294843) baseStart_3294843 baseEnd_3294843 := by
    simpa [prefixWord, tailWord_3294843, baseEnd_3294843] using wordTrace_append hprefix tailTrace_3294843
  have hstable : (prefixWord ++ tailWord_3294843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294843).length < 2 ^ (prefixWord ++ tailWord_3294843).sum := by decide
  have hdescent : baseEnd_3294843 < baseStart_3294843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294845 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 7]
def baseStart_3294845 : Nat := 118140960795 + 3294845 * 2 ^ 59
def prefixEnd_3294845 : Nat := 4983230072969 + 3 ^ 40 * 3294845 * 2
def baseEnd_3294845 : Nat := 375964259347392586107731

theorem tailTrace_3294845 : CollatzResearch.WordTrace tailWord_3294845 prefixEnd_3294845 375964259347392586107731 := by
  unfold tailWord_3294845
  simp only [CollatzResearch.WordTrace]
  refine ⟨120172869748346754571101989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80115246498897836380734659 120172869748346754571101989)
  ·
    refine ⟨22532413077815016482081623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120172869748346754571101989 22532413077815016482081623)
    ·
      refine ⟨33798619616722524723122435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22532413077815016482081623 33798619616722524723122435)
      ·
        refine ⟨50697929425083787084683653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33798619616722524723122435 50697929425083787084683653)
        ·
          refine ⟨9505861767203210078378185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50697929425083787084683653 9505861767203210078378185)
          ·
            refine ⟨7129396325402407558783639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9505861767203210078378185 7129396325402407558783639)
            ·
              refine ⟨10694094488103611338175459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129396325402407558783639 10694094488103611338175459)
              ·
                refine ⟨16041141732155417007263189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10694094488103611338175459 16041141732155417007263189)
                ·
                  refine ⟨375964259347392586107731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16041141732155417007263189 375964259347392586107731)
                  ·
                    rfl

theorem cell22_3294845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_3294845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294845 prefixEnd_3294845 := by exact prefixLift 3294845
  have htrace : WordTrace (prefixWord ++ tailWord_3294845) baseStart_3294845 baseEnd_3294845 := by
    simpa [prefixWord, tailWord_3294845, baseEnd_3294845] using wordTrace_append hprefix tailTrace_3294845
  have hstable : (prefixWord ++ tailWord_3294845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294845).length < 2 ^ (prefixWord ++ tailWord_3294845).sum := by decide
  have hdescent : baseEnd_3294845 < baseStart_3294845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294849 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3294849 : Nat := 118140960795 + 3294849 * 2 ^ 59
def prefixEnd_3294849 : Nat := 4983230072969 + 3 ^ 40 * 3294849 * 2
def baseEnd_3294849 : Nat := 1127894147323923081223181

theorem tailTrace_3294849 : CollatzResearch.WordTrace tailWord_3294849 prefixEnd_3294849 1127894147323923081223181 := by
  unfold tailWord_3294849
  simp only [CollatzResearch.WordTrace]
  refine ⟨120173015640332263254247601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80115343760221508836165067 120173015640332263254247601)
  ·
    refine ⟨90129761730249197440685701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120173015640332263254247601 90129761730249197440685701)
    ·
      refine ⟨16899330324421724520128569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90129761730249197440685701 16899330324421724520128569)
      ·
        refine ⟨12674497743316293390096427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16899330324421724520128569 12674497743316293390096427)
        ·
          refine ⟨19011746614974440085144641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12674497743316293390096427 19011746614974440085144641)
          ·
            refine ⟨14258809961230830063858481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19011746614974440085144641 14258809961230830063858481)
            ·
              refine ⟨10694107470923122547893861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14258809961230830063858481 10694107470923122547893861)
              ·
                refine ⟨2005145150798085477730099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10694107470923122547893861 2005145150798085477730099)
                ·
                  refine ⟨3007717726197128216595149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005145150798085477730099 3007717726197128216595149)
                  ·
                    refine ⟨1127894147323923081223181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3007717726197128216595149 1127894147323923081223181)
                    ·
                      rfl

theorem cell22_3294849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3294849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294849 prefixEnd_3294849 := by exact prefixLift 3294849
  have htrace : WordTrace (prefixWord ++ tailWord_3294849) baseStart_3294849 baseEnd_3294849 := by
    simpa [prefixWord, tailWord_3294849, baseEnd_3294849] using wordTrace_append hprefix tailTrace_3294849
  have hstable : (prefixWord ++ tailWord_3294849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294849).length < 2 ^ (prefixWord ++ tailWord_3294849).sum := by decide
  have hdescent : baseEnd_3294849 < baseStart_3294849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294873 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 8]
def baseStart_3294873 : Nat := 118140960795 + 3294873 * 2 ^ 59
def prefixEnd_3294873 : Nat := 4983230072969 + 3 ^ 40 * 3294873 * 2
def baseEnd_3294873 : Nat := 375967454338131672874369

theorem tailTrace_3294873 : CollatzResearch.WordTrace tailWord_3294873 prefixEnd_3294873 375967454338131672874369 := by
  unfold tailWord_3294873
  simp only [CollatzResearch.WordTrace]
  refine ⟨120173890992245315353121273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80115927328163543568747515 120173890992245315353121273)
  ·
    refine ⟨90130418244183986514840955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120173890992245315353121273 90130418244183986514840955)
    ·
      refine ⟨135195627366275979772261433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90130418244183986514840955 135195627366275979772261433)
      ·
        refine ⟨101396720524706984829196075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135195627366275979772261433 101396720524706984829196075)
        ·
          refine ⟨152095080787060477243794113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101396720524706984829196075 152095080787060477243794113)
          ·
            refine ⟨114071310590295357932845585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152095080787060477243794113 114071310590295357932845585)
            ·
              refine ⟨85553482942721518449634189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114071310590295357932845585 85553482942721518449634189)
              ·
                refine ⟨32082556103520569418612821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85553482942721518449634189 32082556103520569418612821)
                ·
                  refine ⟨375967454338131672874369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32082556103520569418612821 375967454338131672874369)
                  ·
                    rfl

theorem cell22_3294873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_3294873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294873 prefixEnd_3294873 := by exact prefixLift 3294873
  have htrace : WordTrace (prefixWord ++ tailWord_3294873) baseStart_3294873 baseEnd_3294873 := by
    simpa [prefixWord, tailWord_3294873, baseEnd_3294873] using wordTrace_append hprefix tailTrace_3294873
  have hstable : (prefixWord ++ tailWord_3294873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294873).length < 2 ^ (prefixWord ++ tailWord_3294873).sum := by decide
  have hdescent : baseEnd_3294873 < baseStart_3294873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294920 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3294920 : Nat := 118140960795 + 3294920 * 2 ^ 59
def prefixEnd_3294920 : Nat := 4983230072969 + 3 ^ 40 * 3294920 * 2
def baseEnd_3294920 : Nat := 1127918452074902562697963

theorem tailTrace_3294920 : CollatzResearch.WordTrace tailWord_3294920 prefixEnd_3294920 1127918452074902562697963 := by
  unfold tailWord_3294920
  simp only [CollatzResearch.WordTrace]
  refine ⟨60087802611537521190041107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80117070148716694920054809 60087802611537521190041107)
  ·
    refine ⟨90131703917306281785061661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60087802611537521190041107 90131703917306281785061661)
    ·
      refine ⟨33799388968989855669398123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90131703917306281785061661 33799388968989855669398123)
      ·
        refine ⟨50699083453484783504097185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33799388968989855669398123 50699083453484783504097185)
        ·
          refine ⟨38024312590113587628072889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50699083453484783504097185 38024312590113587628072889)
          ·
            refine ⟨28518234442585190721054667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38024312590113587628072889 28518234442585190721054667)
            ·
              refine ⟨42777351663877786081582001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28518234442585190721054667 42777351663877786081582001)
              ·
                refine ⟨32083013747908339561186501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42777351663877786081582001 32083013747908339561186501)
                ·
                  refine ⟨6015565077732813667722469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32083013747908339561186501 6015565077732813667722469)
                  ·
                    refine ⟨1127918452074902562697963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015565077732813667722469 1127918452074902562697963)
                    ·
                      rfl

theorem cell22_3294920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3294920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294920 prefixEnd_3294920 := by exact prefixLift 3294920
  have htrace : WordTrace (prefixWord ++ tailWord_3294920) baseStart_3294920 baseEnd_3294920 := by
    simpa [prefixWord, tailWord_3294920, baseEnd_3294920] using wordTrace_append hprefix tailTrace_3294920
  have hstable : (prefixWord ++ tailWord_3294920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294920).length < 2 ^ (prefixWord ++ tailWord_3294920).sum := by decide
  have hdescent : baseEnd_3294920 < baseStart_3294920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3294937 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_3294937 : Nat := 118140960795 + 3294937 * 2 ^ 59
def prefixEnd_3294937 : Nat := 4983230072969 + 3 ^ 40 * 3294937 * 2
def baseEnd_3294937 : Nat := 1127924271522320185022911

theorem tailTrace_3294937 : CollatzResearch.WordTrace tailWord_3294937 prefixEnd_3294937 1127924271522320185022911 := by
  unfold tailWord_3294937
  simp only [CollatzResearch.WordTrace]
  refine ⟨120176225264013454283451065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80117483509342302855634043 120176225264013454283451065)
  ·
    refine ⟨90132168948010090712588299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120176225264013454283451065 90132168948010090712588299)
    ·
      refine ⟨135198253422015136068882449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90132168948010090712588299 135198253422015136068882449)
      ·
        refine ⟨101398690066511352051661837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135198253422015136068882449 101398690066511352051661837)
        ·
          refine ⟨38024508774941757019373189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101398690066511352051661837 38024508774941757019373189)
          ·
            refine ⟨7129595395301579441132473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38024508774941757019373189 7129595395301579441132473)
            ·
              refine ⟨5347196546476184580849355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7129595395301579441132473 5347196546476184580849355)
              ·
                refine ⟨8020794819714276871274033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347196546476184580849355 8020794819714276871274033)
                ·
                  refine ⟨6015596114785707653455525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8020794819714276871274033 6015596114785707653455525)
                  ·
                    refine ⟨1127924271522320185022911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015596114785707653455525 1127924271522320185022911)
                    ·
                      rfl

theorem cell22_3294937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_3294937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3294937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3294937 prefixEnd_3294937 := by exact prefixLift 3294937
  have htrace : WordTrace (prefixWord ++ tailWord_3294937) baseStart_3294937 baseEnd_3294937 := by
    simpa [prefixWord, tailWord_3294937, baseEnd_3294937] using wordTrace_append hprefix tailTrace_3294937
  have hstable : (prefixWord ++ tailWord_3294937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3294937).length < 2 ^ (prefixWord ++ tailWord_3294937).sum := by decide
  have hdescent : baseEnd_3294937 < baseStart_3294937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3294937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295012 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3295012 : Nat := 118140960795 + 3295012 * 2 ^ 59
def prefixEnd_3295012 : Nat := 4983230072969 + 3 ^ 40 * 3295012 * 2
def baseEnd_3295012 : Nat := 1127949945555044989397681

theorem tailTrace_3295012 : CollatzResearch.WordTrace tailWord_3295012 prefixEnd_3295012 1127949945555044989397681 := by
  unfold tailWord_3295012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60089480369370871046215645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80119307159161161394954193 60089480369370871046215645)
  ·
    refine ⟨22533555138514076642330867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60089480369370871046215645 22533555138514076642330867)
    ·
      refine ⟨33800332707771114963496301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22533555138514076642330867 33800332707771114963496301)
      ·
        refine ⟨12675124765414168111311113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33800332707771114963496301 12675124765414168111311113)
        ·
          refine ⟨9506343574060626083483335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12675124765414168111311113 9506343574060626083483335)
          ·
            refine ⟨14259515361090939125225003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506343574060626083483335 14259515361090939125225003)
            ·
              refine ⟨21389273041636408687837505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14259515361090939125225003 21389273041636408687837505)
              ·
                refine ⟨16041954781227306515878129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21389273041636408687837505 16041954781227306515878129)
                ·
                  refine ⟨12031466085920479886908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16041954781227306515878129 12031466085920479886908597)
                  ·
                    refine ⟨1127949945555044989397681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12031466085920479886908597 1127949945555044989397681)
                    ·
                      rfl

theorem cell22_3295012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3295012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295012 prefixEnd_3295012 := by exact prefixLift 3295012
  have htrace : WordTrace (prefixWord ++ tailWord_3295012) baseStart_3295012 baseEnd_3295012 := by
    simpa [prefixWord, tailWord_3295012, baseEnd_3295012] using wordTrace_append hprefix tailTrace_3295012
  have hstable : (prefixWord ++ tailWord_3295012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295012).length < 2 ^ (prefixWord ++ tailWord_3295012).sum := by decide
  have hdescent : baseEnd_3295012 < baseStart_3295012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295072 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_3295072 : Nat := 118140960795 + 3295072 * 2 ^ 59
def prefixEnd_3295072 : Nat := 4983230072969 + 3 ^ 40 * 3295072 * 2
def baseEnd_3295072 : Nat := 1127970484781224832897497

theorem tailTrace_3295072 : CollatzResearch.WordTrace tailWord_3295072 prefixEnd_3295072 1127970484781224832897497 := by
  unfold tailWord_3295072
  simp only [CollatzResearch.WordTrace]
  refine ⟨60090574559262186169807735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80120766079016248226410313 60090574559262186169807735)
  ·
    refine ⟨90135861838893279254711603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60090574559262186169807735 90135861838893279254711603)
    ·
      refine ⟨135203792758339918882067405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90135861838893279254711603 135203792758339918882067405)
      ·
        refine ⟨50701422284377469580775277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135203792758339918882067405 50701422284377469580775277)
        ·
          refine ⟨19013033356641551092790729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50701422284377469580775277 19013033356641551092790729)
          ·
            refine ⟨14259775017481163319593047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19013033356641551092790729 14259775017481163319593047)
            ·
              refine ⟨21389662526221744979389571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14259775017481163319593047 21389662526221744979389571)
              ·
                refine ⟨32084493789332617469084357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21389662526221744979389571 32084493789332617469084357)
                ·
                  refine ⟨6015842585499865775453317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32084493789332617469084357 6015842585499865775453317)
                  ·
                    refine ⟨1127970484781224832897497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6015842585499865775453317 1127970484781224832897497)
                    ·
                      rfl

theorem cell22_3295072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_3295072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295072 prefixEnd_3295072 := by exact prefixLift 3295072
  have htrace : WordTrace (prefixWord ++ tailWord_3295072) baseStart_3295072 baseEnd_3295072 := by
    simpa [prefixWord, tailWord_3295072, baseEnd_3295072] using wordTrace_append hprefix tailTrace_3295072
  have hstable : (prefixWord ++ tailWord_3295072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295072).length < 2 ^ (prefixWord ++ tailWord_3295072).sum := by decide
  have hdescent : baseEnd_3295072 < baseStart_3295072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295076 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_3295076 : Nat := 118140960795 + 3295076 * 2 ^ 59
def prefixEnd_3295076 : Nat := 4983230072969 + 3 ^ 40 * 3295076 * 2
def baseEnd_3295076 : Nat := 375990618020990051932495

theorem tailTrace_3295076 : CollatzResearch.WordTrace tailWord_3295076 prefixEnd_3295076 375990618020990051932495 := by
  unfold tailWord_3295076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60090647505254940511380541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80120863340339920681840721 60090647505254940511380541)
  ·
    refine ⟨22533992814470602691767703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60090647505254940511380541 22533992814470602691767703)
    ·
      refine ⟨33800989221705904037651555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22533992814470602691767703 33800989221705904037651555)
      ·
        refine ⟨50701483832558856056477333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33800989221705904037651555 50701483832558856056477333)
        ·
          refine ⟨2376632054651196377647375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50701483832558856056477333 2376632054651196377647375)
          ·
            refine ⟨3564948081976794566471063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376632054651196377647375 3564948081976794566471063)
            ·
              refine ⟨5347422122965191849706595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564948081976794566471063 5347422122965191849706595)
              ·
                refine ⟨8021133184447787774559893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347422122965191849706595 8021133184447787774559893)
                ·
                  refine ⟨375990618020990051932495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8021133184447787774559893 375990618020990051932495)
                  ·
                    rfl

theorem cell22_3295076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_3295076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295076 prefixEnd_3295076 := by exact prefixLift 3295076
  have htrace : WordTrace (prefixWord ++ tailWord_3295076) baseStart_3295076 baseEnd_3295076 := by
    simpa [prefixWord, tailWord_3295076, baseEnd_3295076] using wordTrace_append hprefix tailTrace_3295076
  have hstable : (prefixWord ++ tailWord_3295076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295076).length < 2 ^ (prefixWord ++ tailWord_3295076).sum := by decide
  have hdescent : baseEnd_3295076 < baseStart_3295076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295179 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 1, 4]
def baseStart_3295179 : Nat := 118140960795 + 3295179 * 2 ^ 59
def prefixEnd_3295179 : Nat := 4983230072969 + 3 ^ 40 * 3295179 * 2
def baseEnd_3295179 : Nat := 1128007113067912220472169

theorem tailTrace_3295179 : CollatzResearch.WordTrace tailWord_3295179 prefixEnd_3295179 1128007113067912220472169 := by
  unfold tailWord_3295179
  simp only [CollatzResearch.WordTrace]
  refine ⟨120185051729136729613760591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80123367819424486409173727 120185051729136729613760591)
  ·
    refine ⟨180277577593705094420640887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120185051729136729613760591 180277577593705094420640887)
    ·
      refine ⟨270416366390557641630961331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180277577593705094420640887 270416366390557641630961331)
      ·
        refine ⟨405624549585836462446441997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270416366390557641630961331 405624549585836462446441997)
        ·
          refine ⟨152109206094688673417415749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405624549585836462446441997 152109206094688673417415749)
          ·
            refine ⟨28520476142754126265765453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152109206094688673417415749 28520476142754126265765453)
            ·
              refine ⟨10695178553532797349662045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28520476142754126265765453 10695178553532797349662045)
              ·
                refine ⟨4010691957574799006123267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10695178553532797349662045 4010691957574799006123267)
                ·
                  refine ⟨6016037936362198509184901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4010691957574799006123267 6016037936362198509184901)
                  ·
                    refine ⟨1128007113067912220472169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6016037936362198509184901 1128007113067912220472169)
                    ·
                      rfl

theorem cell22_3295179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_3295179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295179 prefixEnd_3295179 := by exact prefixLift 3295179
  have htrace : WordTrace (prefixWord ++ tailWord_3295179) baseStart_3295179 baseEnd_3295179 := by
    simpa [prefixWord, tailWord_3295179, baseEnd_3295179] using wordTrace_append hprefix tailTrace_3295179
  have hstable : (prefixWord ++ tailWord_3295179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295179).length < 2 ^ (prefixWord ++ tailWord_3295179).sum := by decide
  have hdescent : baseEnd_3295179 < baseStart_3295179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295239 : List Nat := [1, 1, 4, 3, 1, 4, 8]
def baseStart_3295239 : Nat := 118140960795 + 3295239 * 2 ^ 59
def prefixEnd_3295239 : Nat := 4983230072969 + 3 ^ 40 * 3295239 * 2
def baseEnd_3295239 : Nat := 41778801936818224591555

theorem tailTrace_3295239 : CollatzResearch.WordTrace tailWord_3295239 prefixEnd_3295239 41778801936818224591555 := by
  unfold tailWord_3295239
  simp only [CollatzResearch.WordTrace]
  refine ⟨120187240108919359860944771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80124826739279573240629847 120187240108919359860944771)
  ·
    refine ⟨180280860163379039791417157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120187240108919359860944771 180280860163379039791417157)
    ·
      refine ⟨33802661280633569960890717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180280860163379039791417157 33802661280633569960890717)
      ·
        refine ⟨12675997980237588735334019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33802661280633569960890717 12675997980237588735334019)
        ·
          refine ⟨19013996970356383103001029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12675997980237588735334019 19013996970356383103001029)
          ·
            refine ⟨3565124431941821831812693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19013996970356383103001029 3565124431941821831812693)
            ·
              refine ⟨41778801936818224591555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3565124431941821831812693 41778801936818224591555)
              ·
                rfl

theorem cell22_3295239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 8].length) (baseStart_3295239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295239 prefixEnd_3295239 := by exact prefixLift 3295239
  have htrace : WordTrace (prefixWord ++ tailWord_3295239) baseStart_3295239 baseEnd_3295239 := by
    simpa [prefixWord, tailWord_3295239, baseEnd_3295239] using wordTrace_append hprefix tailTrace_3295239
  have hstable : (prefixWord ++ tailWord_3295239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295239).length < 2 ^ (prefixWord ++ tailWord_3295239).sum := by decide
  have hdescent : baseEnd_3295239 < baseStart_3295239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295260 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3295260 : Nat := 118140960795 + 3295260 * 2 ^ 59
def prefixEnd_3295260 : Nat := 4983230072969 + 3 ^ 40 * 3295260 * 2
def baseEnd_3295260 : Nat := 1128034841023255009196921

theorem tailTrace_3295260 : CollatzResearch.WordTrace tailWord_3295260 prefixEnd_3295260 1128034841023255009196921 := by
  unfold tailWord_3295260
  simp only [CollatzResearch.WordTrace]
  refine ⟨60094003020921640223729617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80125337361228853631639489 60094003020921640223729617)
  ·
    refine ⟨45070502265691230167797213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60094003020921640223729617 45070502265691230167797213)
    ·
      refine ⟨16901438349634211312923955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45070502265691230167797213 16901438349634211312923955)
      ·
        refine ⟨25352157524451316969385933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16901438349634211312923955 25352157524451316969385933)
        ·
          refine ⟨9507059071669243863519725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25352157524451316969385933 9507059071669243863519725)
          ·
            refine ⟨3565147151875966448819897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9507059071669243863519725 3565147151875966448819897)
            ·
              refine ⟨2673860363906974836614923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565147151875966448819897 2673860363906974836614923)
              ·
                refine ⟨4010790545860462254922385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673860363906974836614923 4010790545860462254922385)
                ·
                  refine ⟨3008092909395346691191789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4010790545860462254922385 3008092909395346691191789)
                  ·
                    refine ⟨1128034841023255009196921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008092909395346691191789 1128034841023255009196921)
                    ·
                      rfl

theorem cell22_3295260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3295260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295260 prefixEnd_3295260 := by exact prefixLift 3295260
  have htrace : WordTrace (prefixWord ++ tailWord_3295260) baseStart_3295260 baseEnd_3295260 := by
    simpa [prefixWord, tailWord_3295260, baseEnd_3295260] using wordTrace_append hprefix tailTrace_3295260
  have hstable : (prefixWord ++ tailWord_3295260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295260).length < 2 ^ (prefixWord ++ tailWord_3295260).sum := by decide
  have hdescent : baseEnd_3295260 < baseStart_3295260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295391 : List Nat := [1, 1, 2, 6, 1, 2, 1, 8]
def baseStart_3295391 : Nat := 118140960795 + 3295391 * 2 ^ 59
def prefixEnd_3295391 : Nat := 4983230072969 + 3 ^ 40 * 3295391 * 2
def baseEnd_3295391 : Nat := 125342187222268259352391

theorem tailTrace_3295391 : CollatzResearch.WordTrace tailWord_3295391 prefixEnd_3295391 125342187222268259352391 := by
  unfold tailWord_3295391
  simp only [CollatzResearch.WordTrace]
  refine ⟨120192784004368689820478027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80128522669579126546985351 120192784004368689820478027)
  ·
    refine ⟨180289176006553034730717041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120192784004368689820478027 180289176006553034730717041)
    ·
      refine ⟨135216882004914776048037781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180289176006553034730717041 135216882004914776048037781)
      ·
        refine ⟨6338291343980380127251771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135216882004914776048037781 6338291343980380127251771)
        ·
          refine ⟨9507437015970570190877657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6338291343980380127251771 9507437015970570190877657)
          ·
            refine ⟨7130577761977927643158243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9507437015970570190877657 7130577761977927643158243)
            ·
              refine ⟨10695866642966891464737365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130577761977927643158243 10695866642966891464737365)
              ·
                refine ⟨125342187222268259352391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10695866642966891464737365 125342187222268259352391)
                ·
                  rfl

theorem cell22_3295391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 8].length) (baseStart_3295391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295391 prefixEnd_3295391 := by exact prefixLift 3295391
  have htrace : WordTrace (prefixWord ++ tailWord_3295391) baseStart_3295391 baseEnd_3295391 := by
    simpa [prefixWord, tailWord_3295391, baseEnd_3295391] using wordTrace_append hprefix tailTrace_3295391
  have hstable : (prefixWord ++ tailWord_3295391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295391).length < 2 ^ (prefixWord ++ tailWord_3295391).sum := by decide
  have hdescent : baseEnd_3295391 < baseStart_3295391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295419 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 7]
def baseStart_3295419 : Nat := 118140960795 + 3295419 * 2 ^ 59
def prefixEnd_3295419 : Nat := 4983230072969 + 3 ^ 40 * 3295419 * 2
def baseEnd_3295419 : Nat := 376029756657543864823811

theorem tailTrace_3295419 : CollatzResearch.WordTrace tailWord_3295419 prefixEnd_3295419 376029756657543864823811 := by
  unfold tailWord_3295419
  simp only [CollatzResearch.WordTrace]
  refine ⟨120193805248267250602497311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80129203498844833734998207 120193805248267250602497311)
  ·
    refine ⟨180290707872400875903745967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120193805248267250602497311 180290707872400875903745967)
    ·
      refine ⟨270436061808601313855618951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180290707872400875903745967 270436061808601313855618951)
      ·
        refine ⟨405654092712901970783428427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270436061808601313855618951 405654092712901970783428427)
        ·
          refine ⟨608481139069352956175142641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405654092712901970783428427 608481139069352956175142641)
          ·
            refine ⟨456360854302014717131356981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608481139069352956175142641 456360854302014717131356981)
            ·
              refine ⟨42783830090813879731064717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456360854302014717131356981 42783830090813879731064717)
              ·
                refine ⟨16043936284055204899149269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42783830090813879731064717 16043936284055204899149269)
                ·
                  refine ⟨376029756657543864823811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16043936284055204899149269 376029756657543864823811)
                  ·
                    rfl

theorem cell22_3295419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_3295419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295419 prefixEnd_3295419 := by exact prefixLift 3295419
  have htrace : WordTrace (prefixWord ++ tailWord_3295419) baseStart_3295419 baseEnd_3295419 := by
    simpa [prefixWord, tailWord_3295419, baseEnd_3295419] using wordTrace_append hprefix tailTrace_3295419
  have hstable : (prefixWord ++ tailWord_3295419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295419).length < 2 ^ (prefixWord ++ tailWord_3295419).sum := by decide
  have hdescent : baseEnd_3295419 < baseStart_3295419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295474 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3295474 : Nat := 118140960795 + 3295474 * 2 ^ 59
def prefixEnd_3295474 : Nat := 4983230072969 + 3 ^ 40 * 3295474 * 2
def baseEnd_3295474 : Nat := 1128108097596629784346265

theorem tailTrace_3295474 : CollatzResearch.WordTrace tailWord_3295474 prefixEnd_3295474 1128108097596629784346265 := by
  unfold tailWord_3295474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30048952815766998748937369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80130540842045329997166317 30048952815766998748937369)
  ·
    refine ⟨22536714611825249061703027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30048952815766998748937369 22536714611825249061703027)
    ·
      refine ⟨33805071917737873592554541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22536714611825249061703027 33805071917737873592554541)
      ·
        refine ⟨12676901969151702597207953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33805071917737873592554541 12676901969151702597207953)
        ·
          refine ⟨9507676476863776947905965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12676901969151702597207953 9507676476863776947905965)
          ·
            refine ⟨3565378678823916355464737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9507676476863776947905965 3565378678823916355464737)
            ·
              refine ⟨2674034009117937266598553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565378678823916355464737 2674034009117937266598553)
              ·
                refine ⟨2005525506838452949948915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674034009117937266598553 2005525506838452949948915)
                ·
                  refine ⟨3008288260257679424923373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005525506838452949948915 3008288260257679424923373)
                  ·
                    refine ⟨1128108097596629784346265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008288260257679424923373 1128108097596629784346265)
                    ·
                      rfl

theorem cell22_3295474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3295474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295474 prefixEnd_3295474 := by exact prefixLift 3295474
  have htrace : WordTrace (prefixWord ++ tailWord_3295474) baseStart_3295474 baseEnd_3295474 := by
    simpa [prefixWord, tailWord_3295474, baseEnd_3295474] using wordTrace_append hprefix tailTrace_3295474
  have hstable : (prefixWord ++ tailWord_3295474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295474).length < 2 ^ (prefixWord ++ tailWord_3295474).sum := by decide
  have hdescent : baseEnd_3295474 < baseStart_3295474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295588 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3295588 : Nat := 118140960795 + 3295588 * 2 ^ 59
def prefixEnd_3295588 : Nat := 4983230072969 + 3 ^ 40 * 3295588 * 2
def baseEnd_3295588 : Nat := 376049040708790495665305

theorem tailTrace_3295588 : CollatzResearch.WordTrace tailWord_3295588 prefixEnd_3295588 376049040708790495665305 := by
  unfold tailWord_3295588
  simp only [CollatzResearch.WordTrace]
  refine ⟨60099984592327496232699709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80133312789769994976932945 60099984592327496232699709)
  ·
    refine ⟨22537494222122811087262391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60099984592327496232699709 22537494222122811087262391)
    ·
      refine ⟨33806241333184216630893587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22537494222122811087262391 33806241333184216630893587)
      ·
        refine ⟨50709361999776324946340381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33806241333184216630893587 50709361999776324946340381)
        ·
          refine ⟨19016010749916121854877643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50709361999776324946340381 19016010749916121854877643)
          ·
            refine ⟨28524016124874182782316465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19016010749916121854877643 28524016124874182782316465)
            ·
              refine ⟨21393012093655637086737349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28524016124874182782316465 21393012093655637086737349)
              ·
                refine ⟨4011189767560431953763253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21393012093655637086737349 4011189767560431953763253)
                ·
                  refine ⟨376049040708790495665305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011189767560431953763253 376049040708790495665305)
                  ·
                    rfl

theorem cell22_3295588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3295588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295588 prefixEnd_3295588 := by exact prefixLift 3295588
  have htrace : WordTrace (prefixWord ++ tailWord_3295588) baseStart_3295588 baseEnd_3295588 := by
    simpa [prefixWord, tailWord_3295588, baseEnd_3295588] using wordTrace_append hprefix tailTrace_3295588
  have hstable : (prefixWord ++ tailWord_3295588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295588).length < 2 ^ (prefixWord ++ tailWord_3295588).sum := by decide
  have hdescent : baseEnd_3295588 < baseStart_3295588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295592 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3295592 : Nat := 118140960795 + 3295592 * 2 ^ 59
def prefixEnd_3295592 : Nat := 4983230072969 + 3 ^ 40 * 3295592 * 2
def baseEnd_3295592 : Nat := 1128148491408116809895903

theorem tailTrace_3295592 : CollatzResearch.WordTrace tailWord_3295592 prefixEnd_3295592 1128148491408116809895903 := by
  unfold tailWord_3295592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60100057538320250574272515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80133410051093667432363353 60100057538320250574272515)
  ·
    refine ⟨90150086307480375861408773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60100057538320250574272515 90150086307480375861408773)
    ·
      refine ⟨16903141182652570474014145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90150086307480375861408773 16903141182652570474014145)
      ·
        refine ⟨12677355886989427855510609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16903141182652570474014145 12677355886989427855510609)
        ·
          refine ⟨9508016915242070891632957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12677355886989427855510609 9508016915242070891632957)
          ·
            refine ⟨3565506343215776584362359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9508016915242070891632957 3565506343215776584362359)
            ·
              refine ⟨5348259514823664876543539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565506343215776584362359 5348259514823664876543539)
              ·
                refine ⟨8022389272235497314815309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348259514823664876543539 8022389272235497314815309)
                ·
                  refine ⟨3008395977088311493055741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8022389272235497314815309 3008395977088311493055741)
                  ·
                    refine ⟨1128148491408116809895903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008395977088311493055741 1128148491408116809895903)
                    ·
                      rfl

theorem cell22_3295592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3295592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295592 prefixEnd_3295592 := by exact prefixLift 3295592
  have htrace : WordTrace (prefixWord ++ tailWord_3295592) baseStart_3295592 baseEnd_3295592 := by
    simpa [prefixWord, tailWord_3295592, baseEnd_3295592] using wordTrace_append hprefix tailTrace_3295592
  have hstable : (prefixWord ++ tailWord_3295592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295592).length < 2 ^ (prefixWord ++ tailWord_3295592).sum := by decide
  have hdescent : baseEnd_3295592 < baseStart_3295592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295601 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3295601 : Nat := 118140960795 + 3295601 * 2 ^ 59
def prefixEnd_3295601 : Nat := 4983230072969 + 3 ^ 40 * 3295601 * 2
def baseEnd_3295601 : Nat := 1128151572292043786420875

theorem tailTrace_3295601 : CollatzResearch.WordTrace tailWord_3295601 prefixEnd_3295601 1128151572292043786420875 := by
  unfold tailWord_3295601
  simp only [CollatzResearch.WordTrace]
  refine ⟨120200443333607895685622657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80133628889071930457081771 120200443333607895685622657)
  ·
    refine ⟨90150332500205921764216993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120200443333607895685622657 90150332500205921764216993)
    ·
      refine ⟨67612749375154441323162745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90150332500205921764216993 67612749375154441323162745)
      ·
        refine ⟨50709562031365830992372059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67612749375154441323162745 50709562031365830992372059)
        ·
          refine ⟨76064343047048746488558089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50709562031365830992372059 76064343047048746488558089)
          ·
            refine ⟨57048257285286559866418567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76064343047048746488558089 57048257285286559866418567)
            ·
              refine ⟨85572385927929839799627851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57048257285286559866418567 85572385927929839799627851)
              ·
                refine ⟨128358578891894759699441777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85572385927929839799627851 128358578891894759699441777)
                ·
                  refine ⟨96268934168921069774581333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128358578891894759699441777 96268934168921069774581333)
                  ·
                    refine ⟨1128151572292043786420875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96268934168921069774581333 1128151572292043786420875)
                    ·
                      rfl

theorem cell22_3295601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3295601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295601 prefixEnd_3295601 := by exact prefixLift 3295601
  have htrace : WordTrace (prefixWord ++ tailWord_3295601) baseStart_3295601 baseEnd_3295601 := by
    simpa [prefixWord, tailWord_3295601, baseEnd_3295601] using wordTrace_append hprefix tailTrace_3295601
  have hstable : (prefixWord ++ tailWord_3295601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295601).length < 2 ^ (prefixWord ++ tailWord_3295601).sum := by decide
  have hdescent : baseEnd_3295601 < baseStart_3295601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295605 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 5]
def baseStart_3295605 : Nat := 118140960795 + 3295605 * 2 ^ 59
def prefixEnd_3295605 : Nat := 4983230072969 + 3 ^ 40 * 3295605 * 2
def baseEnd_3295605 : Nat := 376050980524596369773621

theorem tailTrace_3295605 : CollatzResearch.WordTrace tailWord_3295605 prefixEnd_3295605 376050980524596369773621 := by
  unfold tailWord_3295605
  simp only [CollatzResearch.WordTrace]
  refine ⟨120200589225593404368768269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80133726150395602912512179 120200589225593404368768269)
  ·
    refine ⟨45075220959597526638288101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120200589225593404368768269 45075220959597526638288101)
    ·
      refine ⟨8451603929924536244679019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45075220959597526638288101 8451603929924536244679019)
      ·
        refine ⟨12677405894886804367018529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8451603929924536244679019 12677405894886804367018529)
        ·
          refine ⟨9508054421165103275263897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12677405894886804367018529 9508054421165103275263897)
          ·
            refine ⟨7131040815873827456447923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508054421165103275263897 7131040815873827456447923)
            ·
              refine ⟨10696561223810741184671885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7131040815873827456447923 10696561223810741184671885)
              ·
                refine ⟨4011210458929027944251957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10696561223810741184671885 4011210458929027944251957)
                ·
                  refine ⟨376050980524596369773621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011210458929027944251957 376050980524596369773621)
                  ·
                    rfl

theorem cell22_3295605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_3295605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295605 prefixEnd_3295605 := by exact prefixLift 3295605
  have htrace : WordTrace (prefixWord ++ tailWord_3295605) baseStart_3295605 baseEnd_3295605 := by
    simpa [prefixWord, tailWord_3295605, baseEnd_3295605] using wordTrace_append hprefix tailTrace_3295605
  have hstable : (prefixWord ++ tailWord_3295605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295605).length < 2 ^ (prefixWord ++ tailWord_3295605).sum := by decide
  have hdescent : baseEnd_3295605 < baseStart_3295605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295665 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_3295665 : Nat := 118140960795 + 3295665 * 2 ^ 59
def prefixEnd_3295665 : Nat := 4983230072969 + 3 ^ 40 * 3295665 * 2
def baseEnd_3295665 : Nat := 1128173480799968952820679

theorem tailTrace_3295665 : CollatzResearch.WordTrace tailWord_3295665 prefixEnd_3295665 1128173480799968952820679 := by
  unfold tailWord_3295665
  simp only [CollatzResearch.WordTrace]
  refine ⟨120202777605376034615952449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80135185070250689743968299 120202777605376034615952449)
  ·
    refine ⟨90152083204032025961964337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120202777605376034615952449 90152083204032025961964337)
    ·
      refine ⟨67614062403024019471473253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90152083204032025961964337 67614062403024019471473253)
      ·
        refine ⟨12677636700567003650901235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67614062403024019471473253 12677636700567003650901235)
        ·
          refine ⟨19016455050850505476351853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12677636700567003650901235 19016455050850505476351853)
          ·
            refine ⟨7131170644068939553631945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19016455050850505476351853 7131170644068939553631945)
            ·
              refine ⟨5348377983051704665223959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131170644068939553631945 5348377983051704665223959)
              ·
                refine ⟨8022566974577556997835939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348377983051704665223959 8022566974577556997835939)
                ·
                  refine ⟨12033850461866335496753909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022566974577556997835939 12033850461866335496753909)
                  ·
                    refine ⟨1128173480799968952820679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12033850461866335496753909 1128173480799968952820679)
                    ·
                      rfl

theorem cell22_3295665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_3295665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295665 prefixEnd_3295665 := by exact prefixLift 3295665
  have htrace : WordTrace (prefixWord ++ tailWord_3295665) baseStart_3295665 baseEnd_3295665 := by
    simpa [prefixWord, tailWord_3295665, baseEnd_3295665] using wordTrace_append hprefix tailTrace_3295665
  have hstable : (prefixWord ++ tailWord_3295665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295665).length < 2 ^ (prefixWord ++ tailWord_3295665).sum := by decide
  have hdescent : baseEnd_3295665 < baseStart_3295665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295678 : List Nat := [4, 2, 1, 1, 1, 1, 2, 10]
def baseStart_3295678 : Nat := 118140960795 + 3295678 * 2 ^ 59
def prefixEnd_3295678 : Nat := 4983230072969 + 3 ^ 40 * 3295678 * 2
def baseEnd_3295678 : Nat := 125353103440626805805071

theorem tailTrace_3295678 : CollatzResearch.WordTrace tailWord_3295678 prefixEnd_3295678 125353103440626805805071 := by
  unfold tailWord_3295678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025406469291117229521961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80135501169552625224117125 15025406469291117229521961)
  ·
    refine ⟨11269054851968337922141471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15025406469291117229521961 11269054851968337922141471)
    ·
      refine ⟨16903582277952506883212207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269054851968337922141471 16903582277952506883212207)
      ·
        refine ⟨25355373416928760324818311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16903582277952506883212207 25355373416928760324818311)
        ·
          refine ⟨38033060125393140487227467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25355373416928760324818311 38033060125393140487227467)
          ·
            refine ⟨57049590188089710730841201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38033060125393140487227467 57049590188089710730841201)
            ·
              refine ⟨42787192641067283048130901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57049590188089710730841201 42787192641067283048130901)
              ·
                refine ⟨125353103440626805805071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42787192641067283048130901 125353103440626805805071)
                ·
                  rfl

theorem cell22_3295678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_3295678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295678 prefixEnd_3295678 := by exact prefixLift 3295678
  have htrace : WordTrace (prefixWord ++ tailWord_3295678) baseStart_3295678 baseEnd_3295678 := by
    simpa [prefixWord, tailWord_3295678, baseEnd_3295678] using wordTrace_append hprefix tailTrace_3295678
  have hstable : (prefixWord ++ tailWord_3295678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295678).length < 2 ^ (prefixWord ++ tailWord_3295678).sum := by decide
  have hdescent : baseEnd_3295678 < baseStart_3295678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295684 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3295684 : Nat := 118140960795 + 3295684 * 2 ^ 59
def prefixEnd_3295684 : Nat := 4983230072969 + 3 ^ 40 * 3295684 * 2
def baseEnd_3295684 : Nat := 376059994962753078865207

theorem tailTrace_3295684 : CollatzResearch.WordTrace tailWord_3295684 prefixEnd_3295684 376059994962753078865207 := by
  unfold tailWord_3295684
  simp only [CollatzResearch.WordTrace]
  refine ⟨60101735296153600430447053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80135647061538133907262737 60101735296153600430447053)
  ·
    refine ⟨22538150736057600161417645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60101735296153600430447053 22538150736057600161417645)
    ·
      refine ⟨8451806526021600060531617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22538150736057600161417645 8451806526021600060531617)
      ·
        refine ⟨6338854894516200045398713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8451806526021600060531617 6338854894516200045398713)
        ·
          refine ⟨4754141170887150034049035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6338854894516200045398713 4754141170887150034049035)
          ·
            refine ⟨7131211756330725051073553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754141170887150034049035 7131211756330725051073553)
            ·
              refine ⟨5348408817248043788305165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131211756330725051073553 5348408817248043788305165)
              ·
                refine ⟨2005653306468016420614437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5348408817248043788305165 2005653306468016420614437)
                ·
                  refine ⟨376059994962753078865207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005653306468016420614437 376059994962753078865207)
                  ·
                    rfl

theorem cell22_3295684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3295684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295684 prefixEnd_3295684 := by exact prefixLift 3295684
  have htrace : WordTrace (prefixWord ++ tailWord_3295684) baseStart_3295684 baseEnd_3295684 := by
    simpa [prefixWord, tailWord_3295684, baseEnd_3295684] using wordTrace_append hprefix tailTrace_3295684
  have hstable : (prefixWord ++ tailWord_3295684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295684).length < 2 ^ (prefixWord ++ tailWord_3295684).sum := by decide
  have hdescent : baseEnd_3295684 < baseStart_3295684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295738 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_3295738 : Nat := 118140960795 + 3295738 * 2 ^ 59
def prefixEnd_3295738 : Nat := 4983230072969 + 3 ^ 40 * 3295738 * 2
def baseEnd_3295738 : Nat := 1128198470191821095745455

theorem tailTrace_3295738 : CollatzResearch.WordTrace tailWord_3295738 prefixEnd_3295738 1128198470191821095745455 := by
  unfold tailWord_3295738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051360033527892020839967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80136960089407712055573245 30051360033527892020839967)
  ·
    refine ⟨45077040050291838031259951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30051360033527892020839967 45077040050291838031259951)
    ·
      refine ⟨67615560075437757046889927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45077040050291838031259951 67615560075437757046889927)
      ·
        refine ⟨101423340113156635570334891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67615560075437757046889927 101423340113156635570334891)
        ·
          refine ⟨152135010169734953355502337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101423340113156635570334891 152135010169734953355502337)
          ·
            refine ⟨114101257627301215016626753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152135010169734953355502337 114101257627301215016626753)
            ·
              refine ⟨85575943220475911262470065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114101257627301215016626753 85575943220475911262470065)
              ·
                refine ⟨64181957415356933446852549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85575943220475911262470065 64181957415356933446852549)
                ·
                  refine ⟨12034117015379425021284853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64181957415356933446852549 12034117015379425021284853)
                  ·
                    refine ⟨1128198470191821095745455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12034117015379425021284853 1128198470191821095745455)
                    ·
                      rfl

theorem cell22_3295738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_3295738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295738 prefixEnd_3295738 := by exact prefixLift 3295738
  have htrace : WordTrace (prefixWord ++ tailWord_3295738) baseStart_3295738 baseEnd_3295738 := by
    simpa [prefixWord, tailWord_3295738, baseEnd_3295738] using wordTrace_append hprefix tailTrace_3295738
  have hstable : (prefixWord ++ tailWord_3295738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295738).length < 2 ^ (prefixWord ++ tailWord_3295738).sum := by decide
  have hdescent : baseEnd_3295738 < baseStart_3295738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295800 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3295800 : Nat := 118140960795 + 3295800 * 2 ^ 59
def prefixEnd_3295800 : Nat := 4983230072969 + 3 ^ 40 * 3295800 * 2
def baseEnd_3295800 : Nat := 1128219694058873600695265

theorem tailTrace_3295800 : CollatzResearch.WordTrace tailWord_3295800 prefixEnd_3295800 1128219694058873600695265 := by
  unfold tailWord_3295800
  simp only [CollatzResearch.WordTrace]
  refine ⟨60103850729943476336058427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80138467639924635114744569 60103850729943476336058427)
  ·
    refine ⟨90155776094915214504087641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60103850729943476336058427 90155776094915214504087641)
    ·
      refine ⟨67616832071186410878065731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90155776094915214504087641 67616832071186410878065731)
      ·
        refine ⟨101425248106779616317098597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67616832071186410878065731 101425248106779616317098597)
        ·
          refine ⟨19017234020021178059455987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101425248106779616317098597 19017234020021178059455987)
          ·
            refine ⟨28525851030031767089183981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19017234020021178059455987 28525851030031767089183981)
            ·
              refine ⟨10697194136261912658443993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28525851030031767089183981 10697194136261912658443993)
              ·
                refine ⟨8022895602196434493832995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10697194136261912658443993 8022895602196434493832995)
                ·
                  refine ⟨12034343403294651740749493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022895602196434493832995 12034343403294651740749493)
                  ·
                    refine ⟨1128219694058873600695265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12034343403294651740749493 1128219694058873600695265)
                    ·
                      rfl

theorem cell22_3295800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3295800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295800 prefixEnd_3295800 := by exact prefixLift 3295800
  have htrace : WordTrace (prefixWord ++ tailWord_3295800) baseStart_3295800 baseEnd_3295800 := by
    simpa [prefixWord, tailWord_3295800, baseEnd_3295800] using wordTrace_append hprefix tailTrace_3295800
  have hstable : (prefixWord ++ tailWord_3295800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295800).length < 2 ^ (prefixWord ++ tailWord_3295800).sum := by decide
  have hdescent : baseEnd_3295800 < baseStart_3295800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295804 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3295804 : Nat := 118140960795 + 3295804 * 2 ^ 59
def prefixEnd_3295804 : Nat := 4983230072969 + 3 ^ 40 * 3295804 * 2
def baseEnd_3295804 : Nat := 1128221063340618923595253

theorem tailTrace_3295804 : CollatzResearch.WordTrace tailWord_3295804 prefixEnd_3295804 1128221063340618923595253 := by
  unfold tailWord_3295804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60103923675936230677631233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80138564901248307570174977 60103923675936230677631233)
  ·
    refine ⟨45077942756952173008223425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60103923675936230677631233 45077942756952173008223425)
    ·
      refine ⟨33808457067714129756167569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45077942756952173008223425 33808457067714129756167569)
      ·
        refine ⟨25356342800785597317125677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33808457067714129756167569 25356342800785597317125677)
        ·
          refine ⟨9508628550294598993922129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25356342800785597317125677 9508628550294598993922129)
          ·
            refine ⟨7131471412720949245441597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9508628550294598993922129 7131471412720949245441597)
            ·
              refine ⟨2674301779770355967040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7131471412720949245441597 2674301779770355967040599)
              ·
                refine ⟨4011452669655533950560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674301779770355967040599 4011452669655533950560899)
                ·
                  refine ⟨6017179004483300925841349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011452669655533950560899 6017179004483300925841349)
                  ·
                    refine ⟨1128221063340618923595253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017179004483300925841349 1128221063340618923595253)
                    ·
                      rfl

theorem cell22_3295804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3295804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295804 prefixEnd_3295804 := by exact prefixLift 3295804
  have htrace : WordTrace (prefixWord ++ tailWord_3295804) baseStart_3295804 baseEnd_3295804 := by
    simpa [prefixWord, tailWord_3295804, baseEnd_3295804] using wordTrace_append hprefix tailTrace_3295804
  have hstable : (prefixWord ++ tailWord_3295804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295804).length < 2 ^ (prefixWord ++ tailWord_3295804).sum := by decide
  have hdescent : baseEnd_3295804 < baseStart_3295804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295812 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3295812 : Nat := 118140960795 + 3295812 * 2 ^ 59
def prefixEnd_3295812 : Nat := 4983230072969 + 3 ^ 40 * 3295812 * 2
def baseEnd_3295812 : Nat := 1128223801904109569395229

theorem tailTrace_3295812 : CollatzResearch.WordTrace tailWord_3295812 prefixEnd_3295812 1128223801904109569395229 := by
  unfold tailWord_3295812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60104069567921739360776845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80138759423895652481035793 60104069567921739360776845)
  ·
    refine ⟨22539026087970652260291317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60104069567921739360776845 22539026087970652260291317)
    ·
      refine ⟨2113033695747248649402311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22539026087970652260291317 2113033695747248649402311)
      ·
        refine ⟨3169550543620872974103467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113033695747248649402311 3169550543620872974103467)
        ·
          refine ⟨4754325815431309461155201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169550543620872974103467 4754325815431309461155201)
          ·
            refine ⟨3565744361573482095866401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754325815431309461155201 3565744361573482095866401)
            ·
              refine ⟨2674308271180111571899801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565744361573482095866401 2674308271180111571899801)
              ·
                refine ⟨2005731203385083678924851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674308271180111571899801 2005731203385083678924851)
                ·
                  refine ⟨3008596805077625518387277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005731203385083678924851 3008596805077625518387277)
                  ·
                    refine ⟨1128223801904109569395229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008596805077625518387277 1128223801904109569395229)
                    ·
                      rfl

theorem cell22_3295812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3295812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295812 prefixEnd_3295812 := by exact prefixLift 3295812
  have htrace : WordTrace (prefixWord ++ tailWord_3295812) baseStart_3295812 baseEnd_3295812 := by
    simpa [prefixWord, tailWord_3295812, baseEnd_3295812] using wordTrace_append hprefix tailTrace_3295812
  have hstable : (prefixWord ++ tailWord_3295812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295812).length < 2 ^ (prefixWord ++ tailWord_3295812).sum := by decide
  have hdescent : baseEnd_3295812 < baseStart_3295812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295813 : List Nat := [1, 3, 1, 1, 1, 15]
def baseStart_3295813 : Nat := 118140960795 + 3295813 * 2 ^ 59
def prefixEnd_3295813 : Nat := 4983230072969 + 3 ^ 40 * 3295813 * 2
def baseEnd_3295813 : Nat := 13928693138574640742225

theorem tailTrace_3295813 : CollatzResearch.WordTrace tailWord_3295813 prefixEnd_3295813 13928693138574640742225 := by
  unfold tailWord_3295813
  simp only [CollatzResearch.WordTrace]
  refine ⟨120208175608839855892340093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80138783739226570594893395 120208175608839855892340093)
  ·
    refine ⟨45078065853314945959627535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120208175608839855892340093 45078065853314945959627535)
    ·
      refine ⟨67617098779972418939441303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45078065853314945959627535 67617098779972418939441303)
      ·
        refine ⟨101425648169958628409161955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67617098779972418939441303 101425648169958628409161955)
        ·
          refine ⟨152138472254937942613742933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101425648169958628409161955 152138472254937942613742933)
          ·
            refine ⟨13928693138574640742225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 152138472254937942613742933 13928693138574640742225)
            ·
              rfl

theorem cell22_3295813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 15].length) (baseStart_3295813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295813 prefixEnd_3295813 := by exact prefixLift 3295813
  have htrace : WordTrace (prefixWord ++ tailWord_3295813) baseStart_3295813 baseEnd_3295813 := by
    simpa [prefixWord, tailWord_3295813, baseEnd_3295813] using wordTrace_append hprefix tailTrace_3295813
  have hstable : (prefixWord ++ tailWord_3295813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295813).length < 2 ^ (prefixWord ++ tailWord_3295813).sum := by decide
  have hdescent : baseEnd_3295813 < baseStart_3295813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295879 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3295879 : Nat := 118140960795 + 3295879 * 2 ^ 59
def prefixEnd_3295879 : Nat := 4983230072969 + 3 ^ 40 * 3295879 * 2
def baseEnd_3295879 : Nat := 1128246737373343727970023

theorem tailTrace_3295879 : CollatzResearch.WordTrace tailWord_3295879 prefixEnd_3295879 1128246737373343727970023 := by
  unfold tailWord_3295879
  simp only [CollatzResearch.WordTrace]
  refine ⟨120210582826600749164242691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80140388551067166109495127 120210582826600749164242691)
  ·
    refine ⟨180315874239901123746364037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120210582826600749164242691 180315874239901123746364037)
    ·
      refine ⟨33809226419981460702443257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180315874239901123746364037 33809226419981460702443257)
      ·
        refine ⟨25356919814986095526832443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33809226419981460702443257 25356919814986095526832443)
        ·
          refine ⟨38035379722479143290248665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25356919814986095526832443 38035379722479143290248665)
          ·
            refine ⟨28526534791859357467686499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38035379722479143290248665 28526534791859357467686499)
            ·
              refine ⟨42789802187789036201529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28526534791859357467686499 42789802187789036201529749)
              ·
                refine ⟨2005771977552611071946707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42789802187789036201529749 2005771977552611071946707)
                ·
                  refine ⟨3008657966328916607920061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005771977552611071946707 3008657966328916607920061)
                  ·
                    refine ⟨1128246737373343727970023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008657966328916607920061 1128246737373343727970023)
                    ·
                      rfl

theorem cell22_3295879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3295879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295879 prefixEnd_3295879 := by exact prefixLift 3295879
  have htrace : WordTrace (prefixWord ++ tailWord_3295879) baseStart_3295879 baseEnd_3295879 := by
    simpa [prefixWord, tailWord_3295879, baseEnd_3295879] using wordTrace_append hprefix tailTrace_3295879
  have hstable : (prefixWord ++ tailWord_3295879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295879).length < 2 ^ (prefixWord ++ tailWord_3295879).sum := by decide
  have hdescent : baseEnd_3295879 < baseStart_3295879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295967 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_3295967 : Nat := 118140960795 + 3295967 * 2 ^ 59
def prefixEnd_3295967 : Nat := 4983230072969 + 3 ^ 40 * 3295967 * 2
def baseEnd_3295967 : Nat := 1128276861571740831769753

theorem tailTrace_3295967 : CollatzResearch.WordTrace tailWord_3295967 prefixEnd_3295967 1128276861571740831769753 := by
  unfold tailWord_3295967
  simp only [CollatzResearch.WordTrace]
  refine ⟨120213792450281940193446155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80142528300187960128964103 120213792450281940193446155)
  ·
    refine ⟨180320688675422910290169233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120213792450281940193446155 180320688675422910290169233)
    ·
      refine ⟨135240516506567182717626925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180320688675422910290169233 135240516506567182717626925)
      ·
        refine ⟨50715193689962693519110097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135240516506567182717626925 50715193689962693519110097)
        ·
          refine ⟨38036395267472020139332573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50715193689962693519110097 38036395267472020139332573)
          ·
            refine ⟨14263648225302007552249715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38036395267472020139332573 14263648225302007552249715)
            ·
              refine ⟨21395472337953011328374573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14263648225302007552249715 21395472337953011328374573)
              ·
                refine ⟨8023302126732379248140465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21395472337953011328374573 8023302126732379248140465)
                ·
                  refine ⟨6017476595049284436105349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8023302126732379248140465 6017476595049284436105349)
                  ·
                    refine ⟨1128276861571740831769753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017476595049284436105349 1128276861571740831769753)
                    ·
                      rfl

theorem cell22_3295967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_3295967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295967 prefixEnd_3295967 := by exact prefixLift 3295967
  have htrace : WordTrace (prefixWord ++ tailWord_3295967) baseStart_3295967 baseEnd_3295967 := by
    simpa [prefixWord, tailWord_3295967, baseEnd_3295967] using wordTrace_append hprefix tailTrace_3295967
  have hstable : (prefixWord ++ tailWord_3295967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295967).length < 2 ^ (prefixWord ++ tailWord_3295967).sum := by decide
  have hdescent : baseEnd_3295967 < baseStart_3295967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3295986 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_3295986 : Nat := 118140960795 + 3295986 * 2 ^ 59
def prefixEnd_3295986 : Nat := 4983230072969 + 3 ^ 40 * 3295986 * 2
def baseEnd_3295986 : Nat := 1128283365660031115544695

theorem tailTrace_3295986 : CollatzResearch.WordTrace tailWord_3295986 prefixEnd_3295986 1128283365660031115544695 := by
  unfold tailWord_3295986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30053621359303276609596953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80142990291475404292258541 30053621359303276609596953)
  ·
    refine ⟨22540216019477457457197715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30053621359303276609596953 22540216019477457457197715)
    ·
      refine ⟨33810324029216186185796573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22540216019477457457197715 33810324029216186185796573)
      ·
        refine ⟨12678871510956069819673715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33810324029216186185796573 12678871510956069819673715)
        ·
          refine ⟨19018307266434104729510573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12678871510956069819673715 19018307266434104729510573)
          ·
            refine ⟨7131865224912789273566465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19018307266434104729510573 7131865224912789273566465)
            ·
              refine ⟨5348898918684591955174849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131865224912789273566465 5348898918684591955174849)
              ·
                refine ⟨4011674189013443966381137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5348898918684591955174849 4011674189013443966381137)
                ·
                  refine ⟨3008755641760082974785853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011674189013443966381137 3008755641760082974785853)
                  ·
                    refine ⟨1128283365660031115544695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008755641760082974785853 1128283365660031115544695)
                    ·
                      rfl

theorem cell22_3295986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_3295986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3295986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3295986 prefixEnd_3295986 := by exact prefixLift 3295986
  have htrace : WordTrace (prefixWord ++ tailWord_3295986) baseStart_3295986 baseEnd_3295986 := by
    simpa [prefixWord, tailWord_3295986, baseEnd_3295986] using wordTrace_append hprefix tailTrace_3295986
  have hstable : (prefixWord ++ tailWord_3295986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3295986).length < 2 ^ (prefixWord ++ tailWord_3295986).sum := by decide
  have hdescent : baseEnd_3295986 < baseStart_3295986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3295986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296018 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3296018 : Nat := 118140960795 + 3296018 * 2 ^ 59
def prefixEnd_3296018 : Nat := 4983230072969 + 3 ^ 40 * 3296018 * 2
def baseEnd_3296018 : Nat := 1128294319913993698744597

theorem tailTrace_3296018 : CollatzResearch.WordTrace tailWord_3296018 prefixEnd_3296018 1128294319913993698744597 := by
  unfold tailWord_3296018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30053913143274293975888177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80143768382064783935701805 30053913143274293975888177)
  ·
    refine ⟨22540434857455720481916133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30053913143274293975888177 22540434857455720481916133)
    ·
      refine ⟨4226331535772947590359275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22540434857455720481916133 4226331535772947590359275)
      ·
        refine ⟨6339497303659421385538913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226331535772947590359275 6339497303659421385538913)
        ·
          refine ⟨4754622977744566039154185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339497303659421385538913 4754622977744566039154185)
          ·
            refine ⟨3565967233308424529365639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754622977744566039154185 3565967233308424529365639)
            ·
              refine ⟨5348950849962636794048459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565967233308424529365639 5348950849962636794048459)
              ·
                refine ⟨8023426274943955191072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348950849962636794048459 8023426274943955191072689)
                ·
                  refine ⟨6017569706207966393304517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8023426274943955191072689 6017569706207966393304517)
                  ·
                    refine ⟨1128294319913993698744597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017569706207966393304517 1128294319913993698744597)
                    ·
                      rfl

theorem cell22_3296018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3296018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296018 prefixEnd_3296018 := by exact prefixLift 3296018
  have htrace : WordTrace (prefixWord ++ tailWord_3296018) baseStart_3296018 baseEnd_3296018 := by
    simpa [prefixWord, tailWord_3296018, baseEnd_3296018] using wordTrace_append hprefix tailTrace_3296018
  have hstable : (prefixWord ++ tailWord_3296018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296018).length < 2 ^ (prefixWord ++ tailWord_3296018).sum := by decide
  have hdescent : baseEnd_3296018 < baseStart_3296018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296031 : List Nat := [1, 1, 2, 4, 2, 2, 1, 5, 1, 3]
def baseStart_3296031 : Nat := 118140960795 + 3296031 * 2 ^ 59
def prefixEnd_3296031 : Nat := 4983230072969 + 3 ^ 40 * 3296031 * 2
def baseEnd_3296031 : Nat := 1128298770079665998169557

theorem tailTrace_3296031 : CollatzResearch.WordTrace tailWord_3296031 prefixEnd_3296031 1128298770079665998169557 := by
  unfold tailWord_3296031
  simp only [CollatzResearch.WordTrace]
  refine ⟨120216126722050079123775947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80144084481366719415850631 120216126722050079123775947)
  ·
    refine ⟨180324190083075118685663921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120216126722050079123775947 180324190083075118685663921)
    ·
      refine ⟨135243142562306339014247941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180324190083075118685663921 135243142562306339014247941)
      ·
        refine ⟨25358089230432438565171489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135243142562306339014247941 25358089230432438565171489)
        ·
          refine ⟨19018566922824328923878617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25358089230432438565171489 19018566922824328923878617)
          ·
            refine ⟨14263925192118246692908963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19018566922824328923878617 14263925192118246692908963)
            ·
              refine ⟨21395887788177370039363445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14263925192118246692908963 21395887788177370039363445)
              ·
                refine ⟨2005864480141628441190323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21395887788177370039363445 2005864480141628441190323)
                ·
                  refine ⟨3008796720212442661785485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005864480141628441190323 3008796720212442661785485)
                  ·
                    refine ⟨1128298770079665998169557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008796720212442661785485 1128298770079665998169557)
                    ·
                      rfl

theorem cell22_3296031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 1, 3].length) (baseStart_3296031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296031 prefixEnd_3296031 := by exact prefixLift 3296031
  have htrace : WordTrace (prefixWord ++ tailWord_3296031) baseStart_3296031 baseEnd_3296031 := by
    simpa [prefixWord, tailWord_3296031, baseEnd_3296031] using wordTrace_append hprefix tailTrace_3296031
  have hstable : (prefixWord ++ tailWord_3296031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296031).length < 2 ^ (prefixWord ++ tailWord_3296031).sum := by decide
  have hdescent : baseEnd_3296031 < baseStart_3296031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296072 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_3296072 : Nat := 118140960795 + 3296072 * 2 ^ 59
def prefixEnd_3296072 : Nat := 4983230072969 + 3 ^ 40 * 3296072 * 2
def baseEnd_3296072 : Nat := 376104268405851852631477

theorem tailTrace_3296072 : CollatzResearch.WordTrace tailWord_3296072 prefixEnd_3296072 376104268405851852631477 := by
  unfold tailWord_3296072
  simp only [CollatzResearch.WordTrace]
  refine ⟨60108811057450771563009235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80145081409934362084012313 60108811057450771563009235)
  ·
    refine ⟨90163216586176157344513853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60108811057450771563009235 90163216586176157344513853)
    ·
      refine ⟨33811206219816059004192695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90163216586176157344513853 33811206219816059004192695)
      ·
        refine ⟨50716809329724088506289043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33811206219816059004192695 50716809329724088506289043)
        ·
          refine ⟨76075213994586132759433565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50716809329724088506289043 76075213994586132759433565)
          ·
            refine ⟨28528205247969799784787587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76075213994586132759433565 28528205247969799784787587)
            ·
              refine ⟨42792307871954699677181381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28528205247969799784787587 42792307871954699677181381)
              ·
                refine ⟨8023557725991506189471509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42792307871954699677181381 8023557725991506189471509)
                ·
                  refine ⟨376104268405851852631477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8023557725991506189471509 376104268405851852631477)
                  ·
                    rfl

theorem cell22_3296072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_3296072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296072 prefixEnd_3296072 := by exact prefixLift 3296072
  have htrace : WordTrace (prefixWord ++ tailWord_3296072) baseStart_3296072 baseEnd_3296072 := by
    simpa [prefixWord, tailWord_3296072, baseEnd_3296072] using wordTrace_append hprefix tailTrace_3296072
  have hstable : (prefixWord ++ tailWord_3296072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296072).length < 2 ^ (prefixWord ++ tailWord_3296072).sum := by decide
  have hdescent : baseEnd_3296072 < baseStart_3296072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296121 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_3296121 : Nat := 118140960795 + 3296121 * 2 ^ 59
def prefixEnd_3296121 : Nat := 4983230072969 + 3 ^ 40 * 3296121 * 2
def baseEnd_3296121 : Nat := 1128329578918935763419281

theorem tailTrace_3296121 : CollatzResearch.WordTrace tailWord_3296121 prefixEnd_3296121 1128329578918935763419281 := by
  unfold tailWord_3296121
  simp only [CollatzResearch.WordTrace]
  refine ⟨120219409291724024494552217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80146272861149349663034811 120219409291724024494552217)
  ·
    refine ⟨90164556968793018370914163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120219409291724024494552217 90164556968793018370914163)
    ·
      refine ⟨135246835453189527556371245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90164556968793018370914163 135246835453189527556371245)
      ·
        refine ⟨50717563294946072833639217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135246835453189527556371245 50717563294946072833639217)
        ·
          refine ⟨38038172471209554625229413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50717563294946072833639217 38038172471209554625229413)
          ·
            refine ⟨7132157338351791492230515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38038172471209554625229413 7132157338351791492230515)
            ·
              refine ⟨10698236007527687238345773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132157338351791492230515 10698236007527687238345773)
              ·
                refine ⟨4011838502822882714379665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10698236007527687238345773 4011838502822882714379665)
                ·
                  refine ⟨3008878877117162035784749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4011838502822882714379665 3008878877117162035784749)
                  ·
                    refine ⟨1128329578918935763419281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008878877117162035784749 1128329578918935763419281)
                    ·
                      rfl

theorem cell22_3296121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_3296121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296121 prefixEnd_3296121 := by exact prefixLift 3296121
  have htrace : WordTrace (prefixWord ++ tailWord_3296121) baseStart_3296121 baseEnd_3296121 := by
    simpa [prefixWord, tailWord_3296121, baseEnd_3296121] using wordTrace_append hprefix tailTrace_3296121
  have hstable : (prefixWord ++ tailWord_3296121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296121).length < 2 ^ (prefixWord ++ tailWord_3296121).sum := by decide
  have hdescent : baseEnd_3296121 < baseStart_3296121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296136 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3296136 : Nat := 118140960795 + 3296136 * 2 ^ 59
def prefixEnd_3296136 : Nat := 4983230072969 + 3 ^ 40 * 3296136 * 2
def baseEnd_3296136 : Nat := 1128334713725480724294235

theorem tailTrace_3296136 : CollatzResearch.WordTrace tailWord_3296136 prefixEnd_3296136 1128334713725480724294235 := by
  unfold tailWord_3296136
  simp only [CollatzResearch.WordTrace]
  refine ⟨60109978193334841028174131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80146637591113121370898841 60109978193334841028174131)
  ·
    refine ⟨90164967290002261542261197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60109978193334841028174131 90164967290002261542261197)
    ·
      refine ⟨33811862733750848078347949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90164967290002261542261197 33811862733750848078347949)
      ·
        refine ⟨12679448525156568029380481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33811862733750848078347949 12679448525156568029380481)
        ·
          refine ⟨9509586393867426022035361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12679448525156568029380481 9509586393867426022035361)
          ·
            refine ⟨7132189795400569516526521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9509586393867426022035361 7132189795400569516526521)
            ·
              refine ⟨5349142346550427137394891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7132189795400569516526521 5349142346550427137394891)
              ·
                refine ⟨8023713519825640706092337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349142346550427137394891 8023713519825640706092337)
                ·
                  refine ⟨6017785139869230529569253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8023713519825640706092337 6017785139869230529569253)
                  ·
                    refine ⟨1128334713725480724294235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017785139869230529569253 1128334713725480724294235)
                    ·
                      rfl

theorem cell22_3296136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3296136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296136 prefixEnd_3296136 := by exact prefixLift 3296136
  have htrace : WordTrace (prefixWord ++ tailWord_3296136) baseStart_3296136 baseEnd_3296136 := by
    simpa [prefixWord, tailWord_3296136, baseEnd_3296136] using wordTrace_append hprefix tailTrace_3296136
  have hstable : (prefixWord ++ tailWord_3296136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296136).length < 2 ^ (prefixWord ++ tailWord_3296136).sum := by decide
  have hdescent : baseEnd_3296136 < baseStart_3296136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296200 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_3296200 : Nat := 118140960795 + 3296200 * 2 ^ 59
def prefixEnd_3296200 : Nat := 4983230072969 + 3 ^ 40 * 3296200 * 2
def baseEnd_3296200 : Nat := 1128356622233405890694039

theorem tailTrace_3296200 : CollatzResearch.WordTrace tailWord_3296200 prefixEnd_3296200 1128356622233405890694039 := by
  unfold tailWord_3296200
  simp only [CollatzResearch.WordTrace]
  refine ⟨60111145329218910493339027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80148193772291880657785369 60111145329218910493339027)
  ·
    refine ⟨90166717993828365740008541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60111145329218910493339027 90166717993828365740008541)
    ·
      refine ⟨33812519247685637152503203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90166717993828365740008541 33812519247685637152503203)
      ·
        refine ⟨50718778871528455728754805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33812519247685637152503203 50718778871528455728754805)
        ·
          refine ⟨4754885519205792724570763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50718778871528455728754805 4754885519205792724570763)
          ·
            refine ⟨7132328278808689086856145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754885519205792724570763 7132328278808689086856145)
            ·
              refine ⟨5349246209106516815142109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7132328278808689086856145 5349246209106516815142109)
              ·
                refine ⟨2005967328414943805678291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5349246209106516815142109 2005967328414943805678291)
                ·
                  refine ⟨3008950992622415708517437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2005967328414943805678291 3008950992622415708517437)
                  ·
                    refine ⟨1128356622233405890694039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3008950992622415708517437 1128356622233405890694039)
                    ·
                      rfl

theorem cell22_3296200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_3296200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296200 prefixEnd_3296200 := by exact prefixLift 3296200
  have htrace : WordTrace (prefixWord ++ tailWord_3296200) baseStart_3296200 baseEnd_3296200 := by
    simpa [prefixWord, tailWord_3296200, baseEnd_3296200] using wordTrace_append hprefix tailTrace_3296200
  have hstable : (prefixWord ++ tailWord_3296200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296200).length < 2 ^ (prefixWord ++ tailWord_3296200).sum := by decide
  have hdescent : baseEnd_3296200 < baseStart_3296200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296213 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 5]
def baseStart_3296213 : Nat := 118140960795 + 3296213 * 2 ^ 59
def prefixEnd_3296213 : Nat := 4983230072969 + 3 ^ 40 * 3296213 * 2
def baseEnd_3296213 : Nat := 376120357466359396706333

theorem tailTrace_3296213 : CollatzResearch.WordTrace tailWord_3296213 prefixEnd_3296213 376120357466359396706333 := by
  unfold tailWord_3296213
  simp only [CollatzResearch.WordTrace]
  refine ⟨120222764807390724206901293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80148509871593816137934195 120222764807390724206901293)
  ·
    refine ⟨45083536802771521577587985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120222764807390724206901293 45083536802771521577587985)
    ·
      refine ⟨33812652602078641183190989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45083536802771521577587985 33812652602078641183190989)
      ·
        refine ⟨12679744725779490443696621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33812652602078641183190989 12679744725779490443696621)
        ·
          refine ⟨4754904272167308916386233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12679744725779490443696621 4754904272167308916386233)
          ·
            refine ⟨3566178204125481687289675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754904272167308916386233 3566178204125481687289675)
            ·
              refine ⟨5349267306188222530934513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566178204125481687289675 5349267306188222530934513)
              ·
                refine ⟨4011950479641166898200885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349267306188222530934513 4011950479641166898200885)
                ·
                  refine ⟨376120357466359396706333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011950479641166898200885 376120357466359396706333)
                  ·
                    rfl

theorem cell22_3296213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_3296213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296213 prefixEnd_3296213 := by exact prefixLift 3296213
  have htrace : WordTrace (prefixWord ++ tailWord_3296213) baseStart_3296213 baseEnd_3296213 := by
    simpa [prefixWord, tailWord_3296213, baseEnd_3296213] using wordTrace_append hprefix tailTrace_3296213
  have hstable : (prefixWord ++ tailWord_3296213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296213).length < 2 ^ (prefixWord ++ tailWord_3296213).sum := by decide
  have hdescent : baseEnd_3296213 < baseStart_3296213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296290 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3296290 : Nat := 118140960795 + 3296290 * 2 ^ 59
def prefixEnd_3296290 : Nat := 4983230072969 + 3 ^ 40 * 3296290 * 2
def baseEnd_3296290 : Nat := 1128387431072675655943763

theorem tailTrace_3296290 : CollatzResearch.WordTrace tailWord_3296290 prefixEnd_3296290 1128387431072675655943763 := by
  unfold tailWord_3296290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30056393307027941589363581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80150382152074510904969549 30056393307027941589363581)
  ·
    refine ⟨11271147490135478096011343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30056393307027941589363581 11271147490135478096011343)
    ·
      refine ⟨16906721235203217144017015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11271147490135478096011343 16906721235203217144017015)
      ·
        refine ⟨25360081852804825716025523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906721235203217144017015 25360081852804825716025523)
        ·
          refine ⟨38040122779207238574038285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25360081852804825716025523 38040122779207238574038285)
          ·
            refine ⟨14265046042202714465264357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38040122779207238574038285 14265046042202714465264357)
            ·
              refine ⟨2674696132913008962237067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14265046042202714465264357 2674696132913008962237067)
              ·
                refine ⟨4012044199369513443355601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674696132913008962237067 4012044199369513443355601)
                ·
                  refine ⟨3009033149527135082516701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012044199369513443355601 3009033149527135082516701)
                  ·
                    refine ⟨1128387431072675655943763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009033149527135082516701 1128387431072675655943763)
                    ·
                      rfl

theorem cell22_3296290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3296290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296290 prefixEnd_3296290 := by exact prefixLift 3296290
  have htrace : WordTrace (prefixWord ++ tailWord_3296290) baseStart_3296290 baseEnd_3296290 := by
    simpa [prefixWord, tailWord_3296290, baseEnd_3296290] using wordTrace_append hprefix tailTrace_3296290
  have hstable : (prefixWord ++ tailWord_3296290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296290).length < 2 ^ (prefixWord ++ tailWord_3296290).sum := by decide
  have hdescent : baseEnd_3296290 < baseStart_3296290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296314 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_3296314 : Nat := 118140960795 + 3296314 * 2 ^ 59
def prefixEnd_3296314 : Nat := 4983230072969 + 3 ^ 40 * 3296314 * 2
def baseEnd_3296314 : Nat := 376131882254382531114563

theorem tailTrace_3296314 : CollatzResearch.WordTrace tailWord_3296314 prefixEnd_3296314 376131882254382531114563 := by
  unfold tailWord_3296314
  simp only [CollatzResearch.WordTrace]
  refine ⟨30056612145006204614081999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80150965720016545637551997 30056612145006204614081999)
  ·
    refine ⟨45084918217509306921122999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30056612145006204614081999 45084918217509306921122999)
    ·
      refine ⟨67627377326263960381684499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45084918217509306921122999 67627377326263960381684499)
      ·
        refine ⟨101441065989395940572526749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67627377326263960381684499 101441065989395940572526749)
        ·
          refine ⟨38040399746023477714697531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101441065989395940572526749 38040399746023477714697531)
          ·
            refine ⟨57060599619035216572046297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38040399746023477714697531 57060599619035216572046297)
            ·
              refine ⟨42795449714276412429034723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57060599619035216572046297 42795449714276412429034723)
              ·
                refine ⟨64193174571414618643552085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42795449714276412429034723 64193174571414618643552085)
                ·
                  refine ⟨376131882254382531114563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64193174571414618643552085 376131882254382531114563)
                  ·
                    rfl

theorem cell22_3296314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_3296314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296314 prefixEnd_3296314 := by exact prefixLift 3296314
  have htrace : WordTrace (prefixWord ++ tailWord_3296314) baseStart_3296314 baseEnd_3296314 := by
    simpa [prefixWord, tailWord_3296314, baseEnd_3296314] using wordTrace_append hprefix tailTrace_3296314
  have hstable : (prefixWord ++ tailWord_3296314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296314).length < 2 ^ (prefixWord ++ tailWord_3296314).sum := by decide
  have hdescent : baseEnd_3296314 < baseStart_3296314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296361 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_3296361 : Nat := 118140960795 + 3296361 * 2 ^ 59
def prefixEnd_3296361 : Nat := 4983230072969 + 3 ^ 40 * 3296361 * 2
def baseEnd_3296361 : Nat := 1128411735823655137418545

theorem tailTrace_3296361 : CollatzResearch.WordTrace tailWord_3296361 prefixEnd_3296361 1128411735823655137418545 := by
  unfold tailWord_3296361
  simp only [CollatzResearch.WordTrace]
  refine ⟨120228162810854545483288937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80152108540569696988859291 120228162810854545483288937)
  ·
    refine ⟨90171122108140909112466703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120228162810854545483288937 90171122108140909112466703)
    ·
      refine ⟨135256683162211363668700055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90171122108140909112466703 135256683162211363668700055)
      ·
        refine ⟨202885024743317045503050083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135256683162211363668700055 202885024743317045503050083)
        ·
          refine ⟨304327537114975568254575125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202885024743317045503050083 304327537114975568254575125)
          ·
            refine ⟨14265353302264479761933209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304327537114975568254575125 14265353302264479761933209)
            ·
              refine ⟨10699014976698359821449907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265353302264479761933209 10699014976698359821449907)
              ·
                refine ⟨16048522465047539732174861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699014976698359821449907 16048522465047539732174861)
                ·
                  refine ⟨6018195924392827399565573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16048522465047539732174861 6018195924392827399565573)
                  ·
                    refine ⟨1128411735823655137418545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018195924392827399565573 1128411735823655137418545)
                    ·
                      rfl

theorem cell22_3296361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_3296361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296361 prefixEnd_3296361 := by exact prefixLift 3296361
  have htrace : WordTrace (prefixWord ++ tailWord_3296361) baseStart_3296361 baseEnd_3296361 := by
    simpa [prefixWord, tailWord_3296361, baseEnd_3296361] using wordTrace_append hprefix tailTrace_3296361
  have hstable : (prefixWord ++ tailWord_3296361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296361).length < 2 ^ (prefixWord ++ tailWord_3296361).sum := by decide
  have hdescent : baseEnd_3296361 < baseStart_3296361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296382 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3296382 : Nat := 118140960795 + 3296382 * 2 ^ 59
def prefixEnd_3296382 : Nat := 4983230072969 + 3 ^ 40 * 3296382 * 2
def baseEnd_3296382 : Nat := 376139641517606027547827

theorem tailTrace_3296382 : CollatzResearch.WordTrace tailWord_3296382 prefixEnd_3296382 376139641517606027547827 := by
  unfold tailWord_3296382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15028616092972308258725425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80152619162518977379868933 15028616092972308258725425)
  ·
    refine ⟨11271462069729231194044069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15028616092972308258725425 11271462069729231194044069)
    ·
      refine ⟨2113399138074230848883263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11271462069729231194044069 2113399138074230848883263)
      ·
        refine ⟨3170098707111346273324895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113399138074230848883263 3170098707111346273324895)
        ·
          refine ⟨4755148060667019409987343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170098707111346273324895 4755148060667019409987343)
          ·
            refine ⟨7132722091000529114981015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755148060667019409987343 7132722091000529114981015)
            ·
              refine ⟨10699083136500793672471523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132722091000529114981015 10699083136500793672471523)
              ·
                refine ⟨16048624704751190508707285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699083136500793672471523 16048624704751190508707285)
                ·
                  refine ⟨376139641517606027547827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16048624704751190508707285 376139641517606027547827)
                  ·
                    rfl

theorem cell22_3296382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3296382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296382 prefixEnd_3296382 := by exact prefixLift 3296382
  have htrace : WordTrace (prefixWord ++ tailWord_3296382) baseStart_3296382 baseEnd_3296382 := by
    simpa [prefixWord, tailWord_3296382, baseEnd_3296382] using wordTrace_append hprefix tailTrace_3296382
  have hstable : (prefixWord ++ tailWord_3296382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296382).length < 2 ^ (prefixWord ++ tailWord_3296382).sum := by decide
  have hdescent : baseEnd_3296382 < baseStart_3296382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296393 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 4]
def baseStart_3296393 : Nat := 118140960795 + 3296393 * 2 ^ 59
def prefixEnd_3296393 : Nat := 4983230072969 + 3 ^ 40 * 3296393 * 2
def baseEnd_3296393 : Nat := 376140896692539240206149

theorem tailTrace_3296393 : CollatzResearch.WordTrace tailWord_3296393 prefixEnd_3296393 376140896692539240206149 := by
  unfold tailWord_3296393
  simp only [CollatzResearch.WordTrace]
  refine ⟨120229329946738614948453833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80152886631159076632302555 120229329946738614948453833)
  ·
    refine ⟨90171997460053961211340375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120229329946738614948453833 90171997460053961211340375)
    ·
      refine ⟨135257996190080941817010563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90171997460053961211340375 135257996190080941817010563)
      ·
        refine ⟨202886994285121412725515845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135257996190080941817010563 202886994285121412725515845)
        ·
          refine ⟨38041311428460264886034221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202886994285121412725515845 38041311428460264886034221)
          ·
            refine ⟨14265491785672599332262833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38041311428460264886034221 14265491785672599332262833)
            ·
              refine ⟨10699118839254449499197125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265491785672599332262833 10699118839254449499197125)
              ·
                refine ⟨2006084782360209281099461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10699118839254449499197125 2006084782360209281099461)
                ·
                  refine ⟨376140896692539240206149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006084782360209281099461 376140896692539240206149)
                  ·
                    rfl

theorem cell22_3296393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_3296393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296393 prefixEnd_3296393 := by exact prefixLift 3296393
  have htrace : WordTrace (prefixWord ++ tailWord_3296393) baseStart_3296393 baseEnd_3296393 := by
    simpa [prefixWord, tailWord_3296393, baseEnd_3296393] using wordTrace_append hprefix tailTrace_3296393
  have hstable : (prefixWord ++ tailWord_3296393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296393).length < 2 ^ (prefixWord ++ tailWord_3296393).sum := by decide
  have hdescent : baseEnd_3296393 < baseStart_3296393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296408 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3296408 : Nat := 118140960795 + 3296408 * 2 ^ 59
def prefixEnd_3296408 : Nat := 4983230072969 + 3 ^ 40 * 3296408 * 2
def baseEnd_3296408 : Nat := 1128427824884162681493401

theorem tailTrace_3296408 : CollatzResearch.WordTrace tailWord_3296408 prefixEnd_3296408 1128427824884162681493401 := by
  unfold tailWord_3296408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60114938520842136255124939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80153251361122848340166585 60114938520842136255124939)
  ·
    refine ⟨90172407781263204382687409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60114938520842136255124939 90172407781263204382687409)
    ·
      refine ⟨67629305835947403287015557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90172407781263204382687409 67629305835947403287015557)
      ·
        refine ⟨12680494844240138116315417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67629305835947403287015557 12680494844240138116315417)
        ·
          refine ⟨9510371133180103587236563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12680494844240138116315417 9510371133180103587236563)
          ·
            refine ⟨14265556699770155380854845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510371133180103587236563 14265556699770155380854845)
            ·
              refine ⟨5349583762413808267820567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14265556699770155380854845 5349583762413808267820567)
              ·
                refine ⟨8024375643620712401730851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349583762413808267820567 8024375643620712401730851)
                ·
                  refine ⟨12036563465431068602596277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024375643620712401730851 12036563465431068602596277)
                  ·
                    refine ⟨1128427824884162681493401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12036563465431068602596277 1128427824884162681493401)
                    ·
                      rfl

theorem cell22_3296408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3296408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296408 prefixEnd_3296408 := by exact prefixLift 3296408
  have htrace : WordTrace (prefixWord ++ tailWord_3296408) baseStart_3296408 baseEnd_3296408 := by
    simpa [prefixWord, tailWord_3296408, baseEnd_3296408] using wordTrace_append hprefix tailTrace_3296408
  have hstable : (prefixWord ++ tailWord_3296408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296408).length < 2 ^ (prefixWord ++ tailWord_3296408).sum := by decide
  have hdescent : baseEnd_3296408 < baseStart_3296408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296421 : List Nat := [1, 3, 1, 2, 1, 5, 1, 8]
def baseStart_3296421 : Nat := 118140960795 + 3296421 * 2 ^ 59
def prefixEnd_3296421 : Nat := 4983230072969 + 3 ^ 40 * 3296421 * 2
def baseEnd_3296421 : Nat := 125381363894426108990929

theorem tailTrace_3296421 : CollatzResearch.WordTrace tailWord_3296421 prefixEnd_3296421 125381363894426108990929 := by
  unfold tailWord_3296421
  simp only [CollatzResearch.WordTrace]
  refine ⟨120230351190637175730473117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80153567460424783820315411 120230351190637175730473117)
  ·
    refine ⟨45086381696488940898927419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120230351190637175730473117 45086381696488940898927419)
    ·
      refine ⟨67629572544733411348391129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45086381696488940898927419 67629572544733411348391129)
      ·
        refine ⟨50722179408550058511293347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67629572544733411348391129 50722179408550058511293347)
        ·
          refine ⟨76083269112825087766940021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50722179408550058511293347 76083269112825087766940021)
          ·
            refine ⟨7132806479327351978150627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76083269112825087766940021 7132806479327351978150627)
            ·
              refine ⟨10699209718991027967225941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132806479327351978150627 10699209718991027967225941)
              ·
                refine ⟨125381363894426108990929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10699209718991027967225941 125381363894426108990929)
                ·
                  rfl

theorem cell22_3296421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 8].length) (baseStart_3296421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296421 prefixEnd_3296421 := by exact prefixLift 3296421
  have htrace : WordTrace (prefixWord ++ tailWord_3296421) baseStart_3296421 baseEnd_3296421 := by
    simpa [prefixWord, tailWord_3296421, baseEnd_3296421] using wordTrace_append hprefix tailTrace_3296421
  have hstable : (prefixWord ++ tailWord_3296421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296421).length < 2 ^ (prefixWord ++ tailWord_3296421).sum := by decide
  have hdescent : baseEnd_3296421 < baseStart_3296421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296423 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3296423 : Nat := 118140960795 + 3296423 * 2 ^ 59
def prefixEnd_3296423 : Nat := 4983230072969 + 3 ^ 40 * 3296423 * 2
def baseEnd_3296423 : Nat := 1128432959690707642368355

theorem tailTrace_3296423 : CollatzResearch.WordTrace tailWord_3296423 prefixEnd_3296423 1128432959690707642368355 := by
  unfold tailWord_3296423
  simp only [CollatzResearch.WordTrace]
  refine ⟨120230424136629930072045923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80153616091086620048030615 120230424136629930072045923)
  ·
    refine ⟨180345636204944895108068885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120230424136629930072045923 180345636204944895108068885)
    ·
      refine ⟨8453701697106791958190729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180345636204944895108068885 8453701697106791958190729)
      ·
        refine ⟨6340276272830093968643047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8453701697106791958190729 6340276272830093968643047)
        ·
          refine ⟨9510414409245140952964571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340276272830093968643047 9510414409245140952964571)
          ·
            refine ⟨14265621613867711429446857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510414409245140952964571 14265621613867711429446857)
            ·
              refine ⟨10699216210400783572085143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265621613867711429446857 10699216210400783572085143)
              ·
                refine ⟨16048824315601175358127715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699216210400783572085143 16048824315601175358127715)
                ·
                  refine ⟨24073236473401763037191573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16048824315601175358127715 24073236473401763037191573)
                  ·
                    refine ⟨1128432959690707642368355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24073236473401763037191573 1128432959690707642368355)
                    ·
                      rfl

theorem cell22_3296423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3296423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296423 prefixEnd_3296423 := by exact prefixLift 3296423
  have htrace : WordTrace (prefixWord ++ tailWord_3296423) baseStart_3296423 baseEnd_3296423 := by
    simpa [prefixWord, tailWord_3296423, baseEnd_3296423] using wordTrace_append hprefix tailTrace_3296423
  have hstable : (prefixWord ++ tailWord_3296423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296423).length < 2 ^ (prefixWord ++ tailWord_3296423).sum := by decide
  have hdescent : baseEnd_3296423 < baseStart_3296423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296513 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3296513 : Nat := 118140960795 + 3296513 * 2 ^ 59
def prefixEnd_3296513 : Nat := 4983230072969 + 3 ^ 40 * 3296513 * 2
def baseEnd_3296513 : Nat := 1128463768529977407618079

theorem tailTrace_3296513 : CollatzResearch.WordTrace tailWord_3296513 prefixEnd_3296513 1128463768529977407618079 := by
  unfold tailWord_3296513
  simp only [CollatzResearch.WordTrace]
  refine ⟨120233706706303875442822193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80155804470869250295214795 120233706706303875442822193)
  ·
    refine ⟨90175280029727906582116645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120233706706303875442822193 90175280029727906582116645)
    ·
      refine ⟨16907865005573982484146871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90175280029727906582116645 16907865005573982484146871)
      ·
        refine ⟨25361797508360973726220307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16907865005573982484146871 25361797508360973726220307)
        ·
          refine ⟨38042696262541460589330461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25361797508360973726220307 38042696262541460589330461)
          ·
            refine ⟨14266011098453047720998923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38042696262541460589330461 14266011098453047720998923)
            ·
              refine ⟨21399016647679571581498385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14266011098453047720998923 21399016647679571581498385)
              ·
                refine ⟨16049262485759678686123789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21399016647679571581498385 16049262485759678686123789)
                ·
                  refine ⟨6018473432159879507296421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16049262485759678686123789 6018473432159879507296421)
                  ·
                    refine ⟨1128463768529977407618079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018473432159879507296421 1128463768529977407618079)
                    ·
                      rfl

theorem cell22_3296513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3296513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296513 prefixEnd_3296513 := by exact prefixLift 3296513
  have htrace : WordTrace (prefixWord ++ tailWord_3296513) baseStart_3296513 baseEnd_3296513 := by
    simpa [prefixWord, tailWord_3296513, baseEnd_3296513] using wordTrace_append hprefix tailTrace_3296513
  have hstable : (prefixWord ++ tailWord_3296513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296513).length < 2 ^ (prefixWord ++ tailWord_3296513).sum := by decide
  have hdescent : baseEnd_3296513 < baseStart_3296513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296547 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 1, 4]
def baseStart_3296547 : Nat := 118140960795 + 3296547 * 2 ^ 59
def prefixEnd_3296547 : Nat := 4983230072969 + 3 ^ 40 * 3296547 * 2
def baseEnd_3296547 : Nat := 1128475407424812652267975

theorem tailTrace_3296547 : CollatzResearch.WordTrace tailWord_3296547 prefixEnd_3296547 1128475407424812652267975 := by
  unfold tailWord_3296547
  simp only [CollatzResearch.WordTrace]
  refine ⟨120234946788180699249559895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80156631192120466166373263 120234946788180699249559895)
  ·
    refine ⟨180352420182271048874339843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120234946788180699249559895 180352420182271048874339843)
    ·
      refine ⟨270528630273406573311509765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180352420182271048874339843 270528630273406573311509765)
      ·
        refine ⟨50724118176263732495908081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270528630273406573311509765 50724118176263732495908081)
        ·
          refine ⟨38043088632197799371931061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50724118176263732495908081 38043088632197799371931061)
          ·
            refine ⟨3566539559268543691118537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38043088632197799371931061 3566539559268543691118537)
            ·
              refine ⟨2674904669451407768338903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3566539559268543691118537 2674904669451407768338903)
              ·
                refine ⟨4012357004177111652508355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2674904669451407768338903 4012357004177111652508355)
                ·
                  refine ⟨6018535506265667478762533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012357004177111652508355 6018535506265667478762533)
                  ·
                    refine ⟨1128475407424812652267975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018535506265667478762533 1128475407424812652267975)
                    ·
                      rfl

theorem cell22_3296547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 4].length) (baseStart_3296547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296547 prefixEnd_3296547 := by exact prefixLift 3296547
  have htrace : WordTrace (prefixWord ++ tailWord_3296547) baseStart_3296547 baseEnd_3296547 := by
    simpa [prefixWord, tailWord_3296547, baseEnd_3296547] using wordTrace_append hprefix tailTrace_3296547
  have hstable : (prefixWord ++ tailWord_3296547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296547).length < 2 ^ (prefixWord ++ tailWord_3296547).sum := by decide
  have hdescent : baseEnd_3296547 < baseStart_3296547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296577 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3296577 : Nat := 118140960795 + 3296577 * 2 ^ 59
def prefixEnd_3296577 : Nat := 4983230072969 + 3 ^ 40 * 3296577 * 2
def baseEnd_3296577 : Nat := 1128485677037902574017883

theorem tailTrace_3296577 : CollatzResearch.WordTrace tailWord_3296577 prefixEnd_3296577 1128485677037902574017883 := by
  unfold tailWord_3296577
  simp only [CollatzResearch.WordTrace]
  refine ⟨120236040978072014373151985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80157360652048009582101323 120236040978072014373151985)
  ·
    refine ⟨90177030733554010779863989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120236040978072014373151985 90177030733554010779863989)
    ·
      refine ⟨8454096631270688510612249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90177030733554010779863989 8454096631270688510612249)
      ·
        refine ⟨6340572473453016382959187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454096631270688510612249 6340572473453016382959187)
        ·
          refine ⟨9510858710179524574438781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340572473453016382959187 9510858710179524574438781)
          ·
            refine ⟨3566572016317321715414543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9510858710179524574438781 3566572016317321715414543)
            ·
              refine ⟨5349858024475982573121815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566572016317321715414543 5349858024475982573121815)
              ·
                refine ⟨8024787036713973859682723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349858024475982573121815 8024787036713973859682723)
                ·
                  refine ⟨12037180555070960789524085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024787036713973859682723 12037180555070960789524085)
                  ·
                    refine ⟨1128485677037902574017883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037180555070960789524085 1128485677037902574017883)
                    ·
                      rfl

theorem cell22_3296577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3296577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296577 prefixEnd_3296577 := by exact prefixLift 3296577
  have htrace : WordTrace (prefixWord ++ tailWord_3296577) baseStart_3296577 baseEnd_3296577 := by
    simpa [prefixWord, tailWord_3296577, baseEnd_3296577] using wordTrace_append hprefix tailTrace_3296577
  have hstable : (prefixWord ++ tailWord_3296577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296577).length < 2 ^ (prefixWord ++ tailWord_3296577).sum := by decide
  have hdescent : baseEnd_3296577 < baseStart_3296577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296633 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3296633 : Nat := 118140960795 + 3296633 * 2 ^ 59
def prefixEnd_3296633 : Nat := 4983230072969 + 3 ^ 40 * 3296633 * 2
def baseEnd_3296633 : Nat := 1128504846982337094617711

theorem tailTrace_3296633 : CollatzResearch.WordTrace tailWord_3296633 prefixEnd_3296633 1128504846982337094617711 := by
  unfold tailWord_3296633
  simp only [CollatzResearch.WordTrace]
  refine ⟨120238083465869135937190553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80158722310579423958127035 120238083465869135937190553)
  ·
    refine ⟨90178562599401851952892915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120238083465869135937190553 90178562599401851952892915)
    ·
      refine ⟨135267843899102777929339373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90178562599401851952892915 135267843899102777929339373)
      ·
        refine ⟨50725441462163541723502265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135267843899102777929339373 50725441462163541723502265)
        ·
          refine ⟨38044081096622656292626699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50725441462163541723502265 38044081096622656292626699)
          ·
            refine ⟨57066121644933984438940049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38044081096622656292626699 57066121644933984438940049)
            ·
              refine ⟨42799591233700488329205037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57066121644933984438940049 42799591233700488329205037)
              ·
                refine ⟨16049846712637683123451889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42799591233700488329205037 16049846712637683123451889)
                ·
                  refine ⟨12037385034478262342588917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16049846712637683123451889 12037385034478262342588917)
                  ·
                    refine ⟨1128504846982337094617711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037385034478262342588917 1128504846982337094617711)
                    ·
                      rfl

theorem cell22_3296633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3296633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296633 prefixEnd_3296633 := by exact prefixLift 3296633
  have htrace : WordTrace (prefixWord ++ tailWord_3296633) baseStart_3296633 baseEnd_3296633 := by
    simpa [prefixWord, tailWord_3296633, baseEnd_3296633] using wordTrace_append hprefix tailTrace_3296633
  have hstable : (prefixWord ++ tailWord_3296633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296633).length < 2 ^ (prefixWord ++ tailWord_3296633).sum := by decide
  have hdescent : baseEnd_3296633 < baseStart_3296633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296695 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3296695 : Nat := 118140960795 + 3296695 * 2 ^ 59
def prefixEnd_3296695 : Nat := 4983230072969 + 3 ^ 40 * 3296695 * 2
def baseEnd_3296695 : Nat := 1128526070849389599567521

theorem tailTrace_3296695 : CollatzResearch.WordTrace tailWord_3296695 prefixEnd_3296695 1128526070849389599567521 := by
  unfold tailWord_3296695
  simp only [CollatzResearch.WordTrace]
  refine ⟨120240344791644520525947539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80160229861096347017298359 120240344791644520525947539)
  ·
    refine ⟨180360517187466780788921309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120240344791644520525947539 180360517187466780788921309)
    ·
      refine ⟨67635193945300042795845491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180360517187466780788921309 67635193945300042795845491)
      ·
        refine ⟨101452790917950064193768237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67635193945300042795845491 101452790917950064193768237)
        ·
          refine ⟨38044796594231274072663089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101452790917950064193768237 38044796594231274072663089)
          ·
            refine ⟨28533597445673455554497317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38044796594231274072663089 28533597445673455554497317)
            ·
              refine ⟨5350049521063772916468247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28533597445673455554497317 5350049521063772916468247)
              ·
                refine ⟨8025074281595659374702371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350049521063772916468247 8025074281595659374702371)
                ·
                  refine ⟨12037611422393489062053557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8025074281595659374702371 12037611422393489062053557)
                  ·
                    refine ⟨1128526070849389599567521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037611422393489062053557 1128526070849389599567521)
                    ·
                      rfl

theorem cell22_3296695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3296695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296695 prefixEnd_3296695 := by exact prefixLift 3296695
  have htrace : WordTrace (prefixWord ++ tailWord_3296695) baseStart_3296695 baseEnd_3296695 := by
    simpa [prefixWord, tailWord_3296695, baseEnd_3296695] using wordTrace_append hprefix tailTrace_3296695
  have hstable : (prefixWord ++ tailWord_3296695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296695).length < 2 ^ (prefixWord ++ tailWord_3296695).sum := by decide
  have hdescent : baseEnd_3296695 < baseStart_3296695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296729 : List Nat := [1, 2, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_3296729 : Nat := 118140960795 + 3296729 * 2 ^ 59
def prefixEnd_3296729 : Nat := 4983230072969 + 3 ^ 40 * 3296729 * 2
def baseEnd_3296729 : Nat := 1128537709744224844217417

theorem tailTrace_3296729 : CollatzResearch.WordTrace tailWord_3296729 prefixEnd_3296729 1128537709744224844217417 := by
  unfold tailWord_3296729
  simp only [CollatzResearch.WordTrace]
  refine ⟨120241584873521344332685241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80161056582347562888456827 120241584873521344332685241)
  ·
    refine ⟨90181188655141008249513931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120241584873521344332685241 90181188655141008249513931)
    ·
      refine ⟨135271782982711512374270897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90181188655141008249513931 135271782982711512374270897)
      ·
        refine ⟨101453837237033634280703173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135271782982711512374270897 101453837237033634280703173)
        ·
          refine ⟨19022594481943806427631845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101453837237033634280703173 19022594481943806427631845)
          ·
            refine ⟨3566736465364463705180971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19022594481943806427631845 3566736465364463705180971)
            ·
              refine ⟨5350104698046695557771457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566736465364463705180971 5350104698046695557771457)
              ·
                refine ⟨4012578523535021668328593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350104698046695557771457 4012578523535021668328593)
                ·
                  refine ⟨3009433892651266251246445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012578523535021668328593 3009433892651266251246445)
                  ·
                    refine ⟨1128537709744224844217417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009433892651266251246445 1128537709744224844217417)
                    ·
                      rfl

theorem cell22_3296729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_3296729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296729 prefixEnd_3296729 := by exact prefixLift 3296729
  have htrace : WordTrace (prefixWord ++ tailWord_3296729) baseStart_3296729 baseEnd_3296729 := by
    simpa [prefixWord, tailWord_3296729, baseEnd_3296729] using wordTrace_append hprefix tailTrace_3296729
  have hstable : (prefixWord ++ tailWord_3296729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296729).length < 2 ^ (prefixWord ++ tailWord_3296729).sum := by decide
  have hdescent : baseEnd_3296729 < baseStart_3296729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296746 : List Nat := [3, 1, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_3296746 : Nat := 118140960795 + 3296746 * 2 ^ 59
def prefixEnd_3296746 : Nat := 4983230072969 + 3 ^ 40 * 3296746 * 2
def baseEnd_3296746 : Nat := 1128543529191642466542365

theorem tailTrace_3296746 : CollatzResearch.WordTrace tailWord_3296746 prefixEnd_3296746 1128543529191642466542365 := by
  unfold tailWord_3296746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30060551228614939059013523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80161469942973170824036061 30060551228614939059013523)
  ·
    refine ⟨45090826842922408588520285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30060551228614939059013523 45090826842922408588520285)
    ·
      refine ⟨16909060066095903220695107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45090826842922408588520285 16909060066095903220695107)
      ·
        refine ⟨25363590099143854831042661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909060066095903220695107 25363590099143854831042661)
        ·
          refine ⟨4755673143589472780820499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25363590099143854831042661 4755673143589472780820499)
          ·
            refine ⟨7133509715384209171230749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755673143589472780820499 7133509715384209171230749)
            ·
              refine ⟨2675066143269078439211531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7133509715384209171230749 2675066143269078439211531)
              ·
                refine ⟨4012599214903617658817297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675066143269078439211531 4012599214903617658817297)
                ·
                  refine ⟨3009449411177713244112973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4012599214903617658817297 3009449411177713244112973)
                  ·
                    refine ⟨1128543529191642466542365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009449411177713244112973 1128543529191642466542365)
                    ·
                      rfl

theorem cell22_3296746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_3296746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296746 prefixEnd_3296746 := by exact prefixLift 3296746
  have htrace : WordTrace (prefixWord ++ tailWord_3296746) baseStart_3296746 baseEnd_3296746 := by
    simpa [prefixWord, tailWord_3296746, baseEnd_3296746] using wordTrace_append hprefix tailTrace_3296746
  have hstable : (prefixWord ++ tailWord_3296746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296746).length < 2 ^ (prefixWord ++ tailWord_3296746).sum := by decide
  have hdescent : baseEnd_3296746 < baseStart_3296746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296832 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_3296832 : Nat := 118140960795 + 3296832 * 2 ^ 59
def prefixEnd_3296832 : Nat := 4983230072969 + 3 ^ 40 * 3296832 * 2
def baseEnd_3296832 : Nat := 376190989583055636297367

theorem tailTrace_3296832 : CollatzResearch.WordTrace tailWord_3296832 prefixEnd_3296832 376190989583055636297367 := by
  unfold tailWord_3296832
  simp only [CollatzResearch.WordTrace]
  refine ⟨60122670796074096461842375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80163561061432128615789833 60122670796074096461842375)
  ·
    refine ⟨90184006194111144692763563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60122670796074096461842375 90184006194111144692763563)
    ·
      refine ⟨135276009291166717039145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90184006194111144692763563 135276009291166717039145345)
      ·
        refine ⟨101457006968375037779359009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135276009291166717039145345 101457006968375037779359009)
        ·
          refine ⟨76092755226281278334519257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101457006968375037779359009 76092755226281278334519257)
          ·
            refine ⟨57069566419710958750889443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76092755226281278334519257 57069566419710958750889443)
            ·
              refine ⟨85604349629566438126334165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57069566419710958750889443 85604349629566438126334165)
              ·
                refine ⟨2006351944442963393585957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85604349629566438126334165 2006351944442963393585957)
                ·
                  refine ⟨376190989583055636297367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006351944442963393585957 376190989583055636297367)
                  ·
                    rfl

theorem cell22_3296832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_3296832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296832 prefixEnd_3296832 := by exact prefixLift 3296832
  have htrace : WordTrace (prefixWord ++ tailWord_3296832) baseStart_3296832 baseEnd_3296832 := by
    simpa [prefixWord, tailWord_3296832, baseEnd_3296832] using wordTrace_append hprefix tailTrace_3296832
  have hstable : (prefixWord ++ tailWord_3296832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296832).length < 2 ^ (prefixWord ++ tailWord_3296832).sum := by decide
  have hdescent : baseEnd_3296832 < baseStart_3296832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296890 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_3296890 : Nat := 118140960795 + 3296890 * 2 ^ 59
def prefixEnd_3296890 : Nat := 4983230072969 + 3 ^ 40 * 3296890 * 2
def baseEnd_3296890 : Nat := 1128592823334474090941923

theorem tailTrace_3296890 : CollatzResearch.WordTrace tailWord_3296890 prefixEnd_3296890 1128592823334474090941923 := by
  unfold tailWord_3296890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30061864256484517207324031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80164971350625379219530749 30061864256484517207324031)
  ·
    refine ⟨45092796384726775810986047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30061864256484517207324031 45092796384726775810986047)
    ·
      refine ⟨67639194577090163716479071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45092796384726775810986047 67639194577090163716479071)
      ·
        refine ⟨101458791865635245574718607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67639194577090163716479071 101458791865635245574718607)
        ·
          refine ⟨152188187798452868362077911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101458791865635245574718607 152188187798452868362077911)
          ·
            refine ⟨228282281697679302543116867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152188187798452868362077911 228282281697679302543116867)
            ·
              refine ⟨342423422546518953814675301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228282281697679302543116867 342423422546518953814675301)
              ·
                refine ⟨64204391727472303840251619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342423422546518953814675301 64204391727472303840251619)
                ·
                  refine ⟨96306587591208455760377429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64204391727472303840251619 96306587591208455760377429)
                  ·
                    refine ⟨1128592823334474090941923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96306587591208455760377429 1128592823334474090941923)
                    ·
                      rfl

theorem cell22_3296890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_3296890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296890 prefixEnd_3296890 := by exact prefixLift 3296890
  have htrace : WordTrace (prefixWord ++ tailWord_3296890) baseStart_3296890 baseEnd_3296890 := by
    simpa [prefixWord, tailWord_3296890, baseEnd_3296890] using wordTrace_append hprefix tailTrace_3296890
  have hstable : (prefixWord ++ tailWord_3296890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296890).length < 2 ^ (prefixWord ++ tailWord_3296890).sum := by decide
  have hdescent : baseEnd_3296890 < baseStart_3296890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296892 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3296892 : Nat := 118140960795 + 3296892 * 2 ^ 59
def prefixEnd_3296892 : Nat := 4983230072969 + 3 ^ 40 * 3296892 * 2
def baseEnd_3296892 : Nat := 1128593507975346752391917

theorem tailTrace_3296892 : CollatzResearch.WordTrace tailWord_3296892 prefixEnd_3296892 1128593507975346752391917 := by
  unfold tailWord_3296892
  simp only [CollatzResearch.WordTrace]
  refine ⟨60123764985965411585434465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80165019981287215447245953 60123764985965411585434465)
  ·
    refine ⟨45092823739474058689075849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60123764985965411585434465 45092823739474058689075849)
    ·
      refine ⟨33819617804605544016806887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45092823739474058689075849 33819617804605544016806887)
      ·
        refine ⟨50729426706908316025210331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33819617804605544016806887 50729426706908316025210331)
        ·
          refine ⟨76094140060362474037815497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50729426706908316025210331 76094140060362474037815497)
          ·
            refine ⟨57070605045271855528361623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76094140060362474037815497 57070605045271855528361623)
            ·
              refine ⟨85605907567907783292542435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57070605045271855528361623 85605907567907783292542435)
              ·
                refine ⟨128408861351861674938813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85605907567907783292542435 128408861351861674938813653)
                ·
                  refine ⟨3009582687934258006378445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128408861351861674938813653 3009582687934258006378445)
                  ·
                    refine ⟨1128593507975346752391917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009582687934258006378445 1128593507975346752391917)
                    ·
                      rfl

theorem cell22_3296892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3296892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296892 prefixEnd_3296892 := by exact prefixLift 3296892
  have htrace : WordTrace (prefixWord ++ tailWord_3296892) baseStart_3296892 baseEnd_3296892 := by
    simpa [prefixWord, tailWord_3296892, baseEnd_3296892] using wordTrace_append hprefix tailTrace_3296892
  have hstable : (prefixWord ++ tailWord_3296892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296892).length < 2 ^ (prefixWord ++ tailWord_3296892).sum := by decide
  have hdescent : baseEnd_3296892 < baseStart_3296892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296926 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3296926 : Nat := 118140960795 + 3296926 * 2 ^ 59
def prefixEnd_3296926 : Nat := 4983230072969 + 3 ^ 40 * 3296926 * 2
def baseEnd_3296926 : Nat := 1128605146870181997041813

theorem tailTrace_3296926 : CollatzResearch.WordTrace tailWord_3296926 prefixEnd_3296926 1128605146870181997041813 := by
  unfold tailWord_3296926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031096256725955872200829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80165846702538431318404421 15031096256725955872200829)
  ·
    refine ⟨5636661096272233452075311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15031096256725955872200829 5636661096272233452075311)
    ·
      refine ⟨8454991644408350178112967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636661096272233452075311 8454991644408350178112967)
      ·
        refine ⟨12682487466612525267169451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454991644408350178112967 12682487466612525267169451)
        ·
          refine ⟨19023731199918787900754177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12682487466612525267169451 19023731199918787900754177)
          ·
            refine ⟨14267798399939090925565633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19023731199918787900754177 14267798399939090925565633)
            ·
              refine ⟨10700848799954318194174225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14267798399939090925565633 10700848799954318194174225)
              ·
                refine ⟨8025636599965738645630669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700848799954318194174225 8025636599965738645630669)
                ·
                  refine ⟨3009613724987151992111501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8025636599965738645630669 3009613724987151992111501)
                  ·
                    refine ⟨1128605146870181997041813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009613724987151992111501 1128605146870181997041813)
                    ·
                      rfl

theorem cell22_3296926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3296926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296926 prefixEnd_3296926 := by exact prefixLift 3296926
  have htrace : WordTrace (prefixWord ++ tailWord_3296926) baseStart_3296926 baseEnd_3296926 := by
    simpa [prefixWord, tailWord_3296926, baseEnd_3296926] using wordTrace_append hprefix tailTrace_3296926
  have hstable : (prefixWord ++ tailWord_3296926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296926).length < 2 ^ (prefixWord ++ tailWord_3296926).sum := by decide
  have hdescent : baseEnd_3296926 < baseStart_3296926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296973 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3296973 : Nat := 118140960795 + 3296973 * 2 ^ 59
def prefixEnd_3296973 : Nat := 4983230072969 + 3 ^ 40 * 3296973 * 2
def baseEnd_3296973 : Nat := 376207078643563180372223

theorem tailTrace_3296973 : CollatzResearch.WordTrace tailWord_3296973 prefixEnd_3296973 376207078643563180372223 := by
  unfold tailWord_3296973
  simp only [CollatzResearch.WordTrace]
  refine ⟨120250484284637374004567573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80166989523091582669711715 120250484284637374004567573)
  ·
    refine ⟨5636741450842376906464105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120250484284637374004567573 5636741450842376906464105)
    ·
      refine ⟨4227556088131782679848079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5636741450842376906464105 4227556088131782679848079)
      ·
        refine ⟨6341334132197674019772119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227556088131782679848079 6341334132197674019772119)
        ·
          refine ⟨9512001198296511029658179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341334132197674019772119 9512001198296511029658179)
          ·
            refine ⟨14268001797444766544487269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512001198296511029658179 14268001797444766544487269)
            ·
              refine ⟨2675250337020893727091363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14268001797444766544487269 2675250337020893727091363)
              ·
                refine ⟨4012875505531340590637045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675250337020893727091363 4012875505531340590637045)
                ·
                  refine ⟨376207078643563180372223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4012875505531340590637045 376207078643563180372223)
                  ·
                    rfl

theorem cell22_3296973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3296973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296973 prefixEnd_3296973 := by exact prefixLift 3296973
  have htrace : WordTrace (prefixWord ++ tailWord_3296973) baseStart_3296973 baseEnd_3296973 := by
    simpa [prefixWord, tailWord_3296973, baseEnd_3296973] using wordTrace_append hprefix tailTrace_3296973
  have hstable : (prefixWord ++ tailWord_3296973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296973).length < 2 ^ (prefixWord ++ tailWord_3296973).sum := by decide
  have hdescent : baseEnd_3296973 < baseStart_3296973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3296986 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_3296986 : Nat := 118140960795 + 3296986 * 2 ^ 59
def prefixEnd_3296986 : Nat := 4983230072969 + 3 ^ 40 * 3296986 * 2
def baseEnd_3296986 : Nat := 1128625686096361840541629

theorem tailTrace_3296986 : CollatzResearch.WordTrace tailWord_3296986 prefixEnd_3296986 1128625686096361840541629 := by
  unfold tailWord_3296986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30062739608397569306197703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80167305622393518149860541 30062739608397569306197703)
  ·
    refine ⟨45094109412596353959296555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30062739608397569306197703 45094109412596353959296555)
    ·
      refine ⟨67641164118894530938944833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45094109412596353959296555 67641164118894530938944833)
      ·
        refine ⟨50730873089170898204208625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67641164118894530938944833 50730873089170898204208625)
        ·
          refine ⟨38048154816878173653156469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50730873089170898204208625 38048154816878173653156469)
          ·
            refine ⟨3567014514082328779983419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38048154816878173653156469 3567014514082328779983419)
            ·
              refine ⟨5350521771123493169975129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567014514082328779983419 5350521771123493169975129)
              ·
                refine ⟨4012891328342619877481347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350521771123493169975129 4012891328342619877481347)
                ·
                  refine ⟨6019336992513929816222021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012891328342619877481347 6019336992513929816222021)
                  ·
                    refine ⟨1128625686096361840541629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019336992513929816222021 1128625686096361840541629)
                    ·
                      rfl

theorem cell22_3296986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_3296986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3296986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3296986 prefixEnd_3296986 := by exact prefixLift 3296986
  have htrace : WordTrace (prefixWord ++ tailWord_3296986) baseStart_3296986 baseEnd_3296986 := by
    simpa [prefixWord, tailWord_3296986, baseEnd_3296986] using wordTrace_append hprefix tailTrace_3296986
  have hstable : (prefixWord ++ tailWord_3296986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3296986).length < 2 ^ (prefixWord ++ tailWord_3296986).sum := by decide
  have hdescent : baseEnd_3296986 < baseStart_3296986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3296986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297054 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3297054 : Nat := 118140960795 + 3297054 * 2 ^ 59
def prefixEnd_3297054 : Nat := 4983230072969 + 3 ^ 40 * 3297054 * 2
def baseEnd_3297054 : Nat := 1128648963886032329841421

theorem tailTrace_3297054 : CollatzResearch.WordTrace tailWord_3297054 prefixEnd_3297054 1128648963886032329841421 := by
  unfold tailWord_3297054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031679824667990604783277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80168959064895949892177477 15031679824667990604783277)
  ·
    refine ⟨5636879934250496476793729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15031679824667990604783277 5636879934250496476793729)
    ·
      refine ⟨4227659950687872357595297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5636879934250496476793729 4227659950687872357595297)
      ·
        refine ⟨3170744963015904268196473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4227659950687872357595297 3170744963015904268196473)
        ·
          refine ⟨2378058722261928201147355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170744963015904268196473 2378058722261928201147355)
          ·
            refine ⟨3567088083392892301721033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378058722261928201147355 3567088083392892301721033)
            ·
              refine ⟨2675316062544669226290775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567088083392892301721033 2675316062544669226290775)
              ·
                refine ⟨4012974093817003839436163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675316062544669226290775 4012974093817003839436163)
                ·
                  refine ⟨6019461140725505759154245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012974093817003839436163 6019461140725505759154245)
                  ·
                    refine ⟨1128648963886032329841421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019461140725505759154245 1128648963886032329841421)
                    ·
                      rfl

theorem cell22_3297054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3297054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297054 prefixEnd_3297054 := by exact prefixLift 3297054
  have htrace : WordTrace (prefixWord ++ tailWord_3297054) baseStart_3297054 baseEnd_3297054 := by
    simpa [prefixWord, tailWord_3297054, baseEnd_3297054] using wordTrace_append hprefix tailTrace_3297054
  have hstable : (prefixWord ++ tailWord_3297054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297054).length < 2 ^ (prefixWord ++ tailWord_3297054).sum := by decide
  have hdescent : baseEnd_3297054 < baseStart_3297054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297074 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_3297074 : Nat := 118140960795 + 3297074 * 2 ^ 59
def prefixEnd_3297074 : Nat := 4983230072969 + 3 ^ 40 * 3297074 * 2
def baseEnd_3297074 : Nat := 376218603431586314780453

theorem tailTrace_3297074 : CollatzResearch.WordTrace tailWord_3297074 prefixEnd_3297074 376218603431586314780453 := by
  unfold tailWord_3297074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30063542014317867063498569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80169445371514312169329517 30063542014317867063498569)
  ·
    refine ⟨22547656510738400297623927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30063542014317867063498569 22547656510738400297623927)
    ·
      refine ⟨33821484766107600446435891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22547656510738400297623927 33821484766107600446435891)
      ·
        refine ⟨50732227149161400669653837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33821484766107600446435891 50732227149161400669653837)
        ·
          refine ⟨19024585180935525251120189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50732227149161400669653837 19024585180935525251120189)
          ·
            refine ⟨7134219442850821969170071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19024585180935525251120189 7134219442850821969170071)
            ·
              refine ⟨10701329164276232953755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134219442850821969170071 10701329164276232953755107)
              ·
                refine ⟨16051993746414349430632661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701329164276232953755107 16051993746414349430632661)
                ·
                  refine ⟨376218603431586314780453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16051993746414349430632661 376218603431586314780453)
                  ·
                    rfl

theorem cell22_3297074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_3297074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297074 prefixEnd_3297074 := by exact prefixLift 3297074
  have htrace : WordTrace (prefixWord ++ tailWord_3297074) baseStart_3297074 baseEnd_3297074 := by
    simpa [prefixWord, tailWord_3297074, baseEnd_3297074] using wordTrace_append hprefix tailTrace_3297074
  have hstable : (prefixWord ++ tailWord_3297074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297074).length < 2 ^ (prefixWord ++ tailWord_3297074).sum := by decide
  have hdescent : baseEnd_3297074 < baseStart_3297074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297078 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3297078 : Nat := 118140960795 + 3297078 * 2 ^ 59
def prefixEnd_3297078 : Nat := 4983230072969 + 3 ^ 40 * 3297078 * 2
def baseEnd_3297078 : Nat := 1128657179576504267241347

theorem tailTrace_3297078 : CollatzResearch.WordTrace tailWord_3297078 prefixEnd_3297078 1128657179576504267241347 := by
  unfold tailWord_3297078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7515894621828561058571243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80169542632837984624759925 7515894621828561058571243)
  ·
    refine ⟨11273841932742841587856865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7515894621828561058571243 11273841932742841587856865)
    ·
      refine ⟨8455381449557131190892649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11273841932742841587856865 8455381449557131190892649)
      ·
        refine ⟨6341536087167848393169487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8455381449557131190892649 6341536087167848393169487)
        ·
          refine ⟨9512304130751772589754231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341536087167848393169487 9512304130751772589754231)
          ·
            refine ⟨14268456196127658884631347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512304130751772589754231 14268456196127658884631347)
            ·
              refine ⟨21402684294191488326947021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268456196127658884631347 21402684294191488326947021)
              ·
                refine ⟨8026006610321808122605133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21402684294191488326947021 8026006610321808122605133)
                ·
                  refine ⟨3009752478870678045976925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8026006610321808122605133 3009752478870678045976925)
                  ·
                    refine ⟨1128657179576504267241347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009752478870678045976925 1128657179576504267241347)
                    ·
                      rfl

theorem cell22_3297078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3297078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297078 prefixEnd_3297078 := by exact prefixLift 3297078
  have htrace : WordTrace (prefixWord ++ tailWord_3297078) baseStart_3297078 baseEnd_3297078 := by
    simpa [prefixWord, tailWord_3297078, baseEnd_3297078] using wordTrace_append hprefix tailTrace_3297078
  have hstable : (prefixWord ++ tailWord_3297078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297078).length < 2 ^ (prefixWord ++ tailWord_3297078).sum := by decide
  have hdescent : baseEnd_3297078 < baseStart_3297078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297091 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 5]
def baseStart_3297091 : Nat := 118140960795 + 3297091 * 2 ^ 59
def prefixEnd_3297091 : Nat := 4983230072969 + 3 ^ 40 * 3297091 * 2
def baseEnd_3297091 : Nat := 376220543247392188888769

theorem tailTrace_3297091 : CollatzResearch.WordTrace tailWord_3297091 prefixEnd_3297091 376220543247392188888769 := by
  unfold tailWord_3297091
  simp only [CollatzResearch.WordTrace]
  refine ⟨120254788098209880157363127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80169858732139920104908751 120254788098209880157363127)
  ·
    refine ⟨180382182147314820236044691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120254788098209880157363127 180382182147314820236044691)
    ·
      refine ⟨270573273220972230354067037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180382182147314820236044691 270573273220972230354067037)
      ·
        refine ⟨101464977457864586382775139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270573273220972230354067037 101464977457864586382775139)
        ·
          refine ⟨152197466186796879574162709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101464977457864586382775139 152197466186796879574162709)
          ·
            refine ⟨7134256227506103730038877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152197466186796879574162709 7134256227506103730038877)
            ·
              refine ⟨2675346085314788898764579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7134256227506103730038877 2675346085314788898764579)
              ·
                refine ⟨4013019127972183348146869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675346085314788898764579 4013019127972183348146869)
                ·
                  refine ⟨376220543247392188888769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013019127972183348146869 376220543247392188888769)
                  ·
                    rfl

theorem cell22_3297091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 5].length) (baseStart_3297091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297091 prefixEnd_3297091 := by exact prefixLift 3297091
  have htrace : WordTrace (prefixWord ++ tailWord_3297091) baseStart_3297091 baseEnd_3297091 := by
    simpa [prefixWord, tailWord_3297091, baseEnd_3297091] using wordTrace_append hprefix tailTrace_3297091
  have hstable : (prefixWord ++ tailWord_3297091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297091).length < 2 ^ (prefixWord ++ tailWord_3297091).sum := by decide
  have hdescent : baseEnd_3297091 < baseStart_3297091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297142 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3297142 : Nat := 118140960795 + 3297142 * 2 ^ 59
def prefixEnd_3297142 : Nat := 4983230072969 + 3 ^ 40 * 3297142 * 2
def baseEnd_3297142 : Nat := 376226362694809811213717

theorem tailTrace_3297142 : CollatzResearch.WordTrace tailWord_3297142 prefixEnd_3297142 376226362694809811213717 := by
  unfold tailWord_3297142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516040513814069741716855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80171098814016743911646453 7516040513814069741716855)
  ·
    refine ⟨11274060770721104612575283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7516040513814069741716855 11274060770721104612575283)
    ·
      refine ⟨16911091156081656918862925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11274060770721104612575283 16911091156081656918862925)
      ·
        refine ⟨6341659183530621344573597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16911091156081656918862925 6341659183530621344573597)
        ·
          refine ⟨2378122193823983004215099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6341659183530621344573597 2378122193823983004215099)
          ·
            refine ⟨3567183290735974506322649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378122193823983004215099 3567183290735974506322649)
            ·
              refine ⟨2675387468051980879741987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567183290735974506322649 2675387468051980879741987)
              ·
                refine ⟨4013081202077971319612981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675387468051980879741987 4013081202077971319612981)
                ·
                  refine ⟨376226362694809811213717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013081202077971319612981 376226362694809811213717)
                  ·
                    rfl

theorem cell22_3297142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3297142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297142 prefixEnd_3297142 := by exact prefixLift 3297142
  have htrace : WordTrace (prefixWord ++ tailWord_3297142) baseStart_3297142 baseEnd_3297142 := by
    simpa [prefixWord, tailWord_3297142, baseEnd_3297142] using wordTrace_append hprefix tailTrace_3297142
  have hstable : (prefixWord ++ tailWord_3297142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297142).length < 2 ^ (prefixWord ++ tailWord_3297142).sum := by decide
  have hdescent : baseEnd_3297142 < baseStart_3297142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297149 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3297149 : Nat := 118140960795 + 3297149 * 2 ^ 59
def prefixEnd_3297149 : Nat := 4983230072969 + 3 ^ 40 * 3297149 * 2
def baseEnd_3297149 : Nat := 1128681484327483748716129

theorem tailTrace_3297149 : CollatzResearch.WordTrace tailWord_3297149 prefixEnd_3297149 1128681484327483748716129 := by
  unfold tailWord_3297149
  simp only [CollatzResearch.WordTrace]
  refine ⟨120256903531999756062974501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80171269021333170708649667 120256903531999756062974501)
  ·
    refine ⟨22548169412249954261807719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120256903531999756062974501 22548169412249954261807719)
    ·
      refine ⟨33822254118374931392711579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22548169412249954261807719 33822254118374931392711579)
      ·
        refine ⟨50733381177562397089067369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33822254118374931392711579 50733381177562397089067369)
        ·
          refine ⟨38050035883171797816800527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50733381177562397089067369 38050035883171797816800527)
          ·
            refine ⟨57075053824757696725200791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38050035883171797816800527 57075053824757696725200791)
            ·
              refine ⟨85612580737136545087801187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57075053824757696725200791 85612580737136545087801187)
              ·
                refine ⟨128418871105704817631701781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85612580737136545087801187 128418871105704817631701781)
                ·
                  refine ⟨6019634583079913326486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128418871105704817631701781 6019634583079913326486021)
                  ·
                    refine ⟨1128681484327483748716129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019634583079913326486021 1128681484327483748716129)
                    ·
                      rfl

theorem cell22_3297149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3297149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297149 prefixEnd_3297149 := by exact prefixLift 3297149
  have htrace : WordTrace (prefixWord ++ tailWord_3297149) baseStart_3297149 baseEnd_3297149 := by
    simpa [prefixWord, tailWord_3297149, baseEnd_3297149] using wordTrace_append hprefix tailTrace_3297149
  have hstable : (prefixWord ++ tailWord_3297149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297149).length < 2 ^ (prefixWord ++ tailWord_3297149).sum := by decide
  have hdescent : baseEnd_3297149 < baseStart_3297149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297185 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3297185 : Nat := 118140960795 + 3297185 * 2 ^ 59
def prefixEnd_3297185 : Nat := 4983230072969 + 3 ^ 40 * 3297185 * 2
def baseEnd_3297185 : Nat := 1128693807863191654816019

theorem tailTrace_3297185 : CollatzResearch.WordTrace tailWord_3297185 prefixEnd_3297185 1128693807863191654816019 := by
  unfold tailWord_3297185
  simp only [CollatzResearch.WordTrace]
  refine ⟨120258216559869334211285009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80172144373246222807523339 120258216559869334211285009)
  ·
    refine ⟨90193662419902000658463757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120258216559869334211285009 90193662419902000658463757)
    ·
      refine ⟨33822623407463250246923909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90193662419902000658463757 33822623407463250246923909)
      ·
        refine ⟨6341741888899359421298233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33822623407463250246923909 6341741888899359421298233)
        ·
          refine ⟨4756306416674519565973675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6341741888899359421298233 4756306416674519565973675)
          ·
            refine ⟨7134459625011779348960513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756306416674519565973675 7134459625011779348960513)
            ·
              refine ⟨5350844718758834511720385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134459625011779348960513 5350844718758834511720385)
              ·
                refine ⟨4013133539069125883790289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350844718758834511720385 4013133539069125883790289)
                ·
                  refine ⟨3009850154301844412842717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013133539069125883790289 3009850154301844412842717)
                  ·
                    refine ⟨1128693807863191654816019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009850154301844412842717 1128693807863191654816019)
                    ·
                      rfl

theorem cell22_3297185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3297185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297185 prefixEnd_3297185 := by exact prefixLift 3297185
  have htrace : WordTrace (prefixWord ++ tailWord_3297185) baseStart_3297185 baseEnd_3297185 := by
    simpa [prefixWord, tailWord_3297185, baseEnd_3297185] using wordTrace_append hprefix tailTrace_3297185
  have hstable : (prefixWord ++ tailWord_3297185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297185).length < 2 ^ (prefixWord ++ tailWord_3297185).sum := by decide
  have hdescent : baseEnd_3297185 < baseStart_3297185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297213 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_3297213 : Nat := 118140960795 + 3297213 * 2 ^ 59
def prefixEnd_3297213 : Nat := 4983230072969 + 3 ^ 40 * 3297213 * 2
def baseEnd_3297213 : Nat := 1128703392835408915115933

theorem tailTrace_3297213 : CollatzResearch.WordTrace tailWord_3297213 prefixEnd_3297213 1128703392835408915115933 := by
  unfold tailWord_3297213
  simp only [CollatzResearch.WordTrace]
  refine ⟨120259237803767894993304293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80172825202511929995536195 120259237803767894993304293)
  ·
    refine ⟨22548607088206480311244555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120259237803767894993304293 22548607088206480311244555)
    ·
      refine ⟨33822910632309720466866833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22548607088206480311244555 33822910632309720466866833)
      ·
        refine ⟨25367182974232290350150125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33822910632309720466866833 25367182974232290350150125)
        ·
          refine ⟨9512693615337108881306297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25367182974232290350150125 9512693615337108881306297)
          ·
            refine ⟨7134520211502831660979723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9512693615337108881306297 7134520211502831660979723)
            ·
              refine ⟨10701780317254247491469585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134520211502831660979723 10701780317254247491469585)
              ·
                refine ⟨8026335237940685618602189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10701780317254247491469585 8026335237940685618602189)
                ·
                  refine ⟨3009875714227757106975821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8026335237940685618602189 3009875714227757106975821)
                  ·
                    refine ⟨1128703392835408915115933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009875714227757106975821 1128703392835408915115933)
                    ·
                      rfl

theorem cell22_3297213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_3297213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297213 prefixEnd_3297213 := by exact prefixLift 3297213
  have htrace : WordTrace (prefixWord ++ tailWord_3297213) baseStart_3297213 baseEnd_3297213 := by
    simpa [prefixWord, tailWord_3297213, baseEnd_3297213] using wordTrace_append hprefix tailTrace_3297213
  have hstable : (prefixWord ++ tailWord_3297213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297213).length < 2 ^ (prefixWord ++ tailWord_3297213).sum := by decide
  have hdescent : baseEnd_3297213 < baseStart_3297213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297230 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3297230 : Nat := 118140960795 + 3297230 * 2 ^ 59
def prefixEnd_3297230 : Nat := 4983230072969 + 3 ^ 40 * 3297230 * 2
def baseEnd_3297230 : Nat := 1128709212282826537440881

theorem tailTrace_3297230 : CollatzResearch.WordTrace tailWord_3297230 prefixEnd_3297230 1128709212282826537440881 := by
  unfold tailWord_3297230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032482230588288362084143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80173238563137537931115429 15032482230588288362084143)
  ·
    refine ⟨22548723345882432543126215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15032482230588288362084143 22548723345882432543126215)
    ·
      refine ⟨33823085018823648814689323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22548723345882432543126215 33823085018823648814689323)
      ·
        refine ⟨50734627528235473222033985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33823085018823648814689323 50734627528235473222033985)
        ·
          refine ⟨38050970646176604916525489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50734627528235473222033985 38050970646176604916525489)
          ·
            refine ⟨28538227984632453687394117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38050970646176604916525489 28538227984632453687394117)
            ·
              refine ⟨5350917747118585066386397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28538227984632453687394117 5350917747118585066386397)
              ·
                refine ⟨2006594155169469399894899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5350917747118585066386397 2006594155169469399894899)
                ·
                  refine ⟨3009891232754204099842349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006594155169469399894899 3009891232754204099842349)
                  ·
                    refine ⟨1128709212282826537440881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3009891232754204099842349 1128709212282826537440881)
                    ·
                      rfl

theorem cell22_3297230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3297230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297230 prefixEnd_3297230 := by exact prefixLift 3297230
  have htrace : WordTrace (prefixWord ++ tailWord_3297230) baseStart_3297230 baseEnd_3297230 := by
    simpa [prefixWord, tailWord_3297230, baseEnd_3297230] using wordTrace_append hprefix tailTrace_3297230
  have hstable : (prefixWord ++ tailWord_3297230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297230).length < 2 ^ (prefixWord ++ tailWord_3297230).sum := by decide
  have hdescent : baseEnd_3297230 < baseStart_3297230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297273 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_3297273 : Nat := 118140960795 + 3297273 * 2 ^ 59
def prefixEnd_3297273 : Nat := 4983230072969 + 3 ^ 40 * 3297273 * 2
def baseEnd_3297273 : Nat := 1128723932061588758615749

theorem tailTrace_3297273 : CollatzResearch.WordTrace tailWord_3297273 prefixEnd_3297273 1128723932061588758615749 := by
  unfold tailWord_3297273
  simp only [CollatzResearch.WordTrace]
  refine ⟨120261426183550525240488473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80174284122367016826992315 120261426183550525240488473)
  ·
    refine ⟨90196069637662893930366355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120261426183550525240488473 90196069637662893930366355)
    ·
      refine ⟨135294104456494340895549533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90196069637662893930366355 135294104456494340895549533)
      ·
        refine ⟨50735289171185377835831075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135294104456494340895549533 50735289171185377835831075)
        ·
          refine ⟨76102933756778066753746613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50735289171185377835831075 76102933756778066753746613)
          ·
            refine ⟨7134650039697943758163745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76102933756778066753746613 7134650039697943758163745)
            ·
              refine ⟨5350987529773457818622809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134650039697943758163745 5350987529773457818622809)
              ·
                refine ⟨4013240647330093363967107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5350987529773457818622809 4013240647330093363967107)
                ·
                  refine ⟨6019860970995140045950661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013240647330093363967107 6019860970995140045950661)
                  ·
                    refine ⟨1128723932061588758615749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019860970995140045950661 1128723932061588758615749)
                    ·
                      rfl

theorem cell22_3297273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_3297273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297273 prefixEnd_3297273 := by exact prefixLift 3297273
  have htrace : WordTrace (prefixWord ++ tailWord_3297273) baseStart_3297273 baseEnd_3297273 := by
    simpa [prefixWord, tailWord_3297273, baseEnd_3297273] using wordTrace_append hprefix tailTrace_3297273
  have hstable : (prefixWord ++ tailWord_3297273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297273).length < 2 ^ (prefixWord ++ tailWord_3297273).sum := by decide
  have hdescent : baseEnd_3297273 < baseStart_3297273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297299 : List Nat := [1, 1, 1, 2, 1, 4, 12]
def baseStart_3297299 : Nat := 118140960795 + 3297299 * 2 ^ 59
def prefixEnd_3297299 : Nat := 4983230072969 + 3 ^ 40 * 3297299 * 2
def baseEnd_3297299 : Nat := 41804919718256791017247

theorem tailTrace_3297299 : CollatzResearch.WordTrace tailWord_3297299 prefixEnd_3297299 41804919718256791017247 := by
  unfold tailWord_3297299
  simp only [CollatzResearch.WordTrace]
  refine ⟨120262374481456331680934951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80174916320970887787289967 120262374481456331680934951)
  ·
    refine ⟨180393561722184497521402427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120262374481456331680934951 180393561722184497521402427)
    ·
      refine ⟨270590342583276746282103641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180393561722184497521402427 270590342583276746282103641)
      ·
        refine ⟨202942756937457559711577731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270590342583276746282103641 202942756937457559711577731)
        ·
          refine ⟨304414135406186339567366597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202942756937457559711577731 304414135406186339567366597)
          ·
            refine ⟨57077650388659938668881237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304414135406186339567366597 57077650388659938668881237)
            ·
              refine ⟨41804919718256791017247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57077650388659938668881237 41804919718256791017247)
              ·
                rfl

theorem cell22_3297299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 12].length) (baseStart_3297299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297299 prefixEnd_3297299 := by exact prefixLift 3297299
  have htrace : WordTrace (prefixWord ++ tailWord_3297299) baseStart_3297299 baseEnd_3297299 := by
    simpa [prefixWord, tailWord_3297299, baseEnd_3297299] using wordTrace_append hprefix tailTrace_3297299
  have hstable : (prefixWord ++ tailWord_3297299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297299).length < 2 ^ (prefixWord ++ tailWord_3297299).sum := by decide
  have hdescent : baseEnd_3297299 < baseStart_3297299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297376 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_3297376 : Nat := 118140960795 + 3297376 * 2 ^ 59
def prefixEnd_3297376 : Nat := 4983230072969 + 3 ^ 40 * 3297376 * 2
def baseEnd_3297376 : Nat := 1128759191066530823290433

theorem tailTrace_3297376 : CollatzResearch.WordTrace tailWord_3297376 prefixEnd_3297376 1128759191066530823290433 := by
  unfold tailWord_3297376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132591451088686915743991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80176788601451582554325321 60132591451088686915743991)
  ·
    refine ⟨90198887176633030373615987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60132591451088686915743991 90198887176633030373615987)
    ·
      refine ⟨135298330764949545560423981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90198887176633030373615987 135298330764949545560423981)
      ·
        refine ⟨50736874036856079585158993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135298330764949545560423981 50736874036856079585158993)
        ·
          refine ⟨38052655527642059688869245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50736874036856079585158993 38052655527642059688869245)
          ·
            refine ⟨14269745822865772383325967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38052655527642059688869245 14269745822865772383325967)
            ·
              refine ⟨21404618734298658574988951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269745822865772383325967 21404618734298658574988951)
              ·
                refine ⟨32106928101447987862483427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21404618734298658574988951 32106928101447987862483427)
                ·
                  refine ⟨48160392152171981793725141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32106928101447987862483427 48160392152171981793725141)
                  ·
                    refine ⟨1128759191066530823290433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48160392152171981793725141 1128759191066530823290433)
                    ·
                      rfl

theorem cell22_3297376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_3297376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297376 prefixEnd_3297376 := by exact prefixLift 3297376
  have htrace : WordTrace (prefixWord ++ tailWord_3297376) baseStart_3297376 baseEnd_3297376 := by
    simpa [prefixWord, tailWord_3297376, baseEnd_3297376] using wordTrace_append hprefix tailTrace_3297376
  have hstable : (prefixWord ++ tailWord_3297376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297376).length < 2 ^ (prefixWord ++ tailWord_3297376).sum := by decide
  have hdescent : baseEnd_3297376 < baseStart_3297376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297442 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3297442 : Nat := 118140960795 + 3297442 * 2 ^ 59
def prefixEnd_3297442 : Nat := 4983230072969 + 3 ^ 40 * 3297442 * 2
def baseEnd_3297442 : Nat := 1128781784215328651140231

theorem tailTrace_3297442 : CollatzResearch.WordTrace tailWord_3297442 prefixEnd_3297442 1128781784215328651140231 := by
  unfold tailWord_3297442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066897529984566775847645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80178393413292178068927053 30066897529984566775847645)
  ·
    refine ⟨11275086573744212540942867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30066897529984566775847645 11275086573744212540942867)
    ·
      refine ⟨16912629860616318811414301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275086573744212540942867 16912629860616318811414301)
      ·
        refine ⟨6342236197731119554280363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16912629860616318811414301 6342236197731119554280363)
        ·
          refine ⟨9513354296596679331420545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342236197731119554280363 9513354296596679331420545)
          ·
            refine ⟨7135015722447509498565409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9513354296596679331420545 7135015722447509498565409)
            ·
              refine ⟨5351261791835632123924057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135015722447509498565409 5351261791835632123924057)
              ·
                refine ⟨4013446343876724092943043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351261791835632123924057 4013446343876724092943043)
                ·
                  refine ⟨6020169515815086139414565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013446343876724092943043 6020169515815086139414565)
                  ·
                    refine ⟨1128781784215328651140231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020169515815086139414565 1128781784215328651140231)
                    ·
                      rfl

theorem cell22_3297442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3297442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297442 prefixEnd_3297442 := by exact prefixLift 3297442
  have htrace : WordTrace (prefixWord ++ tailWord_3297442) baseStart_3297442 baseEnd_3297442 := by
    simpa [prefixWord, tailWord_3297442, baseEnd_3297442] using wordTrace_append hprefix tailTrace_3297442
  have hstable : (prefixWord ++ tailWord_3297442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297442).length < 2 ^ (prefixWord ++ tailWord_3297442).sum := by decide
  have hdescent : baseEnd_3297442 < baseStart_3297442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297474 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3297474 : Nat := 118140960795 + 3297474 * 2 ^ 59
def prefixEnd_3297474 : Nat := 4983230072969 + 3 ^ 40 * 3297474 * 2
def baseEnd_3297474 : Nat := 376264246156430411446711

theorem tailTrace_3297474 : CollatzResearch.WordTrace tailWord_3297474 prefixEnd_3297474 376264246156430411446711 := by
  unfold tailWord_3297474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067189313955584142138869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80179171503881557712370317 30067189313955584142138869)
  ·
    refine ⟨2818798998183336013325519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30067189313955584142138869 2818798998183336013325519)
    ·
      refine ⟨4228198497275004019988279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818798998183336013325519 4228198497275004019988279)
      ·
        refine ⟨6342297745912506029982419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228198497275004019988279 6342297745912506029982419)
        ·
          refine ⟨9513446618868759044973629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342297745912506029982419 9513446618868759044973629)
          ·
            refine ⟨3567542482075784641865111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9513446618868759044973629 3567542482075784641865111)
            ·
              refine ⟨5351313723113676962797667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567542482075784641865111 5351313723113676962797667)
              ·
                refine ⟨8026970584670515444196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351313723113676962797667 8026970584670515444196501)
                ·
                  refine ⟨376264246156430411446711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8026970584670515444196501 376264246156430411446711)
                  ·
                    rfl

theorem cell22_3297474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3297474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297474 prefixEnd_3297474 := by exact prefixLift 3297474
  have htrace : WordTrace (prefixWord ++ tailWord_3297474) baseStart_3297474 baseEnd_3297474 := by
    simpa [prefixWord, tailWord_3297474, baseEnd_3297474] using wordTrace_append hprefix tailTrace_3297474
  have hstable : (prefixWord ++ tailWord_3297474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297474).length < 2 ^ (prefixWord ++ tailWord_3297474).sum := by decide
  have hdescent : baseEnd_3297474 < baseStart_3297474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297530 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_3297530 : Nat := 118140960795 + 3297530 * 2 ^ 59
def prefixEnd_3297530 : Nat := 4983230072969 + 3 ^ 40 * 3297530 * 2
def baseEnd_3297530 : Nat := 376270636137908584979987

theorem tailTrace_3297530 : CollatzResearch.WordTrace tailWord_3297530 prefixEnd_3297530 376270636137908584979987 := by
  unfold tailWord_3297530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067699935904864533148511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80180533162412972088396029 30067699935904864533148511)
  ·
    refine ⟨45101549903857296799722767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30067699935904864533148511 45101549903857296799722767)
    ·
      refine ⟨67652324855785945199584151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45101549903857296799722767 67652324855785945199584151)
      ·
        refine ⟨101478487283678917799376227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67652324855785945199584151 101478487283678917799376227)
        ·
          refine ⟨152217730925518376699064341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101478487283678917799376227 152217730925518376699064341)
          ·
            refine ⟨7135206137133673907768641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152217730925518376699064341 7135206137133673907768641)
            ·
              refine ⟨5351404602850255430826481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135206137133673907768641 5351404602850255430826481)
              ·
                refine ⟨4013553452137691573119861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351404602850255430826481 4013553452137691573119861)
                ·
                  refine ⟨376270636137908584979987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013553452137691573119861 376270636137908584979987)
                  ·
                    rfl

theorem cell22_3297530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_3297530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297530 prefixEnd_3297530 := by exact prefixLift 3297530
  have htrace : WordTrace (prefixWord ++ tailWord_3297530) baseStart_3297530 baseEnd_3297530 := by
    simpa [prefixWord, tailWord_3297530, baseEnd_3297530] using wordTrace_append hprefix tailTrace_3297530
  have hstable : (prefixWord ++ tailWord_3297530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297530).length < 2 ^ (prefixWord ++ tailWord_3297530).sum := by decide
  have hdescent : baseEnd_3297530 < baseStart_3297530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297534 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3297534 : Nat := 118140960795 + 3297534 * 2 ^ 59
def prefixEnd_3297534 : Nat := 4983230072969 + 3 ^ 40 * 3297534 * 2
def baseEnd_3297534 : Nat := 1128813277695471077839949

theorem tailTrace_3297534 : CollatzResearch.WordTrace tailWord_3297534 prefixEnd_3297534 1128813277695471077839949 := by
  unfold tailWord_3297534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033868204450620851967457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80180630423736644543826437 15033868204450620851967457)
  ·
    refine ⟨11275401153337965638975593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15033868204450620851967457 11275401153337965638975593)
    ·
      refine ⟨8456550865003474229231695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11275401153337965638975593 8456550865003474229231695)
      ·
        refine ⟨12684826297505211343847543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456550865003474229231695 12684826297505211343847543)
        ·
          refine ⟨19027239446257817015771315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12684826297505211343847543 19027239446257817015771315)
          ·
            refine ⟨28540859169386725523656973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19027239446257817015771315 28540859169386725523656973)
            ·
              refine ⟨10702822188520022071371365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28540859169386725523656973 10702822188520022071371365)
              ·
                refine ⟨2006779160347504138382131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10702822188520022071371365 2006779160347504138382131)
                ·
                  refine ⟨3010168740521256207573197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006779160347504138382131 3010168740521256207573197)
                  ·
                    refine ⟨1128813277695471077839949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010168740521256207573197 1128813277695471077839949)
                    ·
                      rfl

theorem cell22_3297534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3297534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297534 prefixEnd_3297534 := by exact prefixLift 3297534
  have htrace : WordTrace (prefixWord ++ tailWord_3297534) baseStart_3297534 baseEnd_3297534 := by
    simpa [prefixWord, tailWord_3297534, baseEnd_3297534] using wordTrace_append hprefix tailTrace_3297534
  have hstable : (prefixWord ++ tailWord_3297534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297534).length < 2 ^ (prefixWord ++ tailWord_3297534).sum := by decide
  have hdescent : baseEnd_3297534 < baseStart_3297534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297560 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3297560 : Nat := 118140960795 + 3297560 * 2 ^ 59
def prefixEnd_3297560 : Nat := 4983230072969 + 3 ^ 40 * 3297560 * 2
def baseEnd_3297560 : Nat := 1128822178026815676689869

theorem tailTrace_3297560 : CollatzResearch.WordTrace tailWord_3297560 prefixEnd_3297560 1128822178026815676689869 := by
  unfold tailWord_3297560
  simp only [CollatzResearch.WordTrace]
  refine ⟨60135946966755386628093067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80181262622340515504124089 60135946966755386628093067)
  ·
    refine ⟨90203920450133079942139601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60135946966755386628093067 90203920450133079942139601)
    ·
      refine ⟨67652940337599809956604701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90203920450133079942139601 67652940337599809956604701)
      ·
        refine ⟨25369852626599928733726763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67652940337599809956604701 25369852626599928733726763)
        ·
          refine ⟨38054778939899893100590145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25369852626599928733726763 38054778939899893100590145)
          ·
            refine ⟨28541084204924919825442609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38054778939899893100590145 28541084204924919825442609)
            ·
              refine ⟨21405813153693689869081957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28541084204924919825442609 21405813153693689869081957)
              ·
                refine ⟨4013589966317566850452867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21405813153693689869081957 4013589966317566850452867)
                ·
                  refine ⟨6020384949476350275679301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013589966317566850452867 6020384949476350275679301)
                  ·
                    refine ⟨1128822178026815676689869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020384949476350275679301 1128822178026815676689869)
                    ·
                      rfl

theorem cell22_3297560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3297560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297560 prefixEnd_3297560 := by exact prefixLift 3297560
  have htrace : WordTrace (prefixWord ++ tailWord_3297560) baseStart_3297560 baseEnd_3297560 := by
    simpa [prefixWord, tailWord_3297560, baseEnd_3297560] using wordTrace_append hprefix tailTrace_3297560
  have hstable : (prefixWord ++ tailWord_3297560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297560).length < 2 ^ (prefixWord ++ tailWord_3297560).sum := by decide
  have hdescent : baseEnd_3297560 < baseStart_3297560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297581 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3297581 : Nat := 118140960795 + 3297581 * 2 ^ 59
def prefixEnd_3297581 : Nat := 4983230072969 + 3 ^ 40 * 3297581 * 2
def baseEnd_3297581 : Nat := 376276455585326207304935

theorem tailTrace_3297581 : CollatzResearch.WordTrace tailWord_3297581 prefixEnd_3297581 376276455585326207304935 := by
  unfold tailWord_3297581
  simp only [CollatzResearch.WordTrace]
  refine ⟨120272659866434693842700597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80181773244289795895133731 120272659866434693842700597)
  ·
    refine ⟨11275561862478252547753181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120272659866434693842700597 11275561862478252547753181)
    ·
      refine ⟨4228335698429344705407443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11275561862478252547753181 4228335698429344705407443)
      ·
        refine ⟨6342503547644017058111165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228335698429344705407443 6342503547644017058111165)
        ·
          refine ⟨2378438830366506396791687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342503547644017058111165 2378438830366506396791687)
          ·
            refine ⟨3567658245549759595187531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378438830366506396791687 3567658245549759595187531)
            ·
              refine ⟨5351487368324639392781297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567658245549759595187531 5351487368324639392781297)
              ·
                refine ⟨4013615526243479544585973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351487368324639392781297 4013615526243479544585973)
                ·
                  refine ⟨376276455585326207304935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013615526243479544585973 376276455585326207304935)
                  ·
                    rfl

theorem cell22_3297581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3297581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297581 prefixEnd_3297581 := by exact prefixLift 3297581
  have htrace : WordTrace (prefixWord ++ tailWord_3297581) baseStart_3297581 baseEnd_3297581 := by
    simpa [prefixWord, tailWord_3297581, baseEnd_3297581] using wordTrace_append hprefix tailTrace_3297581
  have hstable : (prefixWord ++ tailWord_3297581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297581).length < 2 ^ (prefixWord ++ tailWord_3297581).sum := by decide
  have hdescent : baseEnd_3297581 < baseStart_3297581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297620 : List Nat := [2, 4, 1, 1, 2, 3, 1, 8]
def baseStart_3297620 : Nat := 118140960795 + 3297620 * 2 ^ 59
def prefixEnd_3297620 : Nat := 4983230072969 + 3 ^ 40 * 3297620 * 2
def baseEnd_3297620 : Nat := 125426968583666168909965

theorem tailTrace_3297620 : CollatzResearch.WordTrace tailWord_3297620 prefixEnd_3297620 125426968583666168909965 := by
  unfold tailWord_3297620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60137041156646701751685157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80182721542195602335580209 60137041156646701751685157)
  ·
    refine ⟨11275695216871256578440967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60137041156646701751685157 11275695216871256578440967)
    ·
      refine ⟨16913542825306884867661451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275695216871256578440967 16913542825306884867661451)
      ·
        refine ⟨25370314237960327301492177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16913542825306884867661451 25370314237960327301492177)
        ·
          refine ⟨19027735678470245476119133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25370314237960327301492177 19027735678470245476119133)
          ·
            refine ⟨7135400879426342053544675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19027735678470245476119133 7135400879426342053544675)
            ·
              refine ⟨10703101319139513080317013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135400879426342053544675 10703101319139513080317013)
              ·
                refine ⟨125426968583666168909965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10703101319139513080317013 125426968583666168909965)
                ·
                  rfl

theorem cell22_3297620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_3297620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297620 prefixEnd_3297620 := by exact prefixLift 3297620
  have htrace : WordTrace (prefixWord ++ tailWord_3297620) baseStart_3297620 baseEnd_3297620 := by
    simpa [prefixWord, tailWord_3297620, baseEnd_3297620] using wordTrace_append hprefix tailTrace_3297620
  have hstable : (prefixWord ++ tailWord_3297620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297620).length < 2 ^ (prefixWord ++ tailWord_3297620).sum := by decide
  have hdescent : baseEnd_3297620 < baseStart_3297620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297633 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3297633 : Nat := 118140960795 + 3297633 * 2 ^ 59
def prefixEnd_3297633 : Nat := 4983230072969 + 3 ^ 40 * 3297633 * 2
def baseEnd_3297633 : Nat := 1128847167418667819614645

theorem tailTrace_3297633 : CollatzResearch.WordTrace tailWord_3297633 prefixEnd_3297633 1128847167418667819614645 := by
  unfold tailWord_3297633
  simp only [CollatzResearch.WordTrace]
  refine ⟨120274556462246306723593553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80183037641497537815729035 120274556462246306723593553)
  ·
    refine ⟨90205917346684730042695165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120274556462246306723593553 90205917346684730042695165)
    ·
      refine ⟨33827219005006773766010687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90205917346684730042695165 33827219005006773766010687)
      ·
        refine ⟨50740828507510160649016031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33827219005006773766010687 50740828507510160649016031)
        ·
          refine ⟨76111242761265240973524047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50740828507510160649016031 76111242761265240973524047)
          ·
            refine ⟨114166864141897861460286071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76111242761265240973524047 114166864141897861460286071)
            ·
              refine ⟨171250296212846792190429107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114166864141897861460286071 171250296212846792190429107)
              ·
                refine ⟨256875444319270188285643661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171250296212846792190429107 256875444319270188285643661)
                ·
                  refine ⟨96328291619726320607116373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256875444319270188285643661 96328291619726320607116373)
                  ·
                    refine ⟨1128847167418667819614645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96328291619726320607116373 1128847167418667819614645)
                    ·
                      rfl

theorem cell22_3297633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3297633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297633 prefixEnd_3297633 := by exact prefixLift 3297633
  have htrace : WordTrace (prefixWord ++ tailWord_3297633) baseStart_3297633 baseEnd_3297633 := by
    simpa [prefixWord, tailWord_3297633, baseEnd_3297633] using wordTrace_append hprefix tailTrace_3297633
  have hstable : (prefixWord ++ tailWord_3297633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297633).length < 2 ^ (prefixWord ++ tailWord_3297633).sum := by decide
  have hdescent : baseEnd_3297633 < baseStart_3297633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297654 : List Nat := [5, 1, 1, 4, 1, 1, 2, 7]
def baseStart_3297654 : Nat := 118140960795 + 3297654 * 2 ^ 59
def prefixEnd_3297654 : Nat := 4983230072969 + 3 ^ 40 * 3297654 * 2
def baseEnd_3297654 : Nat := 125428261794203418315509

theorem tailTrace_3297654 : CollatzResearch.WordTrace tailWord_3297654 prefixEnd_3297654 125428261794203418315509 := by
  unfold tailWord_3297654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517207649698139206881751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80183548263446818206738677 7517207649698139206881751)
  ·
    refine ⟨11275811474547208810322627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7517207649698139206881751 11275811474547208810322627)
    ·
      refine ⟨16913717211820813215483941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275811474547208810322627 16913717211820813215483941)
      ·
        refine ⟨3171321977216402477903239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16913717211820813215483941 3171321977216402477903239)
        ·
          refine ⟨4756982965824603716854859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171321977216402477903239 4756982965824603716854859)
          ·
            refine ⟨7135474448736905575282289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756982965824603716854859 7135474448736905575282289)
            ·
              refine ⟨5351605836552679181461717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135474448736905575282289 5351605836552679181461717)
              ·
                refine ⟨125428261794203418315509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5351605836552679181461717 125428261794203418315509)
                ·
                  rfl

theorem cell22_3297654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_3297654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297654 prefixEnd_3297654 := by exact prefixLift 3297654
  have htrace : WordTrace (prefixWord ++ tailWord_3297654) baseStart_3297654 baseEnd_3297654 := by
    simpa [prefixWord, tailWord_3297654, baseEnd_3297654] using wordTrace_append hprefix tailTrace_3297654
  have hstable : (prefixWord ++ tailWord_3297654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297654).length < 2 ^ (prefixWord ++ tailWord_3297654).sum := by decide
  have hdescent : baseEnd_3297654 < baseStart_3297654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297703 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3297703 : Nat := 118140960795 + 3297703 * 2 ^ 59
def prefixEnd_3297703 : Nat := 4983230072969 + 3 ^ 40 * 3297703 * 2
def baseEnd_3297703 : Nat := 1128871129849210970364431

theorem tailTrace_3297703 : CollatzResearch.WordTrace tailWord_3297703 prefixEnd_3297703 1128871129849210970364431 := by
  unfold tailWord_3297703
  simp only [CollatzResearch.WordTrace]
  refine ⟨120277109571992708678641763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80184739714661805785761175 120277109571992708678641763)
  ·
    refine ⟨180415664357989063017962645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120277109571992708678641763 180415664357989063017962645)
    ·
      refine ⟨8456984266780737328966999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180415664357989063017962645 8456984266780737328966999)
      ·
        refine ⟨12685476400171105993450499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456984266780737328966999 12685476400171105993450499)
        ·
          refine ⟨19028214600256658990175749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685476400171105993450499 19028214600256658990175749)
          ·
            refine ⟨3567790237548123560657953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19028214600256658990175749 3567790237548123560657953)
            ·
              refine ⟨2675842678161092670493465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567790237548123560657953 2675842678161092670493465)
              ·
                refine ⟨2006882008620819502870099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675842678161092670493465 2006882008620819502870099)
                ·
                  refine ⟨3010323012931229254305149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006882008620819502870099 3010323012931229254305149)
                  ·
                    refine ⟨1128871129849210970364431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010323012931229254305149 1128871129849210970364431)
                    ·
                      rfl

theorem cell22_3297703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3297703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297703 prefixEnd_3297703 := by exact prefixLift 3297703
  have htrace : WordTrace (prefixWord ++ tailWord_3297703) baseStart_3297703 baseEnd_3297703 := by
    simpa [prefixWord, tailWord_3297703, baseEnd_3297703] using wordTrace_append hprefix tailTrace_3297703
  have hstable : (prefixWord ++ tailWord_3297703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297703).length < 2 ^ (prefixWord ++ tailWord_3297703).sum := by decide
  have hdescent : baseEnd_3297703 < baseStart_3297703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297742 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3297742 : Nat := 118140960795 + 3297742 * 2 ^ 59
def prefixEnd_3297742 : Nat := 4983230072969 + 3 ^ 40 * 3297742 * 2
def baseEnd_3297742 : Nat := 1128884480346227868639311

theorem tailTrace_3297742 : CollatzResearch.WordTrace tailWord_3297742 prefixEnd_3297742 1128884480346227868639311 := by
  unfold tailWord_3297742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034816502356427292413935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80185688012567612226207653 15034816502356427292413935)
  ·
    refine ⟨22552224753534640938620903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034816502356427292413935 22552224753534640938620903)
    ·
      refine ⟨33828337130301961407931355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22552224753534640938620903 33828337130301961407931355)
      ·
        refine ⟨50742505695452942111897033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33828337130301961407931355 50742505695452942111897033)
        ·
          refine ⟨38056879271589706583922775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50742505695452942111897033 38056879271589706583922775)
          ·
            refine ⟨57085318907384559875884163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38056879271589706583922775 57085318907384559875884163)
            ·
              refine ⟨85627978361076839813826245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57085318907384559875884163 85627978361076839813826245)
              ·
                refine ⟨16055245942701907465092421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85627978361076839813826245 16055245942701907465092421)
                ·
                  refine ⟨3010358614256607649704829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16055245942701907465092421 3010358614256607649704829)
                  ·
                    refine ⟨1128884480346227868639311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010358614256607649704829 1128884480346227868639311)
                    ·
                      rfl

theorem cell22_3297742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3297742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297742 prefixEnd_3297742 := by exact prefixLift 3297742
  have htrace : WordTrace (prefixWord ++ tailWord_3297742) baseStart_3297742 baseEnd_3297742 := by
    simpa [prefixWord, tailWord_3297742, baseEnd_3297742] using wordTrace_append hprefix tailTrace_3297742
  have hstable : (prefixWord ++ tailWord_3297742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297742).length < 2 ^ (prefixWord ++ tailWord_3297742).sum := by decide
  have hdescent : baseEnd_3297742 < baseStart_3297742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297746 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3297746 : Nat := 118140960795 + 3297746 * 2 ^ 59
def prefixEnd_3297746 : Nat := 4983230072969 + 3 ^ 40 * 3297746 * 2
def baseEnd_3297746 : Nat := 1128885849627973191539299

theorem tailTrace_3297746 : CollatzResearch.WordTrace tailWord_3297746 prefixEnd_3297746 1128885849627973191539299 := by
  unfold tailWord_3297746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30069669477709231755614273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80185785273891284681638061 30069669477709231755614273)
  ·
    refine ⟨22552252108281923816710705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30069669477709231755614273 22552252108281923816710705)
    ·
      refine ⟨16914189081211442862533029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22552252108281923816710705 16914189081211442862533029)
      ·
        refine ⟨3171410452727145536724943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16914189081211442862533029 3171410452727145536724943)
        ·
          refine ⟨4757115679090718305087415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171410452727145536724943 4757115679090718305087415)
          ·
            refine ⟨7135673518636077457631123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757115679090718305087415 7135673518636077457631123)
            ·
              refine ⟨10703510277954116186446685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135673518636077457631123 10703510277954116186446685)
              ·
                refine ⟨4013816354232793569917507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10703510277954116186446685 4013816354232793569917507)
                ·
                  refine ⟨6020724531349190354876261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013816354232793569917507 6020724531349190354876261)
                  ·
                    refine ⟨1128885849627973191539299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020724531349190354876261 1128885849627973191539299)
                    ·
                      rfl

theorem cell22_3297746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3297746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297746 prefixEnd_3297746 := by exact prefixLift 3297746
  have htrace : WordTrace (prefixWord ++ tailWord_3297746) baseStart_3297746 baseEnd_3297746 := by
    simpa [prefixWord, tailWord_3297746, baseEnd_3297746] using wordTrace_append hprefix tailTrace_3297746
  have hstable : (prefixWord ++ tailWord_3297746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297746).length < 2 ^ (prefixWord ++ tailWord_3297746).sum := by decide
  have hdescent : baseEnd_3297746 < baseStart_3297746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297757 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3297757 : Nat := 118140960795 + 3297757 * 2 ^ 59
def prefixEnd_3297757 : Nat := 4983230072969 + 3 ^ 40 * 3297757 * 2
def baseEnd_3297757 : Nat := 1128889615152772829514265

theorem tailTrace_3297757 : CollatzResearch.WordTrace tailWord_3297757 prefixEnd_3297757 1128889615152772829514265 := by
  unfold tailWord_3297757
  simp only [CollatzResearch.WordTrace]
  refine ⟨120279079113797075901107525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80186052742531383934071683 120279079113797075901107525)
  ·
    refine ⟨22552327333836951731457661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120279079113797075901107525 22552327333836951731457661)
    ·
      refine ⟨8457122750188856899296623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22552327333836951731457661 8457122750188856899296623)
      ·
        refine ⟨12685684125283285348944935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457122750188856899296623 12685684125283285348944935)
        ·
          refine ⟨19028526187924928023417403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685684125283285348944935 19028526187924928023417403)
          ·
            refine ⟨28542789281887392035126105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19028526187924928023417403 28542789281887392035126105)
            ·
              refine ⟨21407091961415544026344579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28542789281887392035126105 21407091961415544026344579)
              ·
                refine ⟨32110637942123316039516869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21407091961415544026344579 32110637942123316039516869)
                ·
                  refine ⟨6020744614148121757409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32110637942123316039516869 6020744614148121757409413)
                  ·
                    refine ⟨1128889615152772829514265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020744614148121757409413 1128889615152772829514265)
                    ·
                      rfl

theorem cell22_3297757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3297757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297757 prefixEnd_3297757 := by exact prefixLift 3297757
  have htrace : WordTrace (prefixWord ++ tailWord_3297757) baseStart_3297757 baseEnd_3297757 := by
    simpa [prefixWord, tailWord_3297757, baseEnd_3297757] using wordTrace_append hprefix tailTrace_3297757
  have hstable : (prefixWord ++ tailWord_3297757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297757).length < 2 ^ (prefixWord ++ tailWord_3297757).sum := by decide
  have hdescent : baseEnd_3297757 < baseStart_3297757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297759 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 2, 3]
def baseStart_3297759 : Nat := 118140960795 + 3297759 * 2 ^ 59
def prefixEnd_3297759 : Nat := 4983230072969 + 3 ^ 40 * 3297759 * 2
def baseEnd_3297759 : Nat := 1128890299793645490964259

theorem tailTrace_3297759 : CollatzResearch.WordTrace tailWord_3297759 prefixEnd_3297759 1128890299793645490964259 := by
  unfold tailWord_3297759
  simp only [CollatzResearch.WordTrace]
  refine ⟨120279152059789830242680331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80186101373193220161786887 120279152059789830242680331)
  ·
    refine ⟨180418728089684745364020497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120279152059789830242680331 180418728089684745364020497)
    ·
      refine ⟨135314046067263559023015373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180418728089684745364020497 135314046067263559023015373)
      ·
        refine ⟨50742767275223834633630765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135314046067263559023015373 50742767275223834633630765)
        ·
          refine ⟨19028537728208937987611537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50742767275223834633630765 19028537728208937987611537)
          ·
            refine ⟨14271403296156703490708653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19028537728208937987611537 14271403296156703490708653)
            ·
              refine ⟨5351776236058763809015745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14271403296156703490708653 5351776236058763809015745)
              ·
                refine ⟨4013832177044072856761809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351776236058763809015745 4013832177044072856761809)
                ·
                  refine ⟨3010374132783054642571357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013832177044072856761809 3010374132783054642571357)
                  ·
                    refine ⟨1128890299793645490964259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010374132783054642571357 1128890299793645490964259)
                    ·
                      rfl

theorem cell22_3297759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_3297759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297759 prefixEnd_3297759 := by exact prefixLift 3297759
  have htrace : WordTrace (prefixWord ++ tailWord_3297759) baseStart_3297759 baseEnd_3297759 := by
    simpa [prefixWord, tailWord_3297759, baseEnd_3297759] using wordTrace_append hprefix tailTrace_3297759
  have hstable : (prefixWord ++ tailWord_3297759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297759).length < 2 ^ (prefixWord ++ tailWord_3297759).sum := by decide
  have hdescent : baseEnd_3297759 < baseStart_3297759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297785 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3297785 : Nat := 118140960795 + 3297785 * 2 ^ 59
def prefixEnd_3297785 : Nat := 4983230072969 + 3 ^ 40 * 3297785 * 2
def baseEnd_3297785 : Nat := 1128899200124990089814179

theorem tailTrace_3297785 : CollatzResearch.WordTrace tailWord_3297785 prefixEnd_3297785 1128899200124990089814179 := by
  unfold tailWord_3297785
  simp only [CollatzResearch.WordTrace]
  refine ⟨120280100357695636683126809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80186733571797091122084539 120280100357695636683126809)
  ·
    refine ⟨90210075268271727512345107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120280100357695636683126809 90210075268271727512345107)
    ·
      refine ⟨135315112902407591268517661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90210075268271727512345107 135315112902407591268517661)
      ·
        refine ⟨50743167338402846725694123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135315112902407591268517661 50743167338402846725694123)
        ·
          refine ⟨76114751007604270088541185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50743167338402846725694123 76114751007604270088541185)
          ·
            refine ⟨57086063255703202566405889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76114751007604270088541185 57086063255703202566405889)
            ·
              refine ⟨42814547441777401924804417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57086063255703202566405889 42814547441777401924804417)
              ·
                refine ⟨32110910581333051443603313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42814547441777401924804417 32110910581333051443603313)
                ·
                  refine ⟨24083182935999788582702485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32110910581333051443603313 24083182935999788582702485)
                  ·
                    refine ⟨1128899200124990089814179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24083182935999788582702485 1128899200124990089814179)
                    ·
                      rfl

theorem cell22_3297785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3297785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297785 prefixEnd_3297785 := by exact prefixLift 3297785
  have htrace : WordTrace (prefixWord ++ tailWord_3297785) baseStart_3297785 baseEnd_3297785 := by
    simpa [prefixWord, tailWord_3297785, baseEnd_3297785] using wordTrace_append hprefix tailTrace_3297785
  have hstable : (prefixWord ++ tailWord_3297785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297785).length < 2 ^ (prefixWord ++ tailWord_3297785).sum := by decide
  have hdescent : baseEnd_3297785 < baseStart_3297785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297821 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3297821 : Nat := 118140960795 + 3297821 * 2 ^ 59
def prefixEnd_3297821 : Nat := 4983230072969 + 3 ^ 40 * 3297821 * 2
def baseEnd_3297821 : Nat := 1128911523660697995914069

theorem tailTrace_3297821 : CollatzResearch.WordTrace tailWord_3297821 prefixEnd_3297821 1128911523660697995914069 := by
  unfold tailWord_3297821
  simp only [CollatzResearch.WordTrace]
  refine ⟨120281413385565214831437317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80187608923710143220958211 120281413385565214831437317)
  ·
    refine ⟨22552765009793477780894497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120281413385565214831437317 22552765009793477780894497)
    ·
      refine ⟨16914573757345108335670873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22552765009793477780894497 16914573757345108335670873)
      ·
        refine ⟨12685930318008831251753155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16914573757345108335670873 12685930318008831251753155)
        ·
          refine ⟨19028895477013246877629733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685930318008831251753155 19028895477013246877629733)
          ·
            refine ⟨3567917901939983789555575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19028895477013246877629733 3567917901939983789555575)
            ·
              refine ⟨5351876852909975684333363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567917901939983789555575 5351876852909975684333363)
              ·
                refine ⟨8027815279364963526500045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351876852909975684333363 8027815279364963526500045)
                ·
                  refine ⟨3010430729761861322437517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8027815279364963526500045 3010430729761861322437517)
                  ·
                    refine ⟨1128911523660697995914069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010430729761861322437517 1128911523660697995914069)
                    ·
                      rfl

theorem cell22_3297821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3297821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297821 prefixEnd_3297821 := by exact prefixLift 3297821
  have htrace : WordTrace (prefixWord ++ tailWord_3297821) baseStart_3297821 baseEnd_3297821 := by
    simpa [prefixWord, tailWord_3297821, baseEnd_3297821] using wordTrace_append hprefix tailTrace_3297821
  have hstable : (prefixWord ++ tailWord_3297821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297821).length < 2 ^ (prefixWord ++ tailWord_3297821).sum := by decide
  have hdescent : baseEnd_3297821 < baseStart_3297821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297834 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_3297834 : Nat := 118140960795 + 3297834 * 2 ^ 59
def prefixEnd_3297834 : Nat := 4983230072969 + 3 ^ 40 * 3297834 * 2
def baseEnd_3297834 : Nat := 376305324608790098446343

theorem tailTrace_3297834 : CollatzResearch.WordTrace tailWord_3297834 prefixEnd_3297834 376305324608790098446343 := by
  unfold tailWord_3297834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070471883629529512915139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80187925023012078701107037 30070471883629529512915139)
  ·
    refine ⟨45105707825444294269372709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070471883629529512915139 45105707825444294269372709)
    ·
      refine ⟨8457320217270805175507383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45105707825444294269372709 8457320217270805175507383)
      ·
        refine ⟨12685980325906207763261075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8457320217270805175507383 12685980325906207763261075)
        ·
          refine ⟨19028970488859311644891613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685980325906207763261075 19028970488859311644891613)
          ·
            refine ⟨7135863933322241866834355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19028970488859311644891613 7135863933322241866834355)
            ·
              refine ⟨10703795899983362800251533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135863933322241866834355 10703795899983362800251533)
              ·
                refine ⟨4013923462493761050094325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10703795899983362800251533 4013923462493761050094325)
                ·
                  refine ⟨376305324608790098446343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013923462493761050094325 376305324608790098446343)
                  ·
                    rfl

theorem cell22_3297834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_3297834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297834 prefixEnd_3297834 := by exact prefixLift 3297834
  have htrace : WordTrace (prefixWord ++ tailWord_3297834) baseStart_3297834 baseEnd_3297834 := by
    simpa [prefixWord, tailWord_3297834, baseEnd_3297834] using wordTrace_append hprefix tailTrace_3297834
  have hstable : (prefixWord ++ tailWord_3297834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297834).length < 2 ^ (prefixWord ++ tailWord_3297834).sum := by decide
  have hdescent : baseEnd_3297834 < baseStart_3297834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297847 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3297847 : Nat := 118140960795 + 3297847 * 2 ^ 59
def prefixEnd_3297847 : Nat := 4983230072969 + 3 ^ 40 * 3297847 * 2
def baseEnd_3297847 : Nat := 1128920423992042594763989

theorem tailTrace_3297847 : CollatzResearch.WordTrace tailWord_3297847 prefixEnd_3297847 1128920423992042594763989 := by
  unfold tailWord_3297847
  simp only [CollatzResearch.WordTrace]
  refine ⟨120282361683471021271883795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80188241122314014181255863 120282361683471021271883795)
  ·
    refine ⟨180423542525206531907825693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120282361683471021271883795 180423542525206531907825693)
    ·
      refine ⟨67658828446952449465434635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180423542525206531907825693 67658828446952449465434635)
      ·
        refine ⟨101488242670428674198151953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67658828446952449465434635 101488242670428674198151953)
        ·
          refine ⟨76116182002821505648613965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101488242670428674198151953 76116182002821505648613965)
          ·
            refine ⟨28543568251058064618230237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76116182002821505648613965 28543568251058064618230237)
            ·
              refine ⟨10703838094146774231836339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28543568251058064618230237 10703838094146774231836339)
              ·
                refine ⟨16055757141220161347754509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703838094146774231836339 16055757141220161347754509)
                ·
                  refine ⟨6020908927957560505407941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16055757141220161347754509 6020908927957560505407941)
                  ·
                    refine ⟨1128920423992042594763989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020908927957560505407941 1128920423992042594763989)
                    ·
                      rfl

theorem cell22_3297847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3297847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297847 prefixEnd_3297847 := by exact prefixLift 3297847
  have htrace : WordTrace (prefixWord ++ tailWord_3297847) baseStart_3297847 baseEnd_3297847 := by
    simpa [prefixWord, tailWord_3297847, baseEnd_3297847] using wordTrace_append hprefix tailTrace_3297847
  have hstable : (prefixWord ++ tailWord_3297847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297847).length < 2 ^ (prefixWord ++ tailWord_3297847).sum := by decide
  have hdescent : baseEnd_3297847 < baseStart_3297847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297879 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 4]
def baseStart_3297879 : Nat := 118140960795 + 3297879 * 2 ^ 59
def prefixEnd_3297879 : Nat := 4983230072969 + 3 ^ 40 * 3297879 * 2
def baseEnd_3297879 : Nat := 376310459415335059321297

theorem tailTrace_3297879 : CollatzResearch.WordTrace tailWord_3297879 prefixEnd_3297879 376310459415335059321297 := by
  unfold tailWord_3297879
  simp only [CollatzResearch.WordTrace]
  refine ⟨120283528819355090737048691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80189019212903393824699127 120283528819355090737048691)
  ·
    refine ⟨180425293229032636105573037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120283528819355090737048691 180425293229032636105573037)
    ·
      refine ⟨67659484960887238539589889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180425293229032636105573037 67659484960887238539589889)
      ·
        refine ⟨50744613720665428904692417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67659484960887238539589889 50744613720665428904692417)
        ·
          refine ⟨38058460290499071678519313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50744613720665428904692417 38058460290499071678519313)
          ·
            refine ⟨28543845217874303758889485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38058460290499071678519313 28543845217874303758889485)
            ·
              refine ⟨10703941956702863909583557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28543845217874303758889485 10703941956702863909583557)
              ·
                refine ⟨2006989116881786983046917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10703941956702863909583557 2006989116881786983046917)
                ·
                  refine ⟨376310459415335059321297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006989116881786983046917 376310459415335059321297)
                  ·
                    rfl

theorem cell22_3297879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 4].length) (baseStart_3297879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297879 prefixEnd_3297879 := by exact prefixLift 3297879
  have htrace : WordTrace (prefixWord ++ tailWord_3297879) baseStart_3297879 baseEnd_3297879 := by
    simpa [prefixWord, tailWord_3297879, baseEnd_3297879] using wordTrace_append hprefix tailTrace_3297879
  have hstable : (prefixWord ++ tailWord_3297879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297879).length < 2 ^ (prefixWord ++ tailWord_3297879).sum := by decide
  have hdescent : baseEnd_3297879 < baseStart_3297879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3297892 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3297892 : Nat := 118140960795 + 3297892 * 2 ^ 59
def prefixEnd_3297892 : Nat := 4983230072969 + 3 ^ 40 * 3297892 * 2
def baseEnd_3297892 : Nat := 1128935828411677477388851

theorem tailTrace_3297892 : CollatzResearch.WordTrace tailWord_3297892 prefixEnd_3297892 1128935828411677477388851 := by
  unfold tailWord_3297892
  simp only [CollatzResearch.WordTrace]
  refine ⟨60142001484153996978635965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80189335312205329304847953 60142001484153996978635965)
  ·
    refine ⟨22553250556557748866988487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60142001484153996978635965 22553250556557748866988487)
    ·
      refine ⟨33829875834836623300482731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22553250556557748866988487 33829875834836623300482731)
      ·
        refine ⟨50744813752254934950724097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33829875834836623300482731 50744813752254934950724097)
        ·
          refine ⟨38058610314191201213043073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50744813752254934950724097 38058610314191201213043073)
          ·
            refine ⟨28543957735643400909782305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38058610314191201213043073 28543957735643400909782305)
            ·
              refine ⟨21407968301732550682336729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28543957735643400909782305 21407968301732550682336729)
              ·
                refine ⟨16055976226299413011752547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21407968301732550682336729 16055976226299413011752547)
                ·
                  refine ⟨24083964339449119517628821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16055976226299413011752547 24083964339449119517628821)
                  ·
                    refine ⟨1128935828411677477388851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24083964339449119517628821 1128935828411677477388851)
                    ·
                      rfl

theorem cell22_3297892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3297892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3297892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3297892 prefixEnd_3297892 := by exact prefixLift 3297892
  have htrace : WordTrace (prefixWord ++ tailWord_3297892) baseStart_3297892 baseEnd_3297892 := by
    simpa [prefixWord, tailWord_3297892, baseEnd_3297892] using wordTrace_append hprefix tailTrace_3297892
  have hstable : (prefixWord ++ tailWord_3297892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3297892).length < 2 ^ (prefixWord ++ tailWord_3297892).sum := by decide
  have hdescent : baseEnd_3297892 < baseStart_3297892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3297892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298076 : List Nat := [2, 2, 3, 1, 1, 4, 3, 6]
def baseStart_3298076 : Nat := 118140960795 + 3298076 * 2 ^ 59
def prefixEnd_3298076 : Nat := 4983230072969 + 3 ^ 40 * 3298076 * 2
def baseEnd_3298076 : Nat := 125444312819106925643143

theorem tailTrace_3298076 : CollatzResearch.WordTrace tailWord_3298076 prefixEnd_3298076 125444312819106925643143 := by
  unfold tailWord_3298076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60145356999820696690985041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80193809333094262254646721 60145356999820696690985041)
  ·
    refine ⟨45109017749865522518238781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60145356999820696690985041 45109017749865522518238781)
    ·
      refine ⟨16915881656199570944339543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45109017749865522518238781 16915881656199570944339543)
      ·
        refine ⟨25373822484299356416509315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16915881656199570944339543 25373822484299356416509315)
        ·
          refine ⟨38060733726449034624763973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25373822484299356416509315 38060733726449034624763973)
          ·
            refine ⟨7136387573709193992143245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38060733726449034624763973 7136387573709193992143245)
            ·
              refine ⟨2676145340140947747053717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7136387573709193992143245 2676145340140947747053717)
              ·
                refine ⟨125444312819106925643143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2676145340140947747053717 125444312819106925643143)
                ·
                  rfl

theorem cell22_3298076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_3298076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298076 prefixEnd_3298076 := by exact prefixLift 3298076
  have htrace : WordTrace (prefixWord ++ tailWord_3298076) baseStart_3298076 baseEnd_3298076 := by
    simpa [prefixWord, tailWord_3298076, baseEnd_3298076] using wordTrace_append hprefix tailTrace_3298076
  have hstable : (prefixWord ++ tailWord_3298076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298076).length < 2 ^ (prefixWord ++ tailWord_3298076).sum := by decide
  have hdescent : baseEnd_3298076 < baseStart_3298076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298093 : List Nat := [1, 5, 3, 2, 1, 1, 9]
def baseStart_3298093 : Nat := 118140960795 + 3298093 * 2 ^ 59
def prefixEnd_3298093 : Nat := 4983230072969 + 3 ^ 40 * 3298093 * 2
def baseEnd_3298093 : Nat := 41814986474791850115305

theorem tailTrace_3298093 : CollatzResearch.WordTrace tailWord_3298093 prefixEnd_3298093 41814986474791850115305 := by
  unfold tailWord_3298093
  simp only [CollatzResearch.WordTrace]
  refine ⟨120291334040579805285338933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80194222693719870190225955 120291334040579805285338933)
  ·
    refine ⟨11277312566304356745500525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120291334040579805285338933 11277312566304356745500525)
    ·
      refine ⟨4228992212364133779562697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11277312566304356745500525 4228992212364133779562697)
      ·
        refine ⟨3171744159273100334672023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228992212364133779562697 3171744159273100334672023)
        ·
          refine ⟨4757616238909650502008035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171744159273100334672023 4757616238909650502008035)
          ·
            refine ⟨7136424358364475753012053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757616238909650502008035 7136424358364475753012053)
            ·
              refine ⟨41814986474791850115305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7136424358364475753012053 41814986474791850115305)
              ·
                rfl

theorem cell22_3298093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 9].length) (baseStart_3298093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298093 prefixEnd_3298093 := by exact prefixLift 3298093
  have htrace : WordTrace (prefixWord ++ tailWord_3298093) baseStart_3298093 baseEnd_3298093 := by
    simpa [prefixWord, tailWord_3298093, baseEnd_3298093] using wordTrace_append hprefix tailTrace_3298093
  have hstable : (prefixWord ++ tailWord_3298093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298093).length < 2 ^ (prefixWord ++ tailWord_3298093).sum := by decide
  have hdescent : baseEnd_3298093 < baseStart_3298093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298104 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_3298104 : Nat := 118140960795 + 3298104 * 2 ^ 59
def prefixEnd_3298104 : Nat := 4983230072969 + 3 ^ 40 * 3298104 * 2
def baseEnd_3298104 : Nat := 376336133448059863696067

theorem tailTrace_3298104 : CollatzResearch.WordTrace tailWord_3298104 prefixEnd_3298104 376336133448059863696067 := by
  unfold tailWord_3298104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60145867621769977081994683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80194490162359969442659577 60145867621769977081994683)
  ·
    refine ⟨90218801432654965622992025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60145867621769977081994683 90218801432654965622992025)
    ·
      refine ⟨67664101074491224217244019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90218801432654965622992025 67664101074491224217244019)
      ·
        refine ⟨101496151611736836325866029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67664101074491224217244019 101496151611736836325866029)
        ·
          refine ⟨38061056854401313622199761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101496151611736836325866029 38061056854401313622199761)
          ·
            refine ⟨28545792640800985216649821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38061056854401313622199761 28545792640800985216649821)
            ·
              refine ⟨10704672240300369456243683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28545792640800985216649821 10704672240300369456243683)
              ·
                refine ⟨16057008360450554184365525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704672240300369456243683 16057008360450554184365525)
                ·
                  refine ⟨376336133448059863696067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16057008360450554184365525 376336133448059863696067)
                  ·
                    rfl

theorem cell22_3298104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_3298104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298104 prefixEnd_3298104 := by exact prefixLift 3298104
  have htrace : WordTrace (prefixWord ++ tailWord_3298104) baseStart_3298104 baseEnd_3298104 := by
    simpa [prefixWord, tailWord_3298104, baseEnd_3298104] using wordTrace_append hprefix tailTrace_3298104
  have hstable : (prefixWord ++ tailWord_3298104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298104).length < 2 ^ (prefixWord ++ tailWord_3298104).sum := by decide
  have hdescent : baseEnd_3298104 < baseStart_3298104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298149 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3298149 : Nat := 118140960795 + 3298149 * 2 ^ 59
def prefixEnd_3298149 : Nat := 4983230072969 + 3 ^ 40 * 3298149 * 2
def baseEnd_3298149 : Nat := 376341268254604824571021

theorem tailTrace_3298149 : CollatzResearch.WordTrace tailWord_3298149 prefixEnd_3298149 376341268254604824571021 := by
  unfold tailWord_3298149
  simp only [CollatzResearch.WordTrace]
  refine ⟨120293376528376926849377501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80195584352251284566251667 120293376528376926849377501)
  ·
    refine ⟨45110016198141347568516563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120293376528376926849377501 45110016198141347568516563)
    ·
      refine ⟨67665024297212021352774845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45110016198141347568516563 67665024297212021352774845)
      ·
        refine ⟨25374384111454508007290567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67665024297212021352774845 25374384111454508007290567)
        ·
          refine ⟨38061576167181762010935851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25374384111454508007290567 38061576167181762010935851)
          ·
            refine ⟨57092364250772643016403777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38061576167181762010935851 57092364250772643016403777)
            ·
              refine ⟨42819273188079482262302833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57092364250772643016403777 42819273188079482262302833)
              ·
                refine ⟨32114454891059611696727125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42819273188079482262302833 32114454891059611696727125)
                ·
                  refine ⟨376341268254604824571021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32114454891059611696727125 376341268254604824571021)
                  ·
                    rfl

theorem cell22_3298149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3298149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298149 prefixEnd_3298149 := by exact prefixLift 3298149
  have htrace : WordTrace (prefixWord ++ tailWord_3298149) baseStart_3298149 baseEnd_3298149 := by
    simpa [prefixWord, tailWord_3298149, baseEnd_3298149] using wordTrace_append hprefix tailTrace_3298149
  have hstable : (prefixWord ++ tailWord_3298149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298149).length < 2 ^ (prefixWord ++ tailWord_3298149).sum := by decide
  have hdescent : baseEnd_3298149 < baseStart_3298149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298253 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3298253 : Nat := 118140960795 + 3298253 * 2 ^ 59
def prefixEnd_3298253 : Nat := 4983230072969 + 3 ^ 40 * 3298253 * 2
def baseEnd_3298253 : Nat := 1129059406089192869112745

theorem tailTrace_3298253 : CollatzResearch.WordTrace tailWord_3298253 prefixEnd_3298253 1129059406089192869112745 := by
  unfold tailWord_3298253
  simp only [CollatzResearch.WordTrace]
  refine ⟨120297169720000152611163413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80198113146666768407442275 120297169720000152611163413)
  ·
    refine ⟨5638929830625007153648285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120297169720000152611163413 5638929830625007153648285)
    ·
      refine ⟨2114598686484377682618107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5638929830625007153648285 2114598686484377682618107)
      ·
        refine ⟨3171898029726566523927161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114598686484377682618107 3171898029726566523927161)
        ·
          refine ⟨2378923522294924892945371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171898029726566523927161 2378923522294924892945371)
          ·
            refine ⟨3568385283442387339418057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378923522294924892945371 3568385283442387339418057)
            ·
              refine ⟨2676288962581790504563543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568385283442387339418057 2676288962581790504563543)
              ·
                refine ⟨4014433443872685756845315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676288962581790504563543 4014433443872685756845315)
                ·
                  refine ⟨6021650165809028635267973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014433443872685756845315 6021650165809028635267973)
                  ·
                    refine ⟨1129059406089192869112745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021650165809028635267973 1129059406089192869112745)
                    ·
                      rfl

theorem cell22_3298253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3298253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298253 prefixEnd_3298253 := by exact prefixLift 3298253
  have htrace : WordTrace (prefixWord ++ tailWord_3298253) baseStart_3298253 baseEnd_3298253 := by
    simpa [prefixWord, tailWord_3298253, baseEnd_3298253] using wordTrace_append hprefix tailTrace_3298253
  have hstable : (prefixWord ++ tailWord_3298253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298253).length < 2 ^ (prefixWord ++ tailWord_3298253).sum := by decide
  have hdescent : baseEnd_3298253 < baseStart_3298253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298277 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_3298277 : Nat := 118140960795 + 3298277 * 2 ^ 59
def prefixEnd_3298277 : Nat := 4983230072969 + 3 ^ 40 * 3298277 * 2
def baseEnd_3298277 : Nat := 1129067621779664806512671

theorem tailTrace_3298277 : CollatzResearch.WordTrace tailWord_3298277 prefixEnd_3298277 1129067621779664806512671 := by
  unfold tailWord_3298277
  simp only [CollatzResearch.WordTrace]
  refine ⟨120298045071913204710037085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80198696714608803140024723 120298045071913204710037085)
  ·
    refine ⟨45111766901967451766263907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120298045071913204710037085 45111766901967451766263907)
    ·
      refine ⟨67667650352951177649395861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45111766901967451766263907 67667650352951177649395861)
      ·
        refine ⟨3171921110294586452315431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67667650352951177649395861 3171921110294586452315431)
        ·
          refine ⟨4757881665441879678473147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171921110294586452315431 4757881665441879678473147)
          ·
            refine ⟨7136822498162819517709721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757881665441879678473147 7136822498162819517709721)
            ·
              refine ⟨5352616873622114638282291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136822498162819517709721 5352616873622114638282291)
              ·
                refine ⟨8028925310433171957423437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352616873622114638282291 8028925310433171957423437)
                ·
                  refine ⟨3010846991412439484033789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8028925310433171957423437 3010846991412439484033789)
                  ·
                    refine ⟨1129067621779664806512671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010846991412439484033789 1129067621779664806512671)
                    ·
                      rfl

theorem cell22_3298277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_3298277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298277 prefixEnd_3298277 := by exact prefixLift 3298277
  have htrace : WordTrace (prefixWord ++ tailWord_3298277) baseStart_3298277 baseEnd_3298277 := by
    simpa [prefixWord, tailWord_3298277, baseEnd_3298277] using wordTrace_append hprefix tailTrace_3298277
  have hstable : (prefixWord ++ tailWord_3298277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298277).length < 2 ^ (prefixWord ++ tailWord_3298277).sum := by decide
  have hdescent : baseEnd_3298277 < baseStart_3298277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298365 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3298365 : Nat := 118140960795 + 3298365 * 2 ^ 59
def prefixEnd_3298365 : Nat := 4983230072969 + 3 ^ 40 * 3298365 * 2
def baseEnd_3298365 : Nat := 1129097745978061910312401

theorem tailTrace_3298365 : CollatzResearch.WordTrace tailWord_3298365 prefixEnd_3298365 1129097745978061910312401 := by
  unfold tailWord_3298365
  simp only [CollatzResearch.WordTrace]
  refine ⟨120301254695594395739240549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80200836463729597159493699 120301254695594395739240549)
  ·
    refine ⟨22556485255423949201107603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120301254695594395739240549 22556485255423949201107603)
    ·
      refine ⟨33834727883135923801661405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22556485255423949201107603 33834727883135923801661405)
      ·
        refine ⟨12688022956175971425623027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33834727883135923801661405 12688022956175971425623027)
        ·
          refine ⟨19032034434263957138434541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688022956175971425623027 19032034434263957138434541)
          ·
            refine ⟨7137012912848983926912953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19032034434263957138434541 7137012912848983926912953)
            ·
              refine ⟨5352759684636737945184715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137012912848983926912953 5352759684636737945184715)
              ·
                refine ⟨8029139526955106917777073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352759684636737945184715 8029139526955106917777073)
                ·
                  refine ⟨6021854645216330188332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8029139526955106917777073 6021854645216330188332805)
                  ·
                    refine ⟨1129097745978061910312401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021854645216330188332805 1129097745978061910312401)
                    ·
                      rfl

theorem cell22_3298365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3298365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298365 prefixEnd_3298365 := by exact prefixLift 3298365
  have htrace : WordTrace (prefixWord ++ tailWord_3298365) baseStart_3298365 baseEnd_3298365 := by
    simpa [prefixWord, tailWord_3298365, baseEnd_3298365] using wordTrace_append hprefix tailTrace_3298365
  have hstable : (prefixWord ++ tailWord_3298365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298365).length < 2 ^ (prefixWord ++ tailWord_3298365).sum := by decide
  have hdescent : baseEnd_3298365 < baseStart_3298365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298397 : List Nat := [1, 4, 4, 1, 2, 2, 1, 7]
def baseStart_3298397 : Nat := 118140960795 + 3298397 * 2 ^ 59
def prefixEnd_3298397 : Nat := 4983230072969 + 3 ^ 40 * 3298397 * 2
def baseEnd_3298397 : Nat := 125456522248002721501367

theorem tailTrace_3298397 : CollatzResearch.WordTrace tailWord_3298397 prefixEnd_3298397 125456522248002721501367 := by
  unfold tailWord_3298397
  simp only [CollatzResearch.WordTrace]
  refine ⟨120302421831478465204405445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80201614554318976802936963 120302421831478465204405445)
  ·
    refine ⟨22556704093402212225826021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120302421831478465204405445 22556704093402212225826021)
    ·
      refine ⟨4229382017512914792342379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22556704093402212225826021 4229382017512914792342379)
      ·
        refine ⟨6344073026269372188513569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229382017512914792342379 6344073026269372188513569)
        ·
          refine ⟨4758054769702029141385177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344073026269372188513569 4758054769702029141385177)
          ·
            refine ⟨3568541077276521856038883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758054769702029141385177 3568541077276521856038883)
            ·
              refine ⟨5352811615914782784058325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568541077276521856038883 5352811615914782784058325)
              ·
                refine ⟨125456522248002721501367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5352811615914782784058325 125456522248002721501367)
                ·
                  rfl

theorem cell22_3298397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 7].length) (baseStart_3298397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298397 prefixEnd_3298397 := by exact prefixLift 3298397
  have htrace : WordTrace (prefixWord ++ tailWord_3298397) baseStart_3298397 baseEnd_3298397 := by
    simpa [prefixWord, tailWord_3298397, baseEnd_3298397] using wordTrace_append hprefix tailTrace_3298397
  have hstable : (prefixWord ++ tailWord_3298397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298397).length < 2 ^ (prefixWord ++ tailWord_3298397).sum := by decide
  have hdescent : baseEnd_3298397 < baseStart_3298397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298483 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_3298483 : Nat := 118140960795 + 3298483 * 2 ^ 59
def prefixEnd_3298483 : Nat := 4983230072969 + 3 ^ 40 * 3298483 * 2
def baseEnd_3298483 : Nat := 1129138139789548935862039

theorem tailTrace_3298483 : CollatzResearch.WordTrace tailWord_3298483 prefixEnd_3298483 1129138139789548935862039 := by
  unfold tailWord_3298483
  simp only [CollatzResearch.WordTrace]
  refine ⟨120305558509166901892036103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80203705672777934594690735 120305558509166901892036103)
  ·
    refine ⟨180458337763750352838054155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120305558509166901892036103 180458337763750352838054155)
    ·
      refine ⟨270687506645625529257081233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180458337763750352838054155 270687506645625529257081233)
      ·
        refine ⟨203015629984219146942810925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270687506645625529257081233 203015629984219146942810925)
        ·
          refine ⟨76130861244082180103554097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203015629984219146942810925 76130861244082180103554097)
          ·
            refine ⟨57098145933061635077665573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76130861244082180103554097 57098145933061635077665573)
            ·
              refine ⟨10705902362449056577062295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57098145933061635077665573 10705902362449056577062295)
              ·
                refine ⟨16058853543673584865593443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705902362449056577062295 16058853543673584865593443)
                ·
                  refine ⟨24088280315510377298390165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16058853543673584865593443 24088280315510377298390165)
                  ·
                    refine ⟨1129138139789548935862039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24088280315510377298390165 1129138139789548935862039)
                    ·
                      rfl

theorem cell22_3298483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_3298483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298483 prefixEnd_3298483 := by exact prefixLift 3298483
  have htrace : WordTrace (prefixWord ++ tailWord_3298483) baseStart_3298483 baseEnd_3298483 := by
    simpa [prefixWord, tailWord_3298483, baseEnd_3298483] using wordTrace_append hprefix tailTrace_3298483
  have hstable : (prefixWord ++ tailWord_3298483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298483).length < 2 ^ (prefixWord ++ tailWord_3298483).sum := by decide
  have hdescent : baseEnd_3298483 < baseStart_3298483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298622 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3298622 : Nat := 118140960795 + 3298622 * 2 ^ 59
def prefixEnd_3298622 : Nat := 4983230072969 + 3 ^ 40 * 3298622 * 2
def baseEnd_3298622 : Nat := 376395240776732968878871

theorem tailTrace_3298622 : CollatzResearch.WordTrace tailWord_3298622 prefixEnd_3298622 376395240776732968878871 := by
  unfold tailWord_3298622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038828531957916078918265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80207085503775552420897413 15038828531957916078918265)
  ·
    refine ⟨11279121398968437059188699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15038828531957916078918265 11279121398968437059188699)
    ·
      refine ⟨16918682098452655588783049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279121398968437059188699 16918682098452655588783049)
      ·
        refine ⟨12689011573839491691587287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16918682098452655588783049 12689011573839491691587287)
        ·
          refine ⟨19033517360759237537380931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689011573839491691587287 19033517360759237537380931)
          ·
            refine ⟨28550276041138856306071397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033517360759237537380931 28550276041138856306071397)
            ·
              refine ⟨5353176757713535557388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28550276041138856306071397 5353176757713535557388387)
              ·
                refine ⟨8029765136570303336082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353176757713535557388387 8029765136570303336082581)
                ·
                  refine ⟨376395240776732968878871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8029765136570303336082581 376395240776732968878871)
                  ·
                    rfl

theorem cell22_3298622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3298622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298622 prefixEnd_3298622 := by exact prefixLift 3298622
  have htrace : WordTrace (prefixWord ++ tailWord_3298622) baseStart_3298622 baseEnd_3298622 := by
    simpa [prefixWord, tailWord_3298622, baseEnd_3298622] using wordTrace_append hprefix tailTrace_3298622
  have hstable : (prefixWord ++ tailWord_3298622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298622).length < 2 ^ (prefixWord ++ tailWord_3298622).sum := by decide
  have hdescent : baseEnd_3298622 < baseStart_3298622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298727 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3298727 : Nat := 118140960795 + 3298727 * 2 ^ 59
def prefixEnd_3298727 : Nat := 4983230072969 + 3 ^ 40 * 3298727 * 2
def baseEnd_3298727 : Nat := 1129221665976013632761291

theorem tailTrace_3298727 : CollatzResearch.WordTrace tailWord_3298727 prefixEnd_3298727 1129221665976013632761291 := by
  unfold tailWord_3298727
  simp only [CollatzResearch.WordTrace]
  refine ⟨120314457920282931563918435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80209638613521954375945623 120314457920282931563918435)
  ·
    refine ⟨180471686880424397345877653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120314457920282931563918435 180471686880424397345877653)
    ·
      refine ⟨8459610322519893625588015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180471686880424397345877653 8459610322519893625588015)
      ·
        refine ⟨12689415483779840438382023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459610322519893625588015 12689415483779840438382023)
        ·
          refine ⟨19034123225669760657573035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689415483779840438382023 19034123225669760657573035)
          ·
            refine ⟨28551184838504640986359553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19034123225669760657573035 28551184838504640986359553)
            ·
              refine ⟨21413388628878480739769665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28551184838504640986359553 21413388628878480739769665)
              ·
                refine ⟨16060041471658860554827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21413388628878480739769665 16060041471658860554827249)
                ·
                  refine ⟨12045031103744145416120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060041471658860554827249 12045031103744145416120437)
                  ·
                    refine ⟨1129221665976013632761291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12045031103744145416120437 1129221665976013632761291)
                    ·
                      rfl

theorem cell22_3298727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3298727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298727 prefixEnd_3298727 := by exact prefixLift 3298727
  have htrace : WordTrace (prefixWord ++ tailWord_3298727) baseStart_3298727 baseEnd_3298727 := by
    simpa [prefixWord, tailWord_3298727, baseEnd_3298727] using wordTrace_append hprefix tailTrace_3298727
  have hstable : (prefixWord ++ tailWord_3298727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298727).length < 2 ^ (prefixWord ++ tailWord_3298727).sum := by decide
  have hdescent : baseEnd_3298727 < baseStart_3298727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298733 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3298733 : Nat := 118140960795 + 3298733 * 2 ^ 59
def prefixEnd_3298733 : Nat := 4983230072969 + 3 ^ 40 * 3298733 * 2
def baseEnd_3298733 : Nat := 1129223719898631617111273

theorem tailTrace_3298733 : CollatzResearch.WordTrace tailWord_3298733 prefixEnd_3298733 1129223719898631617111273 := by
  unfold tailWord_3298733
  simp only [CollatzResearch.WordTrace]
  refine ⟨120314676758261194588636853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80209784505507463059091235 120314676758261194588636853)
  ·
    refine ⟨11279500946086986992684705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120314676758261194588636853 11279500946086986992684705)
    ·
      refine ⟨8459625709565240244513529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11279500946086986992684705 8459625709565240244513529)
      ·
        refine ⟨6344719282173930183385147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8459625709565240244513529 6344719282173930183385147)
        ·
          refine ⟨9517078923260895275077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344719282173930183385147 9517078923260895275077721)
          ·
            refine ⟨7137809192445671456308291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517078923260895275077721 7137809192445671456308291)
            ·
              refine ⟨10706713788668507184462437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137809192445671456308291 10706713788668507184462437)
              ·
                refine ⟨2007508835375345097086707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10706713788668507184462437 2007508835375345097086707)
                ·
                  refine ⟨3011263253063017645630061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007508835375345097086707 3011263253063017645630061)
                  ·
                    refine ⟨1129223719898631617111273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011263253063017645630061 1129223719898631617111273)
                    ·
                      rfl

theorem cell22_3298733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3298733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298733 prefixEnd_3298733 := by exact prefixLift 3298733
  have htrace : WordTrace (prefixWord ++ tailWord_3298733) baseStart_3298733 baseEnd_3298733 := by
    simpa [prefixWord, tailWord_3298733, baseEnd_3298733] using wordTrace_append hprefix tailTrace_3298733
  have hstable : (prefixWord ++ tailWord_3298733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298733).length < 2 ^ (prefixWord ++ tailWord_3298733).sum := by decide
  have hdescent : baseEnd_3298733 < baseStart_3298733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298806 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3298806 : Nat := 118140960795 + 3298806 * 2 ^ 59
def prefixEnd_3298806 : Nat := 4983230072969 + 3 ^ 40 * 3298806 * 2
def baseEnd_3298806 : Nat := 1129248709290483760036049

theorem tailTrace_3298806 : CollatzResearch.WordTrace tailWord_3298806 prefixEnd_3298806 1129248709290483760036049 := by
  unfold tailWord_3298806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519833705437295503502767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80211559524664485370696181 7519833705437295503502767)
  ·
    refine ⟨11279750558155943255254151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7519833705437295503502767 11279750558155943255254151)
    ·
      refine ⟨16919625837233914882881227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279750558155943255254151 16919625837233914882881227)
      ·
        refine ⟨25379438755850872324321841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919625837233914882881227 25379438755850872324321841)
        ·
          refine ⟨19034579066888154243241381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25379438755850872324321841 19034579066888154243241381)
          ·
            refine ⟨3568983575041528920607759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19034579066888154243241381 3568983575041528920607759)
            ·
              refine ⟨5353475362562293380911639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568983575041528920607759 5353475362562293380911639)
              ·
                refine ⟨8030213043843440071367459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353475362562293380911639 8030213043843440071367459)
                ·
                  refine ⟨12045319565765160107051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8030213043843440071367459 12045319565765160107051189)
                  ·
                    refine ⟨1129248709290483760036049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12045319565765160107051189 1129248709290483760036049)
                    ·
                      rfl

theorem cell22_3298806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3298806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298806 prefixEnd_3298806 := by exact prefixLift 3298806
  have htrace : WordTrace (prefixWord ++ tailWord_3298806) baseStart_3298806 baseEnd_3298806 := by
    simpa [prefixWord, tailWord_3298806, baseEnd_3298806] using wordTrace_append hprefix tailTrace_3298806
  have hstable : (prefixWord ++ tailWord_3298806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298806).length < 2 ^ (prefixWord ++ tailWord_3298806).sum := by decide
  have hdescent : baseEnd_3298806 < baseStart_3298806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298836 : List Nat := [2, 4, 3, 1, 2, 2, 8]
def baseStart_3298836 : Nat := 118140960795 + 3298836 * 2 ^ 59
def prefixEnd_3298836 : Nat := 4983230072969 + 3 ^ 40 * 3298836 * 2
def baseEnd_3298836 : Nat := 41824406626058284510591

theorem tailTrace_3298836 : CollatzResearch.WordTrace tailWord_3298836 prefixEnd_3298836 41824406626058284510591 := by
  unfold tailWord_3298836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60159216738444021589818181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80212288984592028786424241 60159216738444021589818181)
  ·
    refine ⟨11279853138458254048090909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60159216738444021589818181 11279853138458254048090909)
    ·
      refine ⟨4229944926921845268034091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11279853138458254048090909 4229944926921845268034091)
      ·
        refine ⟨6344917390382767902051137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229944926921845268034091 6344917390382767902051137)
        ·
          refine ⟨4758688042787075926538353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344917390382767902051137 4758688042787075926538353)
          ·
            refine ⟨3569016032090306944903765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758688042787075926538353 3569016032090306944903765)
            ·
              refine ⟨41824406626058284510591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3569016032090306944903765 41824406626058284510591)
              ·
                rfl

theorem cell22_3298836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 8].length) (baseStart_3298836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298836 prefixEnd_3298836 := by exact prefixLift 3298836
  have htrace : WordTrace (prefixWord ++ tailWord_3298836) baseStart_3298836 baseEnd_3298836 := by
    simpa [prefixWord, tailWord_3298836, baseEnd_3298836] using wordTrace_append hprefix tailTrace_3298836
  have hstable : (prefixWord ++ tailWord_3298836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298836).length < 2 ^ (prefixWord ++ tailWord_3298836).sum := by decide
  have hdescent : baseEnd_3298836 < baseStart_3298836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298847 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 7]
def baseStart_3298847 : Nat := 118140960795 + 3298847 * 2 ^ 59
def prefixEnd_3298847 : Nat := 4983230072969 + 3 ^ 40 * 3298847 * 2
def baseEnd_3298847 : Nat := 376420914809457773253641

theorem tailTrace_3298847 : CollatzResearch.WordTrace tailWord_3298847 prefixEnd_3298847 376420914809457773253641 := by
  unfold tailWord_3298847
  simp only [CollatzResearch.WordTrace]
  refine ⟨120318834679848192058286795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80212556453232128038857863 120318834679848192058286795)
  ·
    refine ⟨180478252019772288087430193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120318834679848192058286795 180478252019772288087430193)
    ·
      refine ⟨135358689014829216065572645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180478252019772288087430193 135358689014829216065572645)
      ·
        refine ⟨25379754190280478012294871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135358689014829216065572645 25379754190280478012294871)
        ·
          refine ⟨38069631285420717018442307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25379754190280478012294871 38069631285420717018442307)
          ·
            refine ⟨57104446928131075527663461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38069631285420717018442307 57104446928131075527663461)
            ·
              refine ⟨10707083799024576661436899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57104446928131075527663461 10707083799024576661436899)
              ·
                refine ⟨16060625698536864992155349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707083799024576661436899 16060625698536864992155349)
                ·
                  refine ⟨376420914809457773253641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16060625698536864992155349 376420914809457773253641)
                  ·
                    rfl

theorem cell22_3298847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_3298847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298847 prefixEnd_3298847 := by exact prefixLift 3298847
  have htrace : WordTrace (prefixWord ++ tailWord_3298847) baseStart_3298847 baseEnd_3298847 := by
    simpa [prefixWord, tailWord_3298847, baseEnd_3298847] using wordTrace_append hprefix tailTrace_3298847
  have hstable : (prefixWord ++ tailWord_3298847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298847).length < 2 ^ (prefixWord ++ tailWord_3298847).sum := by decide
  have hdescent : baseEnd_3298847 < baseStart_3298847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298924 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_3298924 : Nat := 118140960795 + 3298924 * 2 ^ 59
def prefixEnd_3298924 : Nat := 4983230072969 + 3 ^ 40 * 3298924 * 2
def baseEnd_3298924 : Nat := 1129289103101970785585687

theorem tailTrace_3298924 : CollatzResearch.WordTrace tailWord_3298924 prefixEnd_3298924 1129289103101970785585687 := by
  unfold tailWord_3298924
  simp only [CollatzResearch.WordTrace]
  refine ⟨60160821550284617104419913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80214428733712822805893217 60160821550284617104419913)
  ·
    refine ⟨45120616162713462828314935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60160821550284617104419913 45120616162713462828314935)
    ·
      refine ⟨67680924244070194242472403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45120616162713462828314935 67680924244070194242472403)
      ·
        refine ⟨101521386366105291363708605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67680924244070194242472403 101521386366105291363708605)
        ·
          refine ⟨38070519887289484261390727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101521386366105291363708605 38070519887289484261390727)
          ·
            refine ⟨57105779830934226392086091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38070519887289484261390727 57105779830934226392086091)
            ·
              refine ⟨85658669746401339588129137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57105779830934226392086091 85658669746401339588129137)
              ·
                refine ⟨64244002309801004691096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85658669746401339588129137 64244002309801004691096853)
                ·
                  refine ⟨3011437608271922094895165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64244002309801004691096853 3011437608271922094895165)
                  ·
                    refine ⟨1129289103101970785585687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011437608271922094895165 1129289103101970785585687)
                    ·
                      rfl

theorem cell22_3298924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_3298924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298924 prefixEnd_3298924 := by exact prefixLift 3298924
  have htrace : WordTrace (prefixWord ++ tailWord_3298924) baseStart_3298924 baseEnd_3298924 := by
    simpa [prefixWord, tailWord_3298924, baseEnd_3298924] using wordTrace_append hprefix tailTrace_3298924
  have hstable : (prefixWord ++ tailWord_3298924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298924).length < 2 ^ (prefixWord ++ tailWord_3298924).sum := by decide
  have hdescent : baseEnd_3298924 < baseStart_3298924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298926 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_3298926 : Nat := 118140960795 + 3298926 * 2 ^ 59
def prefixEnd_3298926 : Nat := 4983230072969 + 3 ^ 40 * 3298926 * 2
def baseEnd_3298926 : Nat := 376429929247614482345227

theorem tailTrace_3298926 : CollatzResearch.WordTrace tailWord_3298926 prefixEnd_3298926 376429929247614482345227 := by
  unfold tailWord_3298926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040214505820248568801579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80214477364374659033608421 15040214505820248568801579)
  ·
    refine ⟨22560321758730372853202369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15040214505820248568801579 22560321758730372853202369)
    ·
      refine ⟨16920241319047779639901777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22560321758730372853202369 16920241319047779639901777)
      ·
        refine ⟨12690180989285834729926333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16920241319047779639901777 12690180989285834729926333)
        ·
          refine ⟨4758817870982188023722375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12690180989285834729926333 4758817870982188023722375)
          ·
            refine ⟨7138226806473282035583563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758817870982188023722375 7138226806473282035583563)
            ·
              refine ⟨10707340209709923053375345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138226806473282035583563 10707340209709923053375345)
              ·
                refine ⟨8030505157282442290031509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10707340209709923053375345 8030505157282442290031509)
                ·
                  refine ⟨376429929247614482345227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8030505157282442290031509 376429929247614482345227)
                  ·
                    rfl

theorem cell22_3298926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_3298926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298926 prefixEnd_3298926 := by exact prefixLift 3298926
  have htrace : WordTrace (prefixWord ++ tailWord_3298926) baseStart_3298926 baseEnd_3298926 := by
    simpa [prefixWord, tailWord_3298926, baseEnd_3298926] using wordTrace_append hprefix tailTrace_3298926
  have hstable : (prefixWord ++ tailWord_3298926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298926).length < 2 ^ (prefixWord ++ tailWord_3298926).sum := by decide
  have hdescent : baseEnd_3298926 < baseStart_3298926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298954 : List Nat := [3, 1, 2, 3, 2, 2, 9]
def baseStart_3298954 : Nat := 118140960795 + 3298954 * 2 ^ 59
def prefixEnd_3298954 : Nat := 4983230072969 + 3 ^ 40 * 3298954 * 2
def baseEnd_3298954 : Nat := 41825902693150396567985

theorem tailTrace_3298954 : CollatzResearch.WordTrace tailWord_3298954 prefixEnd_3298954 41825902693150396567985 := by
  unfold tailWord_3298954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080684322615137333107979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80215158193640366221621277 30080684322615137333107979)
  ·
    refine ⟨45121026483922705999661969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30080684322615137333107979 45121026483922705999661969)
    ·
      refine ⟨33840769862942029499746477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45121026483922705999661969 33840769862942029499746477)
      ·
        refine ⟨12690288698603261062404929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33840769862942029499746477 12690288698603261062404929)
        ·
          refine ⟨9517716523952445796803697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690288698603261062404929 9517716523952445796803697)
          ·
            refine ⟨7138287392964334347602773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517716523952445796803697 7138287392964334347602773)
            ·
              refine ⟨41825902693150396567985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7138287392964334347602773 41825902693150396567985)
              ·
                rfl

theorem cell22_3298954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 9].length) (baseStart_3298954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298954 prefixEnd_3298954 := by exact prefixLift 3298954
  have htrace : WordTrace (prefixWord ++ tailWord_3298954) baseStart_3298954 baseEnd_3298954 := by
    simpa [prefixWord, tailWord_3298954, baseEnd_3298954] using wordTrace_append hprefix tailTrace_3298954
  have hstable : (prefixWord ++ tailWord_3298954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298954).length < 2 ^ (prefixWord ++ tailWord_3298954).sum := by decide
  have hdescent : baseEnd_3298954 < baseStart_3298954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298958 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3298958 : Nat := 118140960795 + 3298958 * 2 ^ 59
def prefixEnd_3298958 : Nat := 4983230072969 + 3 ^ 40 * 3298958 * 2
def baseEnd_3298958 : Nat := 1129300741996806030235583

theorem tailTrace_3298958 : CollatzResearch.WordTrace tailWord_3298958 prefixEnd_3298958 1129300741996806030235583 := by
  unfold tailWord_3298958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040360397805757251947191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80215255454964038677051685 15040360397805757251947191)
  ·
    refine ⟨22560540596708635877920787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15040360397805757251947191 22560540596708635877920787)
    ·
      refine ⟨33840810895062953816881181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22560540596708635877920787 33840810895062953816881181)
      ·
        refine ⟨12690304085648607681330443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33840810895062953816881181 12690304085648607681330443)
        ·
          refine ⟨19035456128472911521995665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12690304085648607681330443 19035456128472911521995665)
          ·
            refine ⟨14276592096354683641496749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19035456128472911521995665 14276592096354683641496749)
            ·
              refine ⟨5353722036133006365561281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14276592096354683641496749 5353722036133006365561281)
              ·
                refine ⟨4015291527099754774170961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353722036133006365561281 4015291527099754774170961)
                ·
                  refine ⟨3011468645324816080628221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015291527099754774170961 3011468645324816080628221)
                  ·
                    refine ⟨1129300741996806030235583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011468645324816080628221 1129300741996806030235583)
                    ·
                      rfl

theorem cell22_3298958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3298958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298958 prefixEnd_3298958 := by exact prefixLift 3298958
  have htrace : WordTrace (prefixWord ++ tailWord_3298958) baseStart_3298958 baseEnd_3298958 := by
    simpa [prefixWord, tailWord_3298958, baseEnd_3298958] using wordTrace_append hprefix tailTrace_3298958
  have hstable : (prefixWord ++ tailWord_3298958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298958).length < 2 ^ (prefixWord ++ tailWord_3298958).sum := by decide
  have hdescent : baseEnd_3298958 < baseStart_3298958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298975 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 5]
def baseStart_3298975 : Nat := 118140960795 + 3298975 * 2 ^ 59
def prefixEnd_3298975 : Nat := 4983230072969 + 3 ^ 40 * 3298975 * 2
def baseEnd_3298975 : Nat := 1129306561444223652560531

theorem tailTrace_3298975 : CollatzResearch.WordTrace tailWord_3298975 prefixEnd_3298975 1129306561444223652560531 := by
  unfold tailWord_3298975
  simp only [CollatzResearch.WordTrace]
  refine ⟨120323503223384469918946379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80215668815589646612630919 120323503223384469918946379)
  ·
    refine ⟨180485254835076704878419569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120323503223384469918946379 180485254835076704878419569)
    ·
      refine ⟨135363941126307528658814677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180485254835076704878419569 135363941126307528658814677)
      ·
        refine ⟨3172592370147832702940969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 135363941126307528658814677 3172592370147832702940969)
        ·
          refine ⟨2379444277610874527205727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172592370147832702940969 2379444277610874527205727)
          ·
            refine ⟨3569166416416311790808591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379444277610874527205727 3569166416416311790808591)
            ·
              refine ⟨5353749624624467686212887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569166416416311790808591 5353749624624467686212887)
              ·
                refine ⟨8030624436936701529319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353749624624467686212887 8030624436936701529319331)
                ·
                  refine ⟨12045936655405052293978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8030624436936701529319331 12045936655405052293978997)
                  ·
                    refine ⟨1129306561444223652560531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12045936655405052293978997 1129306561444223652560531)
                    ·
                      rfl

theorem cell22_3298975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_3298975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298975 prefixEnd_3298975 := by exact prefixLift 3298975
  have htrace : WordTrace (prefixWord ++ tailWord_3298975) baseStart_3298975 baseEnd_3298975 := by
    simpa [prefixWord, tailWord_3298975, baseEnd_3298975] using wordTrace_append hprefix tailTrace_3298975
  have hstable : (prefixWord ++ tailWord_3298975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298975).length < 2 ^ (prefixWord ++ tailWord_3298975).sum := by decide
  have hdescent : baseEnd_3298975 < baseStart_3298975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3298999 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 7]
def baseStart_3298999 : Nat := 118140960795 + 3298999 * 2 ^ 59
def prefixEnd_3298999 : Nat := 4983230072969 + 3 ^ 40 * 3298999 * 2
def baseEnd_3298999 : Nat := 376438259044898529986819

theorem tailTrace_3298999 : CollatzResearch.WordTrace tailWord_3298999 prefixEnd_3298999 376438259044898529986819 := by
  unfold tailWord_3298999
  simp only [CollatzResearch.WordTrace]
  refine ⟨120324378575297522017820051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80216252383531681345213367 120324378575297522017820051)
  ·
    refine ⟨180486567862946283026730077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120324378575297522017820051 180486567862946283026730077)
    ·
      refine ⟨67682462948604856135023779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180486567862946283026730077 67682462948604856135023779)
      ·
        refine ⟨101523694422907284202535669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67682462948604856135023779 101523694422907284202535669)
        ·
          refine ⟨9517846352147557893987719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101523694422907284202535669 9517846352147557893987719)
          ·
            refine ⟨14276769528221336840981579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517846352147557893987719 14276769528221336840981579)
            ·
              refine ⟨21415154292332005261472369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276769528221336840981579 21415154292332005261472369)
              ·
                refine ⟨16061365719249003946104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21415154292332005261472369 16061365719249003946104277)
                ·
                  refine ⟨376438259044898529986819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16061365719249003946104277 376438259044898529986819)
                  ·
                    rfl

theorem cell22_3298999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_3298999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3298999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3298999 prefixEnd_3298999 := by exact prefixLift 3298999
  have htrace : WordTrace (prefixWord ++ tailWord_3298999) baseStart_3298999 baseEnd_3298999 := by
    simpa [prefixWord, tailWord_3298999, baseEnd_3298999] using wordTrace_append hprefix tailTrace_3298999
  have hstable : (prefixWord ++ tailWord_3298999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3298999).length < 2 ^ (prefixWord ++ tailWord_3298999).sum := by decide
  have hdescent : baseEnd_3298999 < baseStart_3298999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3298999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299020 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_3299020 : Nat := 118140960795 + 3299020 * 2 ^ 59
def prefixEnd_3299020 : Nat := 4983230072969 + 3 ^ 40 * 3299020 * 2
def baseEnd_3299020 : Nat := 1129321965863858535185393

theorem tailTrace_3299020 : CollatzResearch.WordTrace tailWord_3299020 prefixEnd_3299020 1129321965863858535185393 := by
  unfold tailWord_3299020
  simp only [CollatzResearch.WordTrace]
  refine ⟨60162572254110721302167257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80216763005480961736223009 60162572254110721302167257)
  ·
    refine ⟨45121929190583040976625443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60162572254110721302167257 45121929190583040976625443)
    ·
      refine ⟨67682893785874561464938165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45121929190583040976625443 67682893785874561464938165)
      ·
        refine ⟨6345271292425740137337953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67682893785874561464938165 6345271292425740137337953)
        ·
          refine ⟨4758953469319305103003465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345271292425740137337953 4758953469319305103003465)
          ·
            refine ⟨3569215101989478827252599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758953469319305103003465 3569215101989478827252599)
            ·
              refine ⟨5353822652984218240878899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569215101989478827252599 5353822652984218240878899)
              ·
                refine ⟨8030733979476327361318349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353822652984218240878899 8030733979476327361318349)
                ·
                  refine ⟨3011525242303622760494381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8030733979476327361318349 3011525242303622760494381)
                  ·
                    refine ⟨1129321965863858535185393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011525242303622760494381 1129321965863858535185393)
                    ·
                      rfl

theorem cell22_3299020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_3299020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299020 prefixEnd_3299020 := by exact prefixLift 3299020
  have htrace : WordTrace (prefixWord ++ tailWord_3299020) baseStart_3299020 baseEnd_3299020 := by
    simpa [prefixWord, tailWord_3299020, baseEnd_3299020] using wordTrace_append hprefix tailTrace_3299020
  have hstable : (prefixWord ++ tailWord_3299020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299020).length < 2 ^ (prefixWord ++ tailWord_3299020).sum := by decide
  have hdescent : baseEnd_3299020 < baseStart_3299020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299033 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 5]
def baseStart_3299033 : Nat := 118140960795 + 3299033 * 2 ^ 59
def prefixEnd_3299033 : Nat := 4983230072969 + 3 ^ 40 * 3299033 * 2
def baseEnd_3299033 : Nat := 376442138676510278203451

theorem tailTrace_3299033 : CollatzResearch.WordTrace tailWord_3299033 prefixEnd_3299033 376442138676510278203451 := by
  unfold tailWord_3299033
  simp only [CollatzResearch.WordTrace]
  refine ⟨120325618657174345824557753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80217079104782897216371835 120325618657174345824557753)
  ·
    refine ⟨90244213992880759368418315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120325618657174345824557753 90244213992880759368418315)
    ·
      refine ⟨135366320989321139052627473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90244213992880759368418315 135366320989321139052627473)
      ·
        refine ⟨101524740741990854289470605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135366320989321139052627473 101524740741990854289470605)
        ·
          refine ⟨38071777778246570358551477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101524740741990854289470605 38071777778246570358551477)
          ·
            refine ⟨3569229166710615971114201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38071777778246570358551477 3569229166710615971114201)
            ·
              refine ⟨2676921875032961978335651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569229166710615971114201 2676921875032961978335651)
              ·
                refine ⟨4015382812549442967503477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676921875032961978335651 4015382812549442967503477)
                ·
                  refine ⟨376442138676510278203451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015382812549442967503477 376442138676510278203451)
                  ·
                    rfl

theorem cell22_3299033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_3299033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299033 prefixEnd_3299033 := by exact prefixLift 3299033
  have htrace : WordTrace (prefixWord ++ tailWord_3299033) baseStart_3299033 baseEnd_3299033 := by
    simpa [prefixWord, tailWord_3299033, baseEnd_3299033] using wordTrace_append hprefix tailTrace_3299033
  have hstable : (prefixWord ++ tailWord_3299033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299033).length < 2 ^ (prefixWord ++ tailWord_3299033).sum := by decide
  have hdescent : baseEnd_3299033 < baseStart_3299033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299044 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3299044 : Nat := 118140960795 + 3299044 * 2 ^ 59
def prefixEnd_3299044 : Nat := 4983230072969 + 3 ^ 40 * 3299044 * 2
def baseEnd_3299044 : Nat := 376443393851443490861773

theorem tailTrace_3299044 : CollatzResearch.WordTrace tailWord_3299044 prefixEnd_3299044 376443393851443490861773 := by
  unfold tailWord_3299044
  simp only [CollatzResearch.WordTrace]
  refine ⟨60163009930067247351604093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80217346573422996468805457 60163009930067247351604093)
  ·
    refine ⟨22561128723775217756851535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60163009930067247351604093 22561128723775217756851535)
    ·
      refine ⟨33841693085662826635277303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22561128723775217756851535 33841693085662826635277303)
      ·
        refine ⟨50762539628494239952915955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33841693085662826635277303 50762539628494239952915955)
        ·
          refine ⟨76143809442741359929373933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50762539628494239952915955 76143809442741359929373933)
          ·
            refine ⟨28553928541028009973515225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76143809442741359929373933 28553928541028009973515225)
            ·
              refine ⟨21415446405771007480136419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28553928541028009973515225 21415446405771007480136419)
              ·
                refine ⟨32123169608656511220204629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21415446405771007480136419 32123169608656511220204629)
                ·
                  refine ⟨376443393851443490861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32123169608656511220204629 376443393851443490861773)
                  ·
                    rfl

theorem cell22_3299044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3299044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299044 prefixEnd_3299044 := by exact prefixLift 3299044
  have htrace : WordTrace (prefixWord ++ tailWord_3299044) baseStart_3299044 baseEnd_3299044 := by
    simpa [prefixWord, tailWord_3299044, baseEnd_3299044] using wordTrace_append hprefix tailTrace_3299044
  have hstable : (prefixWord ++ tailWord_3299044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299044).length < 2 ^ (prefixWord ++ tailWord_3299044).sum := by decide
  have hdescent : baseEnd_3299044 < baseStart_3299044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299059 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_3299059 : Nat := 118140960795 + 3299059 * 2 ^ 59
def prefixEnd_3299059 : Nat := 4983230072969 + 3 ^ 40 * 3299059 * 2
def baseEnd_3299059 : Nat := 1129335316360875433460273

theorem tailTrace_3299059 : CollatzResearch.WordTrace tailWord_3299059 prefixEnd_3299059 1129335316360875433460273 := by
  unfold tailWord_3299059
  simp only [CollatzResearch.WordTrace]
  refine ⟨120326566955080152265004231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80217711303386768176669487 120326566955080152265004231)
  ·
    refine ⟨180489850432620228397506347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120326566955080152265004231 180489850432620228397506347)
    ·
      refine ⟨270734775648930342596259521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180489850432620228397506347 270734775648930342596259521)
      ·
        refine ⟨203051081736697756947194641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270734775648930342596259521 203051081736697756947194641)
        ·
          refine ⟨152288311302523317710395981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203051081736697756947194641 152288311302523317710395981)
          ·
            refine ⟨57108116738446244141398493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152288311302523317710395981 57108116738446244141398493)
            ·
              refine ⟨21415543776917341553024435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57108116738446244141398493 21415543776917341553024435)
              ·
                refine ⟨32123315665376012329536653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21415543776917341553024435 32123315665376012329536653)
                ·
                  refine ⟨12046243374516004623576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32123315665376012329536653 12046243374516004623576245)
                  ·
                    refine ⟨1129335316360875433460273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12046243374516004623576245 1129335316360875433460273)
                    ·
                      rfl

theorem cell22_3299059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_3299059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299059 prefixEnd_3299059 := by exact prefixLift 3299059
  have htrace : WordTrace (prefixWord ++ tailWord_3299059) baseStart_3299059 baseEnd_3299059 := by
    simpa [prefixWord, tailWord_3299059, baseEnd_3299059] using wordTrace_append hprefix tailTrace_3299059
  have hstable : (prefixWord ++ tailWord_3299059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299059).length < 2 ^ (prefixWord ++ tailWord_3299059).sum := by decide
  have hdescent : baseEnd_3299059 < baseStart_3299059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299093 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_3299093 : Nat := 118140960795 + 3299093 * 2 ^ 59
def prefixEnd_3299093 : Nat := 4983230072969 + 3 ^ 40 * 3299093 * 2
def baseEnd_3299093 : Nat := 1129346955255710678110169

theorem tailTrace_3299093 : CollatzResearch.WordTrace tailWord_3299093 prefixEnd_3299093 1129346955255710678110169 := by
  unfold tailWord_3299093
  simp only [CollatzResearch.WordTrace]
  refine ⟨120327807036956976071741933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80218538024637984047827955 120327807036956976071741933)
  ·
    refine ⟨45122927638858866026903225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120327807036956976071741933 45122927638858866026903225)
    ·
      refine ⟨33842195729144149520177419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45122927638858866026903225 33842195729144149520177419)
      ·
        refine ⟨50763293593716224280266129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33842195729144149520177419 50763293593716224280266129)
        ·
          refine ⟨38072470195287168210199597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50763293593716224280266129 38072470195287168210199597)
          ·
            refine ⟨14277176323232688078824849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38072470195287168210199597 14277176323232688078824849)
            ·
              refine ⟨10707882242424516059118637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14277176323232688078824849 10707882242424516059118637)
              ·
                refine ⟨4015455840909193522169489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10707882242424516059118637 4015455840909193522169489)
                ·
                  refine ⟨3011591880681895141627117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4015455840909193522169489 3011591880681895141627117)
                  ·
                    refine ⟨1129346955255710678110169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011591880681895141627117 1129346955255710678110169)
                    ·
                      rfl

theorem cell22_3299093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_3299093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299093 prefixEnd_3299093 := by exact prefixLift 3299093
  have htrace : WordTrace (prefixWord ++ tailWord_3299093) baseStart_3299093 baseEnd_3299093 := by
    simpa [prefixWord, tailWord_3299093, baseEnd_3299093] using wordTrace_append hprefix tailTrace_3299093
  have hstable : (prefixWord ++ tailWord_3299093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299093).length < 2 ^ (prefixWord ++ tailWord_3299093).sum := by decide
  have hdescent : baseEnd_3299093 < baseStart_3299093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299108 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_3299108 : Nat := 118140960795 + 3299108 * 2 ^ 59
def prefixEnd_3299108 : Nat := 4983230072969 + 3 ^ 40 * 3299108 * 2
def baseEnd_3299108 : Nat := 1129352090062255638985123

theorem tailTrace_3299108 : CollatzResearch.WordTrace tailWord_3299108 prefixEnd_3299108 1129352090062255638985123 := by
  unfold tailWord_3299108
  simp only [CollatzResearch.WordTrace]
  refine ⟨60164177065951316816768989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80218902754601755755691985 60164177065951316816768989)
  ·
    refine ⟨22561566399731743806288371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60164177065951316816768989 22561566399731743806288371)
    ·
      refine ⟨33842349599597615709432557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22561566399731743806288371 33842349599597615709432557)
      ·
        refine ⟨12690881099849105891037209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33842349599597615709432557 12690881099849105891037209)
        ·
          refine ⟨9518160824886829418277907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690881099849105891037209 9518160824886829418277907)
          ·
            refine ⟨14277241237330244127416861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518160824886829418277907 14277241237330244127416861)
            ·
              refine ⟨5353965463998841547781323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14277241237330244127416861 5353965463998841547781323)
              ·
                refine ⟨8030948195998262321671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353965463998841547781323 8030948195998262321671985)
                ·
                  refine ⟨6023211146998696741253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8030948195998262321671985 6023211146998696741253989)
                  ·
                    refine ⟨1129352090062255638985123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023211146998696741253989 1129352090062255638985123)
                    ·
                      rfl

theorem cell22_3299108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_3299108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299108 prefixEnd_3299108 := by exact prefixLift 3299108
  have htrace : WordTrace (prefixWord ++ tailWord_3299108) baseStart_3299108 baseEnd_3299108 := by
    simpa [prefixWord, tailWord_3299108, baseEnd_3299108] using wordTrace_append hprefix tailTrace_3299108
  have hstable : (prefixWord ++ tailWord_3299108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299108).length < 2 ^ (prefixWord ++ tailWord_3299108).sum := by decide
  have hdescent : baseEnd_3299108 < baseStart_3299108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299119 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_3299119 : Nat := 118140960795 + 3299119 * 2 ^ 59
def prefixEnd_3299119 : Nat := 4983230072969 + 3 ^ 40 * 3299119 * 2
def baseEnd_3299119 : Nat := 1129355855587055276960089

theorem tailTrace_3299119 : CollatzResearch.WordTrace tailWord_3299119 prefixEnd_3299119 1129355855587055276960089 := by
  unfold tailWord_3299119
  simp only [CollatzResearch.WordTrace]
  refine ⟨120328755334862782512188411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80219170223241855008125607 120328755334862782512188411)
  ·
    refine ⟨180493133002294173768282617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120328755334862782512188411 180493133002294173768282617)
    ·
      refine ⟨135369849751720630326211963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180493133002294173768282617 135369849751720630326211963)
      ·
        refine ⟨203054774627580945489317945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135369849751720630326211963 203054774627580945489317945)
        ·
          refine ⟨152291080970685709116988459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203054774627580945489317945 152291080970685709116988459)
          ·
            refine ⟨228436621456028563675482689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152291080970685709116988459 228436621456028563675482689)
            ·
              refine ⟨171327466092021422756612017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228436621456028563675482689 171327466092021422756612017)
              ·
                refine ⟨128495599569016067067459013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171327466092021422756612017 128495599569016067067459013)
                ·
                  refine ⟨24092924919190512575148565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128495599569016067067459013 24092924919190512575148565)
                  ·
                    refine ⟨1129355855587055276960089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24092924919190512575148565 1129355855587055276960089)
                    ·
                      rfl

theorem cell22_3299119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_3299119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299119 prefixEnd_3299119 := by exact prefixLift 3299119
  have htrace : WordTrace (prefixWord ++ tailWord_3299119) baseStart_3299119 baseEnd_3299119 := by
    simpa [prefixWord, tailWord_3299119, baseEnd_3299119] using wordTrace_append hprefix tailTrace_3299119
  have hstable : (prefixWord ++ tailWord_3299119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299119).length < 2 ^ (prefixWord ++ tailWord_3299119).sum := by decide
  have hdescent : baseEnd_3299119 < baseStart_3299119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299211 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_3299211 : Nat := 118140960795 + 3299211 * 2 ^ 59
def prefixEnd_3299211 : Nat := 4983230072969 + 3 ^ 40 * 3299211 * 2
def baseEnd_3299211 : Nat := 1129387349067197703659807

theorem tailTrace_3299211 : CollatzResearch.WordTrace tailWord_3299211 prefixEnd_3299211 1129387349067197703659807 := by
  unfold tailWord_3299211
  simp only [CollatzResearch.WordTrace]
  refine ⟨120332110850529482224537487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80221407233686321483024991 120332110850529482224537487)
  ·
    refine ⟨180498166275794223336806231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120332110850529482224537487 180498166275794223336806231)
    ·
      refine ⟨270747249413691335005209347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180498166275794223336806231 270747249413691335005209347)
      ·
        refine ⟨406120874120537002507814021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270747249413691335005209347 406120874120537002507814021)
        ·
          refine ⟨76147663897600687970215129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406120874120537002507814021 76147663897600687970215129)
          ·
            refine ⟨57110747923200515977661347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76147663897600687970215129 57110747923200515977661347)
            ·
              refine ⟨85666121884800773966492021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57110747923200515977661347 85666121884800773966492021)
              ·
                refine ⟨8031198926700072559358627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85666121884800773966492021 8031198926700072559358627)
                ·
                  refine ⟨12046798390050108839037941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031198926700072559358627 12046798390050108839037941)
                  ·
                    refine ⟨1129387349067197703659807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12046798390050108839037941 1129387349067197703659807)
                    ·
                      rfl

theorem cell22_3299211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_3299211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299211 prefixEnd_3299211 := by exact prefixLift 3299211
  have htrace : WordTrace (prefixWord ++ tailWord_3299211) baseStart_3299211 baseEnd_3299211 := by
    simpa [prefixWord, tailWord_3299211, baseEnd_3299211] using wordTrace_append hprefix tailTrace_3299211
  have hstable : (prefixWord ++ tailWord_3299211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299211).length < 2 ^ (prefixWord ++ tailWord_3299211).sum := by decide
  have hdescent : baseEnd_3299211 < baseStart_3299211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299228 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3299228 : Nat := 118140960795 + 3299228 * 2 ^ 59
def prefixEnd_3299228 : Nat := 4983230072969 + 3 ^ 40 * 3299228 * 2
def baseEnd_3299228 : Nat := 1129393168514615325984755

theorem tailTrace_3299228 : CollatzResearch.WordTrace tailWord_3299228 prefixEnd_3299228 1129393168514615325984755 := by
  unfold tailWord_3299228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60166365445733947063953169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80221820594311929418604225 60166365445733947063953169)
  ·
    refine ⟨45124774084300460297964877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60166365445733947063953169 45124774084300460297964877)
    ·
      refine ⟨16921790281612672611736829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45124774084300460297964877 16921790281612672611736829)
      ·
        refine ⟨6345671355604752229401311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16921790281612672611736829 6345671355604752229401311)
        ·
          refine ⟨9518507033407128344101967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345671355604752229401311 9518507033407128344101967)
          ·
            refine ⟨14277760550110692516152951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518507033407128344101967 14277760550110692516152951)
            ·
              refine ⟨21416640825166038774229427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14277760550110692516152951 21416640825166038774229427)
              ·
                refine ⟨32124961237749058161344141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21416640825166038774229427 32124961237749058161344141)
                ·
                  refine ⟨12046860464155896810504053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32124961237749058161344141 12046860464155896810504053)
                  ·
                    refine ⟨1129393168514615325984755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12046860464155896810504053 1129393168514615325984755)
                    ·
                      rfl

theorem cell22_3299228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3299228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299228 prefixEnd_3299228 := by exact prefixLift 3299228
  have htrace : WordTrace (prefixWord ++ tailWord_3299228) baseStart_3299228 baseEnd_3299228 := by
    simpa [prefixWord, tailWord_3299228, baseEnd_3299228] using wordTrace_append hprefix tailTrace_3299228
  have hstable : (prefixWord ++ tailWord_3299228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299228).length < 2 ^ (prefixWord ++ tailWord_3299228).sum := by decide
  have hdescent : baseEnd_3299228 < baseStart_3299228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299271 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3299271 : Nat := 118140960795 + 3299271 * 2 ^ 59
def prefixEnd_3299271 : Nat := 4983230072969 + 3 ^ 40 * 3299271 * 2
def baseEnd_3299271 : Nat := 1129407888293377547159623

theorem tailTrace_3299271 : CollatzResearch.WordTrace tailWord_3299271 prefixEnd_3299271 1129407888293377547159623 := by
  unfold tailWord_3299271
  simp only [CollatzResearch.WordTrace]
  refine ⟨120334299230312112471721667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80222866153541408314481111 120334299230312112471721667)
  ·
    refine ⟨180501448845468168707582501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120334299230312112471721667 180501448845468168707582501)
    ·
      refine ⟨33844021658525281632671719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180501448845468168707582501 33844021658525281632671719)
      ·
        refine ⟨50766032487787922449007579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33844021658525281632671719 50766032487787922449007579)
        ·
          refine ⟨76149048731681883673511369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50766032487787922449007579 76149048731681883673511369)
          ·
            refine ⟨57111786548761412755133527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76149048731681883673511369 57111786548761412755133527)
            ·
              refine ⟨85667679823142119132700291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57111786548761412755133527 85667679823142119132700291)
              ·
                refine ⟨128501519734713178699050437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85667679823142119132700291 128501519734713178699050437)
                ·
                  refine ⟨24094034950258721006071957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128501519734713178699050437 24094034950258721006071957)
                  ·
                    refine ⟨1129407888293377547159623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24094034950258721006071957 1129407888293377547159623)
                    ·
                      rfl

theorem cell22_3299271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3299271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299271 prefixEnd_3299271 := by exact prefixLift 3299271
  have htrace : WordTrace (prefixWord ++ tailWord_3299271) baseStart_3299271 baseEnd_3299271 := by
    simpa [prefixWord, tailWord_3299271, baseEnd_3299271] using wordTrace_append hprefix tailTrace_3299271
  have hstable : (prefixWord ++ tailWord_3299271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299271).length < 2 ^ (prefixWord ++ tailWord_3299271).sum := by decide
  have hdescent : baseEnd_3299271 < baseStart_3299271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299273 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_3299273 : Nat := 118140960795 + 3299273 * 2 ^ 59
def prefixEnd_3299273 : Nat := 4983230072969 + 3 ^ 40 * 3299273 * 2
def baseEnd_3299273 : Nat := 1129408572934250208609617

theorem tailTrace_3299273 : CollatzResearch.WordTrace tailWord_3299273 prefixEnd_3299273 1129408572934250208609617 := by
  unfold tailWord_3299273
  simp only [CollatzResearch.WordTrace]
  refine ⟨120334372176304866813294473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80222914784203244542196315 120334372176304866813294473)
  ·
    refine ⟨90250779132228650109970855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120334372176304866813294473 90250779132228650109970855)
    ·
      refine ⟨135376168698342975164956283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90250779132228650109970855 135376168698342975164956283)
      ·
        refine ⟨203064253047514462747434425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135376168698342975164956283 203064253047514462747434425)
        ·
          refine ⟨152298189785635847060575819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203064253047514462747434425 152298189785635847060575819)
          ·
            refine ⟨228447284678453770590863729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152298189785635847060575819 228447284678453770590863729)
            ·
              refine ⟨171335463508840327943147797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228447284678453770590863729 171335463508840327943147797)
              ·
                refine ⟨8031349851976890372335053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171335463508840327943147797 8031349851976890372335053)
                ·
                  refine ⟨3011756194491333889625645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8031349851976890372335053 3011756194491333889625645)
                  ·
                    refine ⟨1129408572934250208609617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011756194491333889625645 1129408572934250208609617)
                    ·
                      rfl

theorem cell22_3299273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_3299273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299273 prefixEnd_3299273 := by exact prefixLift 3299273
  have htrace : WordTrace (prefixWord ++ tailWord_3299273) baseStart_3299273 baseEnd_3299273 := by
    simpa [prefixWord, tailWord_3299273, baseEnd_3299273] using wordTrace_append hprefix tailTrace_3299273
  have hstable : (prefixWord ++ tailWord_3299273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299273).length < 2 ^ (prefixWord ++ tailWord_3299273).sum := by decide
  have hdescent : baseEnd_3299273 < baseStart_3299273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299292 : List Nat := [2, 2, 6, 1, 1, 1, 9]
def baseStart_3299292 : Nat := 118140960795 + 3299292 * 2 ^ 59
def prefixEnd_3299292 : Nat := 4983230072969 + 3 ^ 40 * 3299292 * 2
def baseEnd_3299292 : Nat := 41830188037871870088317

theorem tailTrace_3299292 : CollatzResearch.WordTrace tailWord_3299292 prefixEnd_3299292 41830188037871870088317 := by
  unfold tailWord_3299292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60167532581618016529118065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80223376775490688705490753 60167532581618016529118065)
  ·
    refine ⟨45125649436213512396838549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60167532581618016529118065 45125649436213512396838549)
    ·
      refine ⟨2115264817322508393601807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45125649436213512396838549 2115264817322508393601807)
      ·
        refine ⟨3172897225983762590402711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115264817322508393601807 3172897225983762590402711)
        ·
          refine ⟨4759345838975643885604067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172897225983762590402711 4759345838975643885604067)
          ·
            refine ⟨7139018758463465828406101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759345838975643885604067 7139018758463465828406101)
            ·
              refine ⟨41830188037871870088317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7139018758463465828406101 41830188037871870088317)
              ·
                rfl

theorem cell22_3299292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 9].length) (baseStart_3299292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299292 prefixEnd_3299292 := by exact prefixLift 3299292
  have htrace : WordTrace (prefixWord ++ tailWord_3299292) baseStart_3299292 baseEnd_3299292 := by
    simpa [prefixWord, tailWord_3299292, baseEnd_3299292] using wordTrace_append hprefix tailTrace_3299292
  have hstable : (prefixWord ++ tailWord_3299292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299292).length < 2 ^ (prefixWord ++ tailWord_3299292).sum := by decide
  have hdescent : baseEnd_3299292 < baseStart_3299292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299365 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 6]
def baseStart_3299365 : Nat := 118140960795 + 3299365 * 2 ^ 59
def prefixEnd_3299365 : Nat := 4983230072969 + 3 ^ 40 * 3299365 * 2
def baseEnd_3299365 : Nat := 376480022138130878436445

theorem tailTrace_3299365 : CollatzResearch.WordTrace tailWord_3299365 prefixEnd_3299365 376480022138130878436445 := by
  unfold tailWord_3299365
  simp only [CollatzResearch.WordTrace]
  refine ⟨120337727691971566525643549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80225151794647711017095699 120337727691971566525643549)
  ·
    refine ⟨45126647884489337447116331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120337727691971566525643549 45126647884489337447116331)
    ·
      refine ⟨67689971826734006170674497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45126647884489337447116331 67689971826734006170674497)
      ·
        refine ⟨50767478870050504628005873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67689971826734006170674497 50767478870050504628005873)
        ·
          refine ⟨38075609152537878471004405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50767478870050504628005873 38075609152537878471004405)
          ·
            refine ⟨3569588358050426106656663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38075609152537878471004405 3569588358050426106656663)
            ·
              refine ⟨5354382537075639159984995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569588358050426106656663 5354382537075639159984995)
              ·
                refine ⟨8031573805613458739977493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354382537075639159984995 8031573805613458739977493)
                ·
                  refine ⟨376480022138130878436445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8031573805613458739977493 376480022138130878436445)
                  ·
                    rfl

theorem cell22_3299365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_3299365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299365 prefixEnd_3299365 := by exact prefixLift 3299365
  have htrace : WordTrace (prefixWord ++ tailWord_3299365) baseStart_3299365 baseEnd_3299365 := by
    simpa [prefixWord, tailWord_3299365, baseEnd_3299365] using wordTrace_append hprefix tailTrace_3299365
  have hstable : (prefixWord ++ tailWord_3299365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299365).length < 2 ^ (prefixWord ++ tailWord_3299365).sum := by decide
  have hdescent : baseEnd_3299365 < baseStart_3299365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299384 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_3299384 : Nat := 118140960795 + 3299384 * 2 ^ 59
def prefixEnd_3299384 : Nat := 4983230072969 + 3 ^ 40 * 3299384 * 2
def baseEnd_3299384 : Nat := 1129446570502682919084277

theorem tailTrace_3299384 : CollatzResearch.WordTrace tailWord_3299384 prefixEnd_3299384 1129446570502682919084277 := by
  unfold tailWord_3299384
  simp only [CollatzResearch.WordTrace]
  refine ⟨60169210339451366385292603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80225613785935155180390137 60169210339451366385292603)
  ·
    refine ⟨90253815509177049577938905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60169210339451366385292603 90253815509177049577938905)
    ·
      refine ⟨67690361631882787183454179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90253815509177049577938905 67690361631882787183454179)
      ·
        refine ⟨101535542447824180775181269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67690361631882787183454179 101535542447824180775181269)
        ·
          refine ⟨2379739276120879236918311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 101535542447824180775181269 2379739276120879236918311)
          ·
            refine ⟨3569608914181318855377467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379739276120879236918311 3569608914181318855377467)
            ·
              refine ⟨5354413371271978283066201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569608914181318855377467 5354413371271978283066201)
              ·
                refine ⟨4015810028453983712299651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354413371271978283066201 4015810028453983712299651)
                ·
                  refine ⟨6023715042680975568449477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015810028453983712299651 6023715042680975568449477)
                  ·
                    refine ⟨1129446570502682919084277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023715042680975568449477 1129446570502682919084277)
                    ·
                      rfl

theorem cell22_3299384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_3299384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299384 prefixEnd_3299384 := by exact prefixLift 3299384
  have htrace : WordTrace (prefixWord ++ tailWord_3299384) baseStart_3299384 baseEnd_3299384 := by
    simpa [prefixWord, tailWord_3299384, baseEnd_3299384] using wordTrace_append hprefix tailTrace_3299384
  have hstable : (prefixWord ++ tailWord_3299384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299384).length < 2 ^ (prefixWord ++ tailWord_3299384).sum := by decide
  have hdescent : baseEnd_3299384 < baseStart_3299384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299410 : List Nat := [3, 2, 2, 1, 5, 9]
def baseStart_3299410 : Nat := 118140960795 + 3299410 * 2 ^ 59
def prefixEnd_3299410 : Nat := 4983230072969 + 3 ^ 40 * 3299410 * 2
def baseEnd_3299410 : Nat := 13943894701654660715237

theorem tailTrace_3299410 : CollatzResearch.WordTrace tailWord_3299410 prefixEnd_3299410 13943894701654660715237 := by
  unfold tailWord_3299410
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084842244202134802757921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80226245984539026140687789 30084842244202134802757921)
  ·
    refine ⟨22563631683151601102068441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084842244202134802757921 22563631683151601102068441)
    ·
      refine ⟨16922723762363700826551331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22563631683151601102068441 16922723762363700826551331)
      ·
        refine ⟨25384085643545551239826997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16922723762363700826551331 25384085643545551239826997)
        ·
          refine ⟨2379758029082395428733781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25384085643545551239826997 2379758029082395428733781)
          ·
            refine ⟨13943894701654660715237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2379758029082395428733781 13943894701654660715237)
            ·
              rfl

theorem cell22_3299410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 9].length) (baseStart_3299410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299410 prefixEnd_3299410 := by exact prefixLift 3299410
  have htrace : WordTrace (prefixWord ++ tailWord_3299410) baseStart_3299410 baseEnd_3299410 := by
    simpa [prefixWord, tailWord_3299410, baseEnd_3299410] using wordTrace_append hprefix tailTrace_3299410
  have hstable : (prefixWord ++ tailWord_3299410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299410).length < 2 ^ (prefixWord ++ tailWord_3299410).sum := by decide
  have hdescent : baseEnd_3299410 < baseStart_3299410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299425 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3299425 : Nat := 118140960795 + 3299425 * 2 ^ 59
def prefixEnd_3299425 : Nat := 4983230072969 + 3 ^ 40 * 3299425 * 2
def baseEnd_3299425 : Nat := 1129460605640572478809151

theorem tailTrace_3299425 : CollatzResearch.WordTrace tailWord_3299425 prefixEnd_3299425 1129460605640572478809151 := by
  unfold tailWord_3299425
  simp only [CollatzResearch.WordTrace]
  refine ⟨120339916071754196772827729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80226610714502797848551819 120339916071754196772827729)
  ·
    refine ⟨90254937053815647579620797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120339916071754196772827729 90254937053815647579620797)
    ·
      refine ⟨33845601395180867842357799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90254937053815647579620797 33845601395180867842357799)
      ·
        refine ⟨50768402092771301763536699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33845601395180867842357799 50768402092771301763536699)
        ·
          refine ⟨76152603139156952645305049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50768402092771301763536699 76152603139156952645305049)
          ·
            refine ⟨57114452354367714483978787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76152603139156952645305049 57114452354367714483978787)
            ·
              refine ⟨85671678531551571725968181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57114452354367714483978787 85671678531551571725968181)
              ·
                refine ⟨8031719862332959849309517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85671678531551571725968181 8031719862332959849309517)
                ·
                  refine ⟨3011894948374859943491069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8031719862332959849309517 3011894948374859943491069)
                  ·
                    refine ⟨1129460605640572478809151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011894948374859943491069 1129460605640572478809151)
                    ·
                      rfl

theorem cell22_3299425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3299425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299425 prefixEnd_3299425 := by exact prefixLift 3299425
  have htrace : WordTrace (prefixWord ++ tailWord_3299425) baseStart_3299425 baseEnd_3299425 := by
    simpa [prefixWord, tailWord_3299425, baseEnd_3299425] using wordTrace_append hprefix tailTrace_3299425
  have hstable : (prefixWord ++ tailWord_3299425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299425).length < 2 ^ (prefixWord ++ tailWord_3299425).sum := by decide
  have hdescent : baseEnd_3299425 < baseStart_3299425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299442 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_3299442 : Nat := 118140960795 + 3299442 * 2 ^ 59
def prefixEnd_3299442 : Nat := 4983230072969 + 3 ^ 40 * 3299442 * 2
def baseEnd_3299442 : Nat := 1129466425087990101134099

theorem tailTrace_3299442 : CollatzResearch.WordTrace tailWord_3299442 prefixEnd_3299442 1129466425087990101134099 := by
  unfold tailWord_3299442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30085134028173152169049145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80227024075128405784131053 30085134028173152169049145)
  ·
    refine ⟨22563850521129864126786859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30085134028173152169049145 22563850521129864126786859)
    ·
      refine ⟨33845775781694796190180289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22563850521129864126786859 33845775781694796190180289)
      ·
        refine ⟨25384331836271097142635217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33845775781694796190180289 25384331836271097142635217)
        ·
          refine ⟨19038248877203322856976413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25384331836271097142635217 19038248877203322856976413)
          ·
            refine ⟨7139343328951246071366155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19038248877203322856976413 7139343328951246071366155)
            ·
              refine ⟨10709014993426869107049233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139343328951246071366155 10709014993426869107049233)
              ·
                refine ⟨8031761245070151830286925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10709014993426869107049233 8031761245070151830286925)
                ·
                  refine ⟨3011910466901306936357597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8031761245070151830286925 3011910466901306936357597)
                  ·
                    refine ⟨1129466425087990101134099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011910466901306936357597 1129466425087990101134099)
                    ·
                      rfl

theorem cell22_3299442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_3299442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299442 prefixEnd_3299442 := by exact prefixLift 3299442
  have htrace : WordTrace (prefixWord ++ tailWord_3299442) baseStart_3299442 baseEnd_3299442 := by
    simpa [prefixWord, tailWord_3299442, baseEnd_3299442] using wordTrace_append hprefix tailTrace_3299442
  have hstable : (prefixWord ++ tailWord_3299442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299442).length < 2 ^ (prefixWord ++ tailWord_3299442).sum := by decide
  have hdescent : baseEnd_3299442 < baseStart_3299442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299459 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 1, 3]
def baseStart_3299459 : Nat := 118140960795 + 3299459 * 2 ^ 59
def prefixEnd_3299459 : Nat := 4983230072969 + 3 ^ 40 * 3299459 * 2
def baseEnd_3299459 : Nat := 1129472244535407723459047

theorem tailTrace_3299459 : CollatzResearch.WordTrace tailWord_3299459 prefixEnd_3299459 1129472244535407723459047 := by
  unfold tailWord_3299459
  simp only [CollatzResearch.WordTrace]
  refine ⟨120341156153631020579565431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80227437435754013719710287 120341156153631020579565431)
  ·
    refine ⟨180511734230446530869348147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120341156153631020579565431 180511734230446530869348147)
    ·
      refine ⟨270767601345669796304022221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180511734230446530869348147 270767601345669796304022221)
      ·
        refine ⟨101537850504626173614008333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270767601345669796304022221 101537850504626173614008333)
        ·
          refine ⟨38076693939234815105253125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101537850504626173614008333 38076693939234815105253125)
          ·
            refine ⟨7139380113606527832234961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38076693939234815105253125 7139380113606527832234961)
            ·
              refine ⟨5354535085204895874176221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139380113606527832234961 5354535085204895874176221)
              ·
                refine ⟨2007950656951835952816083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354535085204895874176221 2007950656951835952816083)
                ·
                  refine ⟨3011925985427753929224125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007950656951835952816083 3011925985427753929224125)
                  ·
                    refine ⟨1129472244535407723459047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011925985427753929224125 1129472244535407723459047)
                    ·
                      rfl

theorem cell22_3299459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 3].length) (baseStart_3299459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299459 prefixEnd_3299459 := by exact prefixLift 3299459
  have htrace : WordTrace (prefixWord ++ tailWord_3299459) baseStart_3299459 baseEnd_3299459 := by
    simpa [prefixWord, tailWord_3299459, baseEnd_3299459] using wordTrace_append hprefix tailTrace_3299459
  have hstable : (prefixWord ++ tailWord_3299459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299459).length < 2 ^ (prefixWord ++ tailWord_3299459).sum := by decide
  have hdescent : baseEnd_3299459 < baseStart_3299459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299476 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3299476 : Nat := 118140960795 + 3299476 * 2 ^ 59
def prefixEnd_3299476 : Nat := 4983230072969 + 3 ^ 40 * 3299476 * 2
def baseEnd_3299476 : Nat := 1129478063982825345783995

theorem tailTrace_3299476 : CollatzResearch.WordTrace tailWord_3299476 prefixEnd_3299476 1129478063982825345783995 := by
  unfold tailWord_3299476
  simp only [CollatzResearch.WordTrace]
  refine ⟨60170888097284716241467141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80227850796379621655289521 60170888097284716241467141)
  ·
    refine ⟨11282041518240884295275089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60170888097284716241467141 11282041518240884295275089)
    ·
      refine ⟨8461531138680663221456317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11282041518240884295275089 8461531138680663221456317)
      ·
        refine ⟨3173074177005248708046119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8461531138680663221456317 3173074177005248708046119)
        ·
          refine ⟨4759611265507873062069179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173074177005248708046119 4759611265507873062069179)
          ·
            refine ⟨7139416898261809593103769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759611265507873062069179 7139416898261809593103769)
            ·
              refine ⟨5354562673696357194827827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7139416898261809593103769 5354562673696357194827827)
              ·
                refine ⟨8031844010544535792241741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354562673696357194827827 8031844010544535792241741)
                ·
                  refine ⟨3011941503954200922090653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8031844010544535792241741 3011941503954200922090653)
                  ·
                    refine ⟨1129478063982825345783995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011941503954200922090653 1129478063982825345783995)
                    ·
                      rfl

theorem cell22_3299476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3299476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299476 prefixEnd_3299476 := by exact prefixLift 3299476
  have htrace : WordTrace (prefixWord ++ tailWord_3299476) baseStart_3299476 baseEnd_3299476 := by
    simpa [prefixWord, tailWord_3299476, baseEnd_3299476] using wordTrace_append hprefix tailTrace_3299476
  have hstable : (prefixWord ++ tailWord_3299476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299476).length < 2 ^ (prefixWord ++ tailWord_3299476).sum := by decide
  have hdescent : baseEnd_3299476 < baseStart_3299476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299515 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 6, 3]
def baseStart_3299515 : Nat := 118140960795 + 3299515 * 2 ^ 59
def prefixEnd_3299515 : Nat := 4983230072969 + 3 ^ 40 * 3299515 * 2
def baseEnd_3299515 : Nat := 1129491414479842244058875

theorem tailTrace_3299515 : CollatzResearch.WordTrace tailWord_3299515 prefixEnd_3299515 1129491414479842244058875 := by
  unfold tailWord_3299515
  simp only [CollatzResearch.WordTrace]
  refine ⟨120343198641428142143603999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80228799094285428095735999 120343198641428142143603999)
  ·
    refine ⟨180514797962142213215405999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120343198641428142143603999 180514797962142213215405999)
    ·
      refine ⟨270772196943213319823108999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180514797962142213215405999 270772196943213319823108999)
      ·
        refine ⟨406158295414819979734663499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270772196943213319823108999 406158295414819979734663499)
        ·
          refine ⟨609237443122229969601995249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406158295414819979734663499 609237443122229969601995249)
          ·
            refine ⟨456928082341672477201496437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609237443122229969601995249 456928082341672477201496437)
            ·
              refine ⟨42837007719531794737640291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456928082341672477201496437 42837007719531794737640291)
              ·
                refine ⟨64255511579297692106460437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42837007719531794737640291 64255511579297692106460437)
                ·
                  refine ⟨3011977105279579317490333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64255511579297692106460437 3011977105279579317490333)
                  ·
                    refine ⟨1129491414479842244058875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011977105279579317490333 1129491414479842244058875)
                    ·
                      rfl

theorem cell22_3299515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 3].length) (baseStart_3299515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299515 prefixEnd_3299515 := by exact prefixLift 3299515
  have htrace : WordTrace (prefixWord ++ tailWord_3299515) baseStart_3299515 baseEnd_3299515 := by
    simpa [prefixWord, tailWord_3299515, baseEnd_3299515] using wordTrace_append hprefix tailTrace_3299515
  have hstable : (prefixWord ++ tailWord_3299515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299515).length < 2 ^ (prefixWord ++ tailWord_3299515).sum := by decide
  have hdescent : baseEnd_3299515 < baseStart_3299515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299605 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3299605 : Nat := 118140960795 + 3299605 * 2 ^ 59
def prefixEnd_3299605 : Nat := 4983230072969 + 3 ^ 40 * 3299605 * 2
def baseEnd_3299605 : Nat := 1129522223319112009308599

theorem tailTrace_3299605 : CollatzResearch.WordTrace tailWord_3299605 prefixEnd_3299605 1129522223319112009308599 := by
  unfold tailWord_3299605
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346481211102087514380269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80230987474068058342920179 120346481211102087514380269)
  ·
    refine ⟨45129930454163282817892601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120346481211102087514380269 45129930454163282817892601)
    ·
      refine ⟨33847447840622462113419451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45129930454163282817892601 33847447840622462113419451)
      ·
        refine ⟨50771171760933693170129177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33847447840622462113419451 50771171760933693170129177)
        ·
          refine ⟨38078378820700269877596883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50771171760933693170129177 38078378820700269877596883)
          ·
            refine ⟨57117568231050404816395325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38078378820700269877596883 57117568231050404816395325)
            ·
              refine ⟨21419088086643901806148247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57117568231050404816395325 21419088086643901806148247)
              ·
                refine ⟨32128632129965852709222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21419088086643901806148247 32128632129965852709222371)
                ·
                  refine ⟨48192948194948779063833557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32128632129965852709222371 48192948194948779063833557)
                  ·
                    refine ⟨1129522223319112009308599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48192948194948779063833557 1129522223319112009308599)
                    ·
                      rfl

theorem cell22_3299605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3299605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299605 prefixEnd_3299605 := by exact prefixLift 3299605
  have htrace : WordTrace (prefixWord ++ tailWord_3299605) baseStart_3299605 baseEnd_3299605 := by
    simpa [prefixWord, tailWord_3299605, baseEnd_3299605] using wordTrace_append hprefix tailTrace_3299605
  have hstable : (prefixWord ++ tailWord_3299605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299605).length < 2 ^ (prefixWord ++ tailWord_3299605).sum := by decide
  have hdescent : baseEnd_3299605 < baseStart_3299605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299607 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 5]
def baseStart_3299607 : Nat := 118140960795 + 3299607 * 2 ^ 59
def prefixEnd_3299607 : Nat := 4983230072969 + 3 ^ 40 * 3299607 * 2
def baseEnd_3299607 : Nat := 376507635986661556919531

theorem tailTrace_3299607 : CollatzResearch.WordTrace tailWord_3299607 prefixEnd_3299607 376507635986661556919531 := by
  unfold tailWord_3299607
  simp only [CollatzResearch.WordTrace]
  refine ⟨120346554157094841855953075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80231036104729894570635383 120346554157094841855953075)
  ·
    refine ⟨180519831235642262783929613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120346554157094841855953075 180519831235642262783929613)
    ·
      refine ⟨67694936713365848543973605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180519831235642262783929613 67694936713365848543973605)
      ·
        refine ⟨12692800633756096601995051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67694936713365848543973605 12692800633756096601995051)
        ·
          refine ⟨19039200950634144902992577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12692800633756096601995051 19039200950634144902992577)
          ·
            refine ⟨14279400712975608677244433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19039200950634144902992577 14279400712975608677244433)
            ·
              refine ⟨10709550534731706507933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14279400712975608677244433 10709550534731706507933325)
              ·
                refine ⟨4016081450524389940474997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10709550534731706507933325 4016081450524389940474997)
                ·
                  refine ⟨376507635986661556919531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016081450524389940474997 376507635986661556919531)
                  ·
                    rfl

theorem cell22_3299607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 5].length) (baseStart_3299607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299607 prefixEnd_3299607 := by exact prefixLift 3299607
  have htrace : WordTrace (prefixWord ++ tailWord_3299607) baseStart_3299607 baseEnd_3299607 := by
    simpa [prefixWord, tailWord_3299607, baseEnd_3299607] using wordTrace_append hprefix tailTrace_3299607
  have hstable : (prefixWord ++ tailWord_3299607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299607).length < 2 ^ (prefixWord ++ tailWord_3299607).sum := by decide
  have hdescent : baseEnd_3299607 < baseStart_3299607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299635 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 8]
def baseStart_3299635 : Nat := 118140960795 + 3299635 * 2 ^ 59
def prefixEnd_3299635 : Nat := 4983230072969 + 3 ^ 40 * 3299635 * 2
def baseEnd_3299635 : Nat := 376510830977400643686169

theorem tailTrace_3299635 : CollatzResearch.WordTrace tailWord_3299635 prefixEnd_3299635 376510830977400643686169 := by
  unfold tailWord_3299635
  simp only [CollatzResearch.WordTrace]
  refine ⟨120347575400993402637972359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80231716933995601758648239 120347575400993402637972359)
  ·
    refine ⟨180521363101490103956958539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120347575400993402637972359 180521363101490103956958539)
    ·
      refine ⟨270782044652235155935437809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180521363101490103956958539 270782044652235155935437809)
      ·
        refine ⟨203086533489176366951578357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270782044652235155935437809 203086533489176366951578357)
        ·
          refine ⟨19039362514610284401710471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203086533489176366951578357 19039362514610284401710471)
          ·
            refine ⟨28559043771915426602565707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19039362514610284401710471 28559043771915426602565707)
            ·
              refine ⟨42838565657873139903848561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28559043771915426602565707 42838565657873139903848561)
              ·
                refine ⟨32128924243404854927886421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42838565657873139903848561 32128924243404854927886421)
                ·
                  refine ⟨376510830977400643686169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32128924243404854927886421 376510830977400643686169)
                  ·
                    rfl

theorem cell22_3299635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_3299635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299635 prefixEnd_3299635 := by exact prefixLift 3299635
  have htrace : WordTrace (prefixWord ++ tailWord_3299635) baseStart_3299635 baseEnd_3299635 := by
    simpa [prefixWord, tailWord_3299635, baseEnd_3299635] using wordTrace_append hprefix tailTrace_3299635
  have hstable : (prefixWord ++ tailWord_3299635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299635).length < 2 ^ (prefixWord ++ tailWord_3299635).sum := by decide
  have hdescent : baseEnd_3299635 < baseStart_3299635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299754 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_3299754 : Nat := 118140960795 + 3299754 * 2 ^ 59
def prefixEnd_3299754 : Nat := 4983230072969 + 3 ^ 40 * 3299754 * 2
def baseEnd_3299754 : Nat := 376524409688041762444381

theorem tailTrace_3299754 : CollatzResearch.WordTrace tailWord_3299754 prefixEnd_3299754 376524409688041762444381 := by
  unfold tailWord_3299754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30087978921890571490388579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80234610458374857307702877 30087978921890571490388579)
  ·
    refine ⟨45131968382835857235582869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30087978921890571490388579 45131968382835857235582869)
    ·
      refine ⟨2115561017945430807917947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45131968382835857235582869 2115561017945430807917947)
      ·
        refine ⟨3173341526918146211876921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115561017945430807917947 3173341526918146211876921)
        ·
          refine ⟨2380006145188609658907691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3173341526918146211876921 2380006145188609658907691)
          ·
            refine ⟨3570009217782914488361537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380006145188609658907691 3570009217782914488361537)
            ·
              refine ⟨2677506913337185866271153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570009217782914488361537 2677506913337185866271153)
              ·
                refine ⟨2008130185002889399703365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677506913337185866271153 2008130185002889399703365)
                ·
                  refine ⟨376524409688041762444381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008130185002889399703365 376524409688041762444381)
                  ·
                    rfl

theorem cell22_3299754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_3299754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299754 prefixEnd_3299754 := by exact prefixLift 3299754
  have htrace : WordTrace (prefixWord ++ tailWord_3299754) baseStart_3299754 baseEnd_3299754 := by
    simpa [prefixWord, tailWord_3299754, baseEnd_3299754] using wordTrace_append hprefix tailTrace_3299754
  have hstable : (prefixWord ++ tailWord_3299754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299754).length < 2 ^ (prefixWord ++ tailWord_3299754).sum := by decide
  have hdescent : baseEnd_3299754 < baseStart_3299754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299810 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_3299810 : Nat := 118140960795 + 3299810 * 2 ^ 59
def prefixEnd_3299810 : Nat := 4983230072969 + 3 ^ 40 * 3299810 * 2
def baseEnd_3299810 : Nat := 376530799669519935977657

theorem tailTrace_3299810 : CollatzResearch.WordTrace tailWord_3299810 prefixEnd_3299810 376530799669519935977657 := by
  unfold tailWord_3299810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088489543839851881398221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80235972116906271683728589 30088489543839851881398221)
  ·
    refine ⟨11283183578939944455524333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30088489543839851881398221 11283183578939944455524333)
    ·
      refine ⟨4231193842102479170821625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11283183578939944455524333 4231193842102479170821625)
      ·
        refine ⟨3173395381576859378116219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231193842102479170821625 3173395381576859378116219)
        ·
          refine ⟨4760093072365289067174329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173395381576859378116219 4760093072365289067174329)
          ·
            refine ⟨3570069804273966800380747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4760093072365289067174329 3570069804273966800380747)
            ·
              refine ⟨5355104706410950200571121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570069804273966800380747 5355104706410950200571121)
              ·
                refine ⟨4016328529808212650428341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5355104706410950200571121 4016328529808212650428341)
                ·
                  refine ⟨376530799669519935977657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016328529808212650428341 376530799669519935977657)
                  ·
                    rfl

theorem cell22_3299810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_3299810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299810 prefixEnd_3299810 := by exact prefixLift 3299810
  have htrace : WordTrace (prefixWord ++ tailWord_3299810) baseStart_3299810 baseEnd_3299810 := by
    simpa [prefixWord, tailWord_3299810, baseEnd_3299810] using wordTrace_append hprefix tailTrace_3299810
  have hstable : (prefixWord ++ tailWord_3299810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299810).length < 2 ^ (prefixWord ++ tailWord_3299810).sum := by decide
  have hdescent : baseEnd_3299810 < baseStart_3299810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299819 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 4, 3]
def baseStart_3299819 : Nat := 118140960795 + 3299819 * 2 ^ 59
def prefixEnd_3299819 : Nat := 4983230072969 + 3 ^ 40 * 3299819 * 2
def baseEnd_3299819 : Nat := 1129595479892486784457943

theorem tailTrace_3299819 : CollatzResearch.WordTrace tailWord_3299819 prefixEnd_3299819 1129595479892486784457943 := by
  unfold tailWord_3299819
  simp only [CollatzResearch.WordTrace]
  refine ⟨120354286432326802062670511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80236190954884534708447007 120354286432326802062670511)
  ·
    refine ⟨180531429648490203094005767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120354286432326802062670511 180531429648490203094005767)
    ·
      refine ⟨270797144472735304641008651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180531429648490203094005767 270797144472735304641008651)
      ·
        refine ⟨406195716709102956961512977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270797144472735304641008651 406195716709102956961512977)
        ·
          refine ⟨304646787531827217721134733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406195716709102956961512977 304646787531827217721134733)
          ·
            refine ⟨114242545324435206645425525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304646787531827217721134733 114242545324435206645425525)
            ·
              refine ⟨10710238624165800623008643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114242545324435206645425525 10710238624165800623008643)
              ·
                refine ⟨16065357936248700934512965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10710238624165800623008643 16065357936248700934512965)
                ·
                  refine ⟨3012254613046631425221181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16065357936248700934512965 3012254613046631425221181)
                  ·
                    refine ⟨1129595479892486784457943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012254613046631425221181 1129595479892486784457943)
                    ·
                      rfl

theorem cell22_3299819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 3].length) (baseStart_3299819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299819 prefixEnd_3299819 := by exact prefixLift 3299819
  have htrace : WordTrace (prefixWord ++ tailWord_3299819) baseStart_3299819 baseEnd_3299819 := by
    simpa [prefixWord, tailWord_3299819, baseEnd_3299819] using wordTrace_append hprefix tailTrace_3299819
  have hstable : (prefixWord ++ tailWord_3299819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299819).length < 2 ^ (prefixWord ++ tailWord_3299819).sum := by decide
  have hdescent : baseEnd_3299819 < baseStart_3299819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299821 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3299821 : Nat := 118140960795 + 3299821 * 2 ^ 59
def prefixEnd_3299821 : Nat := 4983230072969 + 3 ^ 40 * 3299821 * 2
def baseEnd_3299821 : Nat := 376532054844453148635979

theorem tailTrace_3299821 : CollatzResearch.WordTrace tailWord_3299821 prefixEnd_3299821 376532054844453148635979 := by
  unfold tailWord_3299821
  simp only [CollatzResearch.WordTrace]
  refine ⟨120354359378319556404243317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80236239585546370936162211 120354359378319556404243317)
  ·
    refine ⟨11283221191717458412897811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120354359378319556404243317 11283221191717458412897811)
    ·
      refine ⟨16924831787576187619346717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11283221191717458412897811 16924831787576187619346717)
      ·
        refine ⟨6346811920341070357255019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16924831787576187619346717 6346811920341070357255019)
        ·
          refine ⟨9520217880511605535882529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346811920341070357255019 9520217880511605535882529)
          ·
            refine ⟨7140163410383704151911897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9520217880511605535882529 7140163410383704151911897)
            ·
              refine ⟨5355122557787778113933923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7140163410383704151911897 5355122557787778113933923)
              ·
                refine ⟨8032683836681667170900885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355122557787778113933923 8032683836681667170900885)
                ·
                  refine ⟨376532054844453148635979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8032683836681667170900885 376532054844453148635979)
                  ·
                    rfl

theorem cell22_3299821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3299821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299821 prefixEnd_3299821 := by exact prefixLift 3299821
  have htrace : WordTrace (prefixWord ++ tailWord_3299821) baseStart_3299821 baseEnd_3299821 := by
    simpa [prefixWord, tailWord_3299821, baseEnd_3299821] using wordTrace_append hprefix tailTrace_3299821
  have hstable : (prefixWord ++ tailWord_3299821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299821).length < 2 ^ (prefixWord ++ tailWord_3299821).sum := by decide
  have hdescent : baseEnd_3299821 < baseStart_3299821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299832 : List Nat := [2, 1, 2, 1, 1, 4, 2, 9]
def baseStart_3299832 : Nat := 118140960795 + 3299832 * 2 ^ 59
def prefixEnd_3299832 : Nat := 4983230072969 + 3 ^ 40 * 3299832 * 2
def baseEnd_3299832 : Nat := 125511103339795453764767

theorem tailTrace_3299832 : CollatzResearch.WordTrace tailWord_3299832 prefixEnd_3299832 125511103339795453764767 := by
  unfold tailWord_3299832
  simp only [CollatzResearch.WordTrace]
  refine ⟨60177380290639852641446875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80236507054186470188595833 60177380290639852641446875)
  ·
    refine ⟨90266070435959778962170313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60177380290639852641446875 90266070435959778962170313)
    ·
      refine ⟨67699552826969834221627735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90266070435959778962170313 67699552826969834221627735)
      ·
        refine ⟨101549329240454751332441603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67699552826969834221627735 101549329240454751332441603)
        ·
          refine ⟨152323993860682126998662405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101549329240454751332441603 152323993860682126998662405)
          ·
            refine ⟨28560748848877898812249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152323993860682126998662405 28560748848877898812249201)
            ·
              refine ⟨21420561636658424109186901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28560748848877898812249201 21420561636658424109186901)
              ·
                refine ⟨125511103339795453764767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21420561636658424109186901 125511103339795453764767)
                ·
                  rfl

theorem cell22_3299832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_3299832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299832 prefixEnd_3299832 := by exact prefixLift 3299832
  have htrace : WordTrace (prefixWord ++ tailWord_3299832) baseStart_3299832 baseEnd_3299832 := by
    simpa [prefixWord, tailWord_3299832, baseEnd_3299832] using wordTrace_append hprefix tailTrace_3299832
  have hstable : (prefixWord ++ tailWord_3299832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299832).length < 2 ^ (prefixWord ++ tailWord_3299832).sum := by decide
  have hdescent : baseEnd_3299832 < baseStart_3299832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299939 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 6]
def baseStart_3299939 : Nat := 118140960795 + 3299939 * 2 ^ 59
def prefixEnd_3299939 : Nat := 4983230072969 + 3 ^ 40 * 3299939 * 2
def baseEnd_3299939 : Nat := 376545519448282157152525

theorem tailTrace_3299939 : CollatzResearch.WordTrace tailWord_3299939 prefixEnd_3299939 376545519448282157152525 := by
  unfold tailWord_3299939
  simp only [CollatzResearch.WordTrace]
  refine ⟨120358663191892062557038871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80239108794594708371359247 120358663191892062557038871)
  ·
    refine ⟨180537994787838093835558307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120358663191892062557038871 180537994787838093835558307)
    ·
      refine ⟨270806992181757140753337461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180537994787838093835558307 270806992181757140753337461)
      ·
        refine ⟨25388155517039731945625387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270806992181757140753337461 25388155517039731945625387)
        ·
          refine ⟨38082233275559597918438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25388155517039731945625387 38082233275559597918438081)
          ·
            refine ⟨28561674956669698438828561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38082233275559597918438081 28561674956669698438828561)
            ·
              refine ⟨21421256217502273829121421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28561674956669698438828561 21421256217502273829121421)
              ·
                refine ⟨8032971081563352685920533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21421256217502273829121421 8032971081563352685920533)
                ·
                  refine ⟨376545519448282157152525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8032971081563352685920533 376545519448282157152525)
                  ·
                    rfl

theorem cell22_3299939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_3299939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299939 prefixEnd_3299939 := by exact prefixLift 3299939
  have htrace : WordTrace (prefixWord ++ tailWord_3299939) baseStart_3299939 baseEnd_3299939 := by
    simpa [prefixWord, tailWord_3299939, baseEnd_3299939] using wordTrace_append hprefix tailTrace_3299939
  have hstable : (prefixWord ++ tailWord_3299939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299939).length < 2 ^ (prefixWord ++ tailWord_3299939).sum := by decide
  have hdescent : baseEnd_3299939 < baseStart_3299939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3299973 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 4]
def baseStart_3299973 : Nat := 118140960795 + 3299973 * 2 ^ 59
def prefixEnd_3299973 : Nat := 4983230072969 + 3 ^ 40 * 3299973 * 2
def baseEnd_3299973 : Nat := 376549399079893905369157

theorem tailTrace_3299973 : CollatzResearch.WordTrace tailWord_3299973 prefixEnd_3299973 376549399079893905369157 := by
  unfold tailWord_3299973
  simp only [CollatzResearch.WordTrace]
  refine ⟨120359903273768886363776573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80239935515845924242517715 120359903273768886363776573)
  ·
    refine ⟨45134963727663332386416215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120359903273768886363776573 45134963727663332386416215)
    ·
      refine ⟨67702445591494998579624323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45134963727663332386416215 67702445591494998579624323)
      ·
        refine ⟨101553668387242497869436485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67702445591494998579624323 101553668387242497869436485)
        ·
          refine ⟨19041312822607968350519341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101553668387242497869436485 19041312822607968350519341)
          ·
            refine ⟨7140492308477988131444753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19041312822607968350519341 7140492308477988131444753)
            ·
              refine ⟨5355369231358491098583565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7140492308477988131444753 5355369231358491098583565)
              ·
                refine ⟨2008263461759434161968837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5355369231358491098583565 2008263461759434161968837)
                ·
                  refine ⟨376549399079893905369157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008263461759434161968837 376549399079893905369157)
                  ·
                    rfl

theorem cell22_3299973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_3299973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3299973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3299973 prefixEnd_3299973 := by exact prefixLift 3299973
  have htrace : WordTrace (prefixWord ++ tailWord_3299973) baseStart_3299973 baseEnd_3299973 := by
    simpa [prefixWord, tailWord_3299973, baseEnd_3299973] using wordTrace_append hprefix tailTrace_3299973
  have hstable : (prefixWord ++ tailWord_3299973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3299973).length < 2 ^ (prefixWord ++ tailWord_3299973).sum := by decide
  have hdescent : baseEnd_3299973 < baseStart_3299973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3299973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300046 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3300046 : Nat := 118140960795 + 3300046 * 2 ^ 59
def prefixEnd_3300046 : Nat := 4983230072969 + 3 ^ 40 * 3300046 * 2
def baseEnd_3300046 : Nat := 376557728877177953010749

theorem tailTrace_3300046 : CollatzResearch.WordTrace tailWord_3300046 prefixEnd_3300046 376557728877177953010749 := by
  unfold tailWord_3300046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045320725313052478897999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80241710535002946554122661 15045320725313052478897999)
  ·
    refine ⟨22567981087969578718346999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045320725313052478897999 22567981087969578718346999)
    ·
      refine ⟨33851971631954368077520499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22567981087969578718346999 33851971631954368077520499)
      ·
        refine ⟨50777957447931552116280749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33851971631954368077520499 50777957447931552116280749)
        ·
          refine ⟨19041734042974332043605281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50777957447931552116280749 19041734042974332043605281)
          ·
            refine ⟨14281300532230749032703961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19041734042974332043605281 14281300532230749032703961)
            ·
              refine ⟨10710975399173061774527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14281300532230749032703961 10710975399173061774527971)
              ·
                refine ⟨16066463098759592661791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10710975399173061774527971 16066463098759592661791957)
                ·
                  refine ⟨376557728877177953010749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16066463098759592661791957 376557728877177953010749)
                  ·
                    rfl

theorem cell22_3300046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3300046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300046 prefixEnd_3300046 := by exact prefixLift 3300046
  have htrace : WordTrace (prefixWord ++ tailWord_3300046) baseStart_3300046 baseEnd_3300046 := by
    simpa [prefixWord, tailWord_3300046, baseEnd_3300046] using wordTrace_append hprefix tailTrace_3300046
  have hstable : (prefixWord ++ tailWord_3300046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300046).length < 2 ^ (prefixWord ++ tailWord_3300046).sum := by decide
  have hdescent : baseEnd_3300046 < baseStart_3300046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300063 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 5]
def baseStart_3300063 : Nat := 118140960795 + 3300063 * 2 ^ 59
def prefixEnd_3300063 : Nat := 4983230072969 + 3 ^ 40 * 3300063 * 2
def baseEnd_3300063 : Nat := 376559668692983827119065

theorem tailTrace_3300063 : CollatzResearch.WordTrace tailWord_3300063 prefixEnd_3300063 376559668692983827119065 := by
  unfold tailWord_3300063
  simp only [CollatzResearch.WordTrace]
  refine ⟨120363185843442831734552843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80242123895628554489701895 120363185843442831734552843)
  ·
    refine ⟨180544778765164247601829265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120363185843442831734552843 180544778765164247601829265)
    ·
      refine ⟨135408584073873185701371949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180544778765164247601829265 135408584073873185701371949)
      ·
        refine ⟨50778219027702444638014481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135408584073873185701371949 50778219027702444638014481)
        ·
          refine ⟨38083664270776833478510861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50778219027702444638014481 38083664270776833478510861)
          ·
            refine ⟨14281374101541312554441573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38083664270776833478510861 14281374101541312554441573)
            ·
              refine ⟨2677757644038996103957795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14281374101541312554441573 2677757644038996103957795)
              ·
                refine ⟨4016636466058494155936693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677757644038996103957795 4016636466058494155936693)
                ·
                  refine ⟨376559668692983827119065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016636466058494155936693 376559668692983827119065)
                  ·
                    rfl

theorem cell22_3300063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 5].length) (baseStart_3300063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300063 prefixEnd_3300063 := by exact prefixLift 3300063
  have htrace : WordTrace (prefixWord ++ tailWord_3300063) baseStart_3300063 baseEnd_3300063 := by
    simpa [prefixWord, tailWord_3300063, baseEnd_3300063] using wordTrace_append hprefix tailTrace_3300063
  have hstable : (prefixWord ++ tailWord_3300063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300063).length < 2 ^ (prefixWord ++ tailWord_3300063).sum := by decide
  have hdescent : baseEnd_3300063 < baseStart_3300063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300106 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3300106 : Nat := 118140960795 + 3300106 * 2 ^ 59
def prefixEnd_3300106 : Nat := 4983230072969 + 3 ^ 40 * 3300106 * 2
def baseEnd_3300106 : Nat := 1129693725857713702532063

theorem tailTrace_3300106 : CollatzResearch.WordTrace tailWord_3300106 prefixEnd_3300106 1129693725857713702532063 := by
  unfold tailWord_3300106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091188545571762519592043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80243169454858033385578781 30091188545571762519592043)
  ·
    refine ⟨45136782818357643779388065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30091188545571762519592043 45136782818357643779388065)
    ·
      refine ⟨33852587113768232834541049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45136782818357643779388065 33852587113768232834541049)
      ·
        refine ⟨25389440335326174625905787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33852587113768232834541049 25389440335326174625905787)
        ·
          refine ⟨38084160502989261938858681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25389440335326174625905787 38084160502989261938858681)
          ·
            refine ⟨28563120377241946454144011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38084160502989261938858681 28563120377241946454144011)
            ·
              refine ⟨42844680565862919681216017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28563120377241946454144011 42844680565862919681216017)
              ·
                refine ⟨32133510424397189760912013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42844680565862919681216017 32133510424397189760912013)
                ·
                  refine ⟨12050066409148946160342005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32133510424397189760912013 12050066409148946160342005)
                  ·
                    refine ⟨1129693725857713702532063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12050066409148946160342005 1129693725857713702532063)
                    ·
                      rfl

theorem cell22_3300106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3300106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300106 prefixEnd_3300106 := by exact prefixLift 3300106
  have htrace : WordTrace (prefixWord ++ tailWord_3300106) baseStart_3300106 baseEnd_3300106 := by
    simpa [prefixWord, tailWord_3300106, baseEnd_3300106] using wordTrace_append hprefix tailTrace_3300106
  have hstable : (prefixWord ++ tailWord_3300106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300106).length < 2 ^ (prefixWord ++ tailWord_3300106).sum := by decide
  have hdescent : baseEnd_3300106 < baseStart_3300106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300125 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 6]
def baseStart_3300125 : Nat := 118140960795 + 3300125 * 2 ^ 59
def prefixEnd_3300125 : Nat := 4983230072969 + 3 ^ 40 * 3300125 * 2
def baseEnd_3300125 : Nat := 376566743315334662102335

theorem tailTrace_3300125 : CollatzResearch.WordTrace tailWord_3300125 prefixEnd_3300125 376566743315334662102335 := by
  unfold tailWord_3300125
  simp only [CollatzResearch.WordTrace]
  refine ⟨120365447169218216323309829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80243631446145477548873219 120365447169218216323309829)
  ·
    refine ⟨22568521344228415560620593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120365447169218216323309829 22568521344228415560620593)
    ·
      refine ⟨16926391008171311670465445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22568521344228415560620593 16926391008171311670465445)
      ·
        refine ⟨3173698314032120938212271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16926391008171311670465445 3173698314032120938212271)
        ·
          refine ⟨4760547471048181407318407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173698314032120938212271 4760547471048181407318407)
          ·
            refine ⟨7140821206572272110977611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760547471048181407318407 7140821206572272110977611)
            ·
              refine ⟨10711231809858408166466417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140821206572272110977611 10711231809858408166466417)
              ·
                refine ⟨8033423857393806124849813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10711231809858408166466417 8033423857393806124849813)
                ·
                  refine ⟨376566743315334662102335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8033423857393806124849813 376566743315334662102335)
                  ·
                    rfl

theorem cell22_3300125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_3300125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300125 prefixEnd_3300125 := by exact prefixLift 3300125
  have htrace : WordTrace (prefixWord ++ tailWord_3300125) baseStart_3300125 baseEnd_3300125 := by
    simpa [prefixWord, tailWord_3300125, baseEnd_3300125] using wordTrace_append hprefix tailTrace_3300125
  have hstable : (prefixWord ++ tailWord_3300125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300125).length < 2 ^ (prefixWord ++ tailWord_3300125).sum := by decide
  have hdescent : baseEnd_3300125 < baseStart_3300125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300142 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3300142 : Nat := 118140960795 + 3300142 * 2 ^ 59
def prefixEnd_3300142 : Nat := 4983230072969 + 3 ^ 40 * 3300142 * 2
def baseEnd_3300142 : Nat := 376568683131140536210651

theorem tailTrace_3300142 : CollatzResearch.WordTrace tailWord_3300142 prefixEnd_3300142 376568683131140536210651 := by
  unfold tailWord_3300142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045758401269578528334835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80244044806771085484452453 15045758401269578528334835)
  ·
    refine ⟨22568637601904367792502253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045758401269578528334835 22568637601904367792502253)
    ·
      refine ⟨8463239100714137922188345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22568637601904367792502253 8463239100714137922188345)
      ·
        refine ⟨6347429325535603441641259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463239100714137922188345 6347429325535603441641259)
        ·
          refine ⟨9521143988303405162461889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347429325535603441641259 9521143988303405162461889)
          ·
            refine ⟨7140857991227553871846417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9521143988303405162461889 7140857991227553871846417)
            ·
              refine ⟨5355643493420665403884813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7140857991227553871846417 5355643493420665403884813)
              ·
                refine ⟨2008366310032749526456805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5355643493420665403884813 2008366310032749526456805)
                ·
                  refine ⟨376568683131140536210651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008366310032749526456805 376568683131140536210651)
                  ·
                    rfl

theorem cell22_3300142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3300142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300142 prefixEnd_3300142 := by exact prefixLift 3300142
  have htrace : WordTrace (prefixWord ++ tailWord_3300142) baseStart_3300142 baseEnd_3300142 := by
    simpa [prefixWord, tailWord_3300142, baseEnd_3300142] using wordTrace_append hprefix tailTrace_3300142
  have hstable : (prefixWord ++ tailWord_3300142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300142).length < 2 ^ (prefixWord ++ tailWord_3300142).sum := by decide
  have hdescent : baseEnd_3300142 < baseStart_3300142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300228 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3300228 : Nat := 118140960795 + 3300228 * 2 ^ 59
def prefixEnd_3300228 : Nat := 4983230072969 + 3 ^ 40 * 3300228 * 2
def baseEnd_3300228 : Nat := 1129735488950946050981689

theorem tailTrace_3300228 : CollatzResearch.WordTrace tailWord_3300228 prefixEnd_3300228 1129735488950946050981689 := by
  unfold tailWord_3300228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60184601943922532457154669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80246135925230043276206225 60184601943922532457154669)
  ·
    refine ⟨22569225728970949671433001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60184601943922532457154669 22569225728970949671433001)
    ·
      refine ⟨16926919296728212253574751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22569225728970949671433001 16926919296728212253574751)
      ·
        refine ⟨25390378945092318380362127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16926919296728212253574751 25390378945092318380362127)
        ·
          refine ⟨38085568417638477570543191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25390378945092318380362127 38085568417638477570543191)
          ·
            refine ⟨57128352626457716355814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38085568417638477570543191 57128352626457716355814787)
            ·
              refine ⟨85692528939686574533722181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57128352626457716355814787 85692528939686574533722181)
              ·
                refine ⟨16067349176191232725072909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85692528939686574533722181 16067349176191232725072909)
                ·
                  refine ⟨6025255941071712271902341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16067349176191232725072909 6025255941071712271902341)
                  ·
                    refine ⟨1129735488950946050981689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025255941071712271902341 1129735488950946050981689)
                    ·
                      rfl

theorem cell22_3300228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3300228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300228 prefixEnd_3300228 := by exact prefixLift 3300228
  have htrace : WordTrace (prefixWord ++ tailWord_3300228) baseStart_3300228 baseEnd_3300228 := by
    simpa [prefixWord, tailWord_3300228, baseEnd_3300228] using wordTrace_append hprefix tailTrace_3300228
  have hstable : (prefixWord ++ tailWord_3300228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300228).length < 2 ^ (prefixWord ++ tailWord_3300228).sum := by decide
  have hdescent : baseEnd_3300228 < baseStart_3300228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300232 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_3300232 : Nat := 118140960795 + 3300232 * 2 ^ 59
def prefixEnd_3300232 : Nat := 4983230072969 + 3 ^ 40 * 3300232 * 2
def baseEnd_3300232 : Nat := 376578952744230457960559

theorem tailTrace_3300232 : CollatzResearch.WordTrace tailWord_3300232 prefixEnd_3300232 376578952744230457960559 := by
  unfold tailWord_3300232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60184674889915286798727475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80246233186553715731636633 60184674889915286798727475)
  ·
    refine ⟨90277012334872930198091213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60184674889915286798727475 90277012334872930198091213)
    ·
      refine ⟨33853879625577348824284205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90277012334872930198091213 33853879625577348824284205)
      ·
        refine ⟨12695204859591505809106577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33853879625577348824284205 12695204859591505809106577)
        ·
          refine ⟨9521403644693629356829933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12695204859591505809106577 9521403644693629356829933)
          ·
            refine ⟨3570526366760111008811225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9521403644693629356829933 3570526366760111008811225)
            ·
              refine ⟨2677894775070083256608419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570526366760111008811225 2677894775070083256608419)
              ·
                refine ⟨4016842162605124884912629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677894775070083256608419 4016842162605124884912629)
                ·
                  refine ⟨376578952744230457960559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016842162605124884912629 376578952744230457960559)
                  ·
                    rfl

theorem cell22_3300232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_3300232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300232 prefixEnd_3300232 := by exact prefixLift 3300232
  have htrace : WordTrace (prefixWord ++ tailWord_3300232) baseStart_3300232 baseEnd_3300232 := by
    simpa [prefixWord, tailWord_3300232, baseEnd_3300232] using wordTrace_append hprefix tailTrace_3300232
  have hstable : (prefixWord ++ tailWord_3300232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300232).length < 2 ^ (prefixWord ++ tailWord_3300232).sum := by decide
  have hdescent : baseEnd_3300232 < baseStart_3300232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300245 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3300245 : Nat := 118140960795 + 3300245 * 2 ^ 59
def prefixEnd_3300245 : Nat := 4983230072969 + 3 ^ 40 * 3300245 * 2
def baseEnd_3300245 : Nat := 1129741308398363673306637

theorem tailTrace_3300245 : CollatzResearch.WordTrace tailWord_3300245 prefixEnd_3300245 1129741308398363673306637 := by
  unfold tailWord_3300245
  simp only [CollatzResearch.WordTrace]
  refine ⟨120369823928783476817678189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80246549285855651211785459 120369823928783476817678189)
  ·
    refine ⟨45138683973293803806629321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120369823928783476817678189 45138683973293803806629321)
    ·
      refine ⟨33854012979970352854971991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45138683973293803806629321 33854012979970352854971991)
      ·
        refine ⟨50781019469955529282457987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33854012979970352854971991 50781019469955529282457987)
        ·
          refine ⟨76171529204933293923686981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50781019469955529282457987 76171529204933293923686981)
          ·
            refine ⟨14282161725924992610691309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76171529204933293923686981 14282161725924992610691309)
            ·
              refine ⟨5355810647221872229009241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14282161725924992610691309 5355810647221872229009241)
              ·
                refine ⟨4016857985416404171756931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5355810647221872229009241 4016857985416404171756931)
                ·
                  refine ⟨6025286978124606257635397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4016857985416404171756931 6025286978124606257635397)
                  ·
                    refine ⟨1129741308398363673306637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025286978124606257635397 1129741308398363673306637)
                    ·
                      rfl

theorem cell22_3300245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3300245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300245 prefixEnd_3300245 := by exact prefixLift 3300245
  have htrace : WordTrace (prefixWord ++ tailWord_3300245) baseStart_3300245 baseEnd_3300245 := by
    simpa [prefixWord, tailWord_3300245, baseEnd_3300245] using wordTrace_append hprefix tailTrace_3300245
  have hstable : (prefixWord ++ tailWord_3300245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300245).length < 2 ^ (prefixWord ++ tailWord_3300245).sum := by decide
  have hdescent : baseEnd_3300245 < baseStart_3300245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300260 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_3300260 : Nat := 118140960795 + 3300260 * 2 ^ 59
def prefixEnd_3300260 : Nat := 4983230072969 + 3 ^ 40 * 3300260 * 2
def baseEnd_3300260 : Nat := 376582147734969544727197

theorem tailTrace_3300260 : CollatzResearch.WordTrace tailWord_3300260 prefixEnd_3300260 376582147734969544727197 := by
  unfold tailWord_3300260
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185185511864567189737117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80246914015819422919649489 60185185511864567189737117)
  ·
    refine ⟨22569444566949212696151419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60185185511864567189737117 22569444566949212696151419)
    ·
      refine ⟨33854166850423819044227129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22569444566949212696151419 33854166850423819044227129)
      ·
        refine ⟨25390625137817864283170347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33854166850423819044227129 25390625137817864283170347)
        ·
          refine ⟨38085937706726796424755521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25390625137817864283170347 38085937706726796424755521)
          ·
            refine ⟨28564453280045097318566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38085937706726796424755521 28564453280045097318566641)
            ·
              refine ⟨21423339960033822988924981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28564453280045097318566641 21423339960033822988924981)
              ·
                refine ⟨2008438121253170905211717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21423339960033822988924981 2008438121253170905211717)
                ·
                  refine ⟨376582147734969544727197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008438121253170905211717 376582147734969544727197)
                  ·
                    rfl

theorem cell22_3300260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_3300260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300260 prefixEnd_3300260 := by exact prefixLift 3300260
  have htrace : WordTrace (prefixWord ++ tailWord_3300260) baseStart_3300260 baseEnd_3300260 := by
    simpa [prefixWord, tailWord_3300260, baseEnd_3300260] using wordTrace_append hprefix tailTrace_3300260
  have hstable : (prefixWord ++ tailWord_3300260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300260).length < 2 ^ (prefixWord ++ tailWord_3300260).sum := by decide
  have hdescent : baseEnd_3300260 < baseStart_3300260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300288 : List Nat := [2, 1, 1, 2, 3, 3, 3, 7]
def baseStart_3300288 : Nat := 118140960795 + 3300288 * 2 ^ 59
def prefixEnd_3300288 : Nat := 4983230072969 + 3 ^ 40 * 3300288 * 2
def baseEnd_3300288 : Nat := 125528447575236210497945

theorem tailTrace_3300288 : CollatzResearch.WordTrace tailWord_3300288 prefixEnd_3300288 125528447575236210497945 := by
  unfold tailWord_3300288
  simp only [CollatzResearch.WordTrace]
  refine ⟨60185696133813847580746759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80247594845085130107662345 60185696133813847580746759)
  ·
    refine ⟨90278544200720771371120139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60185696133813847580746759 90278544200720771371120139)
    ·
      refine ⟨135417816301081157056680209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90278544200720771371120139 135417816301081157056680209)
      ·
        refine ⟨101563362225810867792510157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135417816301081157056680209 101563362225810867792510157)
        ·
          refine ⟨38086260834679075422191309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101563362225810867792510157 38086260834679075422191309)
          ·
            refine ⟨14282347813004653283321741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38086260834679075422191309 14282347813004653283321741)
            ·
              refine ⟨5355880429876744981245653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14282347813004653283321741 5355880429876744981245653)
              ·
                refine ⟨125528447575236210497945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5355880429876744981245653 125528447575236210497945)
                ·
                  rfl

theorem cell22_3300288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_3300288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300288 prefixEnd_3300288 := by exact prefixLift 3300288
  have htrace : WordTrace (prefixWord ++ tailWord_3300288) baseStart_3300288 baseEnd_3300288 := by
    simpa [prefixWord, tailWord_3300288, baseEnd_3300288] using wordTrace_append hprefix tailTrace_3300288
  have hstable : (prefixWord ++ tailWord_3300288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300288).length < 2 ^ (prefixWord ++ tailWord_3300288).sum := by decide
  have hdescent : baseEnd_3300288 < baseStart_3300288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300337 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_3300337 : Nat := 118140960795 + 3300337 * 2 ^ 59
def prefixEnd_3300337 : Nat := 4983230072969 + 3 ^ 40 * 3300337 * 2
def baseEnd_3300337 : Nat := 1129772801878506100006355

theorem tailTrace_3300337 : CollatzResearch.WordTrace tailWord_3300337 prefixEnd_3300337 1129772801878506100006355 := by
  unfold tailWord_3300337
  simp only [CollatzResearch.WordTrace]
  refine ⟨120373179444450176530027265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80248786296300117686684843 120373179444450176530027265)
  ·
    refine ⟨90279884583337632397520449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120373179444450176530027265 90279884583337632397520449)
    ·
      refine ⟨67709913437503224298140337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90279884583337632397520449 67709913437503224298140337)
      ·
        refine ⟨50782435078127418223605253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67709913437503224298140337 50782435078127418223605253)
        ·
          refine ⟨9521706577148890916925985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50782435078127418223605253 9521706577148890916925985)
          ·
            refine ⟨7141279932861668187694489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9521706577148890916925985 7141279932861668187694489)
            ·
              refine ⟨5355959949646251140770867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141279932861668187694489 5355959949646251140770867)
              ·
                refine ⟨8033939924469376711156301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355959949646251140770867 8033939924469376711156301)
                ·
                  refine ⟨3012727471676016266683613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8033939924469376711156301 3012727471676016266683613)
                  ·
                    refine ⟨1129772801878506100006355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012727471676016266683613 1129772801878506100006355)
                    ·
                      rfl

theorem cell22_3300337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_3300337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300337 prefixEnd_3300337 := by exact prefixLift 3300337
  have htrace : WordTrace (prefixWord ++ tailWord_3300337) baseStart_3300337 baseEnd_3300337 := by
    simpa [prefixWord, tailWord_3300337, baseEnd_3300337] using wordTrace_append hprefix tailTrace_3300337
  have hstable : (prefixWord ++ tailWord_3300337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300337).length < 2 ^ (prefixWord ++ tailWord_3300337).sum := by decide
  have hdescent : baseEnd_3300337 < baseStart_3300337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300414 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3300414 : Nat := 118140960795 + 3300414 * 2 ^ 59
def prefixEnd_3300414 : Nat := 4983230072969 + 3 ^ 40 * 3300414 * 2
def baseEnd_3300414 : Nat := 1129799160552103565831119

theorem tailTrace_3300414 : CollatzResearch.WordTrace tailWord_3300414 prefixEnd_3300414 1129799160552103565831119 := by
  unfold tailWord_3300414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046998483146402335072537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80250658576780812453720197 15046998483146402335072537)
  ·
    refine ⟨11285248862359801751304403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15046998483146402335072537 11285248862359801751304403)
    ·
      refine ⟨16927873293539702626956605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11285248862359801751304403 16927873293539702626956605)
      ·
        refine ⟨6347952485077388485108727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16927873293539702626956605 6347952485077388485108727)
        ·
          refine ⟨9521928727616082727663091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347952485077388485108727 9521928727616082727663091)
          ·
            refine ⟨14282893091424124091494637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9521928727616082727663091 14282893091424124091494637)
            ·
              refine ⟨5356084909284046534310489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14282893091424124091494637 5356084909284046534310489)
              ·
                refine ⟨4017063681963034900732867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356084909284046534310489 4017063681963034900732867)
                ·
                  refine ⟨6025595522944552351099301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017063681963034900732867 6025595522944552351099301)
                  ·
                    refine ⟨1129799160552103565831119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025595522944552351099301 1129799160552103565831119)
                    ·
                      rfl

theorem cell22_3300414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3300414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300414 prefixEnd_3300414 := by exact prefixLift 3300414
  have htrace : WordTrace (prefixWord ++ tailWord_3300414) baseStart_3300414 baseEnd_3300414 := by
    simpa [prefixWord, tailWord_3300414, baseEnd_3300414] using wordTrace_append hprefix tailTrace_3300414
  have hstable : (prefixWord ++ tailWord_3300414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300414).length < 2 ^ (prefixWord ++ tailWord_3300414).sum := by decide
  have hdescent : baseEnd_3300414 < baseStart_3300414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300444 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3300444 : Nat := 118140960795 + 3300444 * 2 ^ 59
def prefixEnd_3300444 : Nat := 4983230072969 + 3 ^ 40 * 3300444 * 2
def baseEnd_3300444 : Nat := 1129809430165193487581027

theorem tailTrace_3300444 : CollatzResearch.WordTrace tailWord_3300444 prefixEnd_3300444 1129809430165193487581027 := by
  unfold tailWord_3300444
  simp only [CollatzResearch.WordTrace]
  refine ⟨60188541027531266902086193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80251388036708355869448257 60188541027531266902086193)
  ·
    refine ⟨45141405770648450176564645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60188541027531266902086193 45141405770648450176564645)
    ·
      refine ⟨8464013581996584408105871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45141405770648450176564645 8464013581996584408105871)
      ·
        refine ⟨12696020372994876612158807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8464013581996584408105871 12696020372994876612158807)
        ·
          refine ⟨19044030559492314918238211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12696020372994876612158807 19044030559492314918238211)
          ·
            refine ⟨28566045839238472377357317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19044030559492314918238211 28566045839238472377357317)
            ·
              refine ⟨5356133594857213570754497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28566045839238472377357317 5356133594857213570754497)
              ·
                refine ⟨4017100196142910178065873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356133594857213570754497 4017100196142910178065873)
                ·
                  refine ⟨3012825147107182633549405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4017100196142910178065873 3012825147107182633549405)
                  ·
                    refine ⟨1129809430165193487581027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012825147107182633549405 1129809430165193487581027)
                    ·
                      rfl

theorem cell22_3300444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3300444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300444 prefixEnd_3300444 := by exact prefixLift 3300444
  have htrace : WordTrace (prefixWord ++ tailWord_3300444) baseStart_3300444 baseEnd_3300444 := by
    simpa [prefixWord, tailWord_3300444, baseEnd_3300444] using wordTrace_append hprefix tailTrace_3300444
  have hstable : (prefixWord ++ tailWord_3300444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300444).length < 2 ^ (prefixWord ++ tailWord_3300444).sum := by decide
  have hdescent : baseEnd_3300444 < baseStart_3300444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300489 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_3300489 : Nat := 118140960795 + 3300489 * 2 ^ 59
def prefixEnd_3300489 : Nat := 4983230072969 + 3 ^ 40 * 3300489 * 2
def baseEnd_3300489 : Nat := 1129824834584828370205889

theorem tailTrace_3300489 : CollatzResearch.WordTrace tailWord_3300489 prefixEnd_3300489 1129824834584828370205889 := by
  unfold tailWord_3300489
  simp only [CollatzResearch.WordTrace]
  refine ⟨120378723339899506489560521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80252482226599670993040347 120378723339899506489560521)
  ·
    refine ⟨90284042504924629867170391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120378723339899506489560521 90284042504924629867170391)
    ·
      refine ⟨135426063757386944800755587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90284042504924629867170391 135426063757386944800755587)
      ·
        refine ⟨203139095636080417201133381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135426063757386944800755587 203139095636080417201133381)
        ·
          refine ⟨38088580431765078225212509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203139095636080417201133381 38088580431765078225212509)
          ·
            refine ⟨14283217661911904334454691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38088580431765078225212509 14283217661911904334454691)
            ·
              refine ⟨21424826492867856501682037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14283217661911904334454691 21424826492867856501682037)
              ·
                refine ⟨2008577483706361547032691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21424826492867856501682037 2008577483706361547032691)
                ·
                  refine ⟨3012866225559542320549037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008577483706361547032691 3012866225559542320549037)
                  ·
                    refine ⟨1129824834584828370205889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012866225559542320549037 1129824834584828370205889)
                    ·
                      rfl

theorem cell22_3300489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_3300489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300489 prefixEnd_3300489 := by exact prefixLift 3300489
  have htrace : WordTrace (prefixWord ++ tailWord_3300489) baseStart_3300489 baseEnd_3300489 := by
    simpa [prefixWord, tailWord_3300489, baseEnd_3300489] using wordTrace_append hprefix tailTrace_3300489
  have hstable : (prefixWord ++ tailWord_3300489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300489).length < 2 ^ (prefixWord ++ tailWord_3300489).sum := by decide
  have hdescent : baseEnd_3300489 < baseStart_3300489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300506 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_3300506 : Nat := 118140960795 + 3300506 * 2 ^ 59
def prefixEnd_3300506 : Nat := 4983230072969 + 3 ^ 40 * 3300506 * 2
def baseEnd_3300506 : Nat := 1129830654032245992530837

theorem tailTrace_3300506 : CollatzResearch.WordTrace tailWord_3300506 prefixEnd_3300506 1129830654032245992530837 := by
  unfold tailWord_3300506
  simp only [CollatzResearch.WordTrace]
  refine ⟨30094835845209479598232343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80252895587225278928619581 30094835845209479598232343)
  ·
    refine ⟨45142253767814219397348515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30094835845209479598232343 45142253767814219397348515)
    ·
      refine ⟨67713380651721329096022773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45142253767814219397348515 67713380651721329096022773)
      ·
        refine ⟨6348129436098874602752135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67713380651721329096022773 6348129436098874602752135)
        ·
          refine ⟨9522194154148311904128203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348129436098874602752135 9522194154148311904128203)
          ·
            refine ⟨14283291231222467856192305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9522194154148311904128203 14283291231222467856192305)
            ·
              refine ⟨10712468423416850892144229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14283291231222467856192305 10712468423416850892144229)
              ·
                refine ⟨2008587829390659542277043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10712468423416850892144229 2008587829390659542277043)
                ·
                  refine ⟨3012881744085989313415565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008587829390659542277043 3012881744085989313415565)
                  ·
                    refine ⟨1129830654032245992530837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012881744085989313415565 1129830654032245992530837)
                    ·
                      rfl

theorem cell22_3300506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_3300506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300506 prefixEnd_3300506 := by exact prefixLift 3300506
  have htrace : WordTrace (prefixWord ++ tailWord_3300506) baseStart_3300506 baseEnd_3300506 := by
    simpa [prefixWord, tailWord_3300506, baseEnd_3300506] using wordTrace_append hprefix tailTrace_3300506
  have hstable : (prefixWord ++ tailWord_3300506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300506).length < 2 ^ (prefixWord ++ tailWord_3300506).sum := by decide
  have hdescent : baseEnd_3300506 < baseStart_3300506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300515 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_3300515 : Nat := 118140960795 + 3300515 * 2 ^ 59
def prefixEnd_3300515 : Nat := 4983230072969 + 3 ^ 40 * 3300515 * 2
def baseEnd_3300515 : Nat := 1129833734916172969055809

theorem tailTrace_3300515 : CollatzResearch.WordTrace tailWord_3300515 prefixEnd_3300515 1129833734916172969055809 := by
  unfold tailWord_3300515
  simp only [CollatzResearch.WordTrace]
  refine ⟨120379671637805312930006999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80253114425203541953337999 120379671637805312930006999)
  ·
    refine ⟨180569507456707969395010499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120379671637805312930006999 180569507456707969395010499)
    ·
      refine ⟨270854261185061954092515749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180569507456707969395010499 270854261185061954092515749)
      ·
        refine ⟨50785173972199116392346703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270854261185061954092515749 50785173972199116392346703)
        ·
          refine ⟨76177760958298674588520055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50785173972199116392346703 76177760958298674588520055)
          ·
            refine ⟨114266641437448011882780083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76177760958298674588520055 114266641437448011882780083)
            ·
              refine ⟨171399962156172017824170125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114266641437448011882780083 171399962156172017824170125)
              ·
                refine ⟨64274985808564506684063797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171399962156172017824170125 64274985808564506684063797)
                ·
                  refine ⟨6025779919552922501630981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64274985808564506684063797 6025779919552922501630981)
                  ·
                    refine ⟨1129833734916172969055809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025779919552922501630981 1129833734916172969055809)
                    ·
                      rfl

theorem cell22_3300515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_3300515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300515 prefixEnd_3300515 := by exact prefixLift 3300515
  have htrace : WordTrace (prefixWord ++ tailWord_3300515) baseStart_3300515 baseEnd_3300515 := by
    simpa [prefixWord, tailWord_3300515, baseEnd_3300515] using wordTrace_append hprefix tailTrace_3300515
  have hstable : (prefixWord ++ tailWord_3300515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300515).length < 2 ^ (prefixWord ++ tailWord_3300515).sum := by decide
  have hdescent : baseEnd_3300515 < baseStart_3300515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300547 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 4]
def baseStart_3300547 : Nat := 118140960795 + 3300547 * 2 ^ 59
def prefixEnd_3300547 : Nat := 4983230072969 + 3 ^ 40 * 3300547 * 2
def baseEnd_3300547 : Nat := 376614896390045184085237

theorem tailTrace_3300547 : CollatzResearch.WordTrace tailWord_3300547 prefixEnd_3300547 376614896390045184085237 := by
  unfold tailWord_3300547
  simp only [CollatzResearch.WordTrace]
  refine ⟨120380838773689382395171895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80253892515792921596781263 120380838773689382395171895)
  ·
    refine ⟨180571258160534073592757843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120380838773689382395171895 180571258160534073592757843)
    ·
      refine ⟨270856887240801110389136765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180571258160534073592757843 270856887240801110389136765)
      ·
        refine ⟨101571332715300416395926287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270856887240801110389136765 101571332715300416395926287)
        ·
          refine ⟨152356999072950624593889431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101571332715300416395926287 152356999072950624593889431)
          ·
            refine ⟨228535498609425936890834147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152356999072950624593889431 228535498609425936890834147)
            ·
              refine ⟨342803247914138905336251221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228535498609425936890834147 342803247914138905336251221)
              ·
                refine ⟨2008612780746907648454597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 342803247914138905336251221 2008612780746907648454597)
                ·
                  refine ⟨376614896390045184085237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008612780746907648454597 376614896390045184085237)
                  ·
                    rfl

theorem cell22_3300547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 4].length) (baseStart_3300547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300547 prefixEnd_3300547 := by exact prefixLift 3300547
  have htrace : WordTrace (prefixWord ++ tailWord_3300547) baseStart_3300547 baseEnd_3300547 := by
    simpa [prefixWord, tailWord_3300547, baseEnd_3300547] using wordTrace_append hprefix tailTrace_3300547
  have hstable : (prefixWord ++ tailWord_3300547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300547).length < 2 ^ (prefixWord ++ tailWord_3300547).sum := by decide
  have hdescent : baseEnd_3300547 < baseStart_3300547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300557 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3300557 : Nat := 118140960795 + 3300557 * 2 ^ 59
def prefixEnd_3300557 : Nat := 4983230072969 + 3 ^ 40 * 3300557 * 2
def baseEnd_3300557 : Nat := 1129848112374498859505681

theorem tailTrace_3300557 : CollatzResearch.WordTrace tailWord_3300557 prefixEnd_3300557 1129848112374498859505681 := by
  unfold tailWord_3300557
  simp only [CollatzResearch.WordTrace]
  refine ⟨120381203503653154103035925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80254135669102102735357283 120381203503653154103035925)
  ·
    refine ⟨5642868914233741598579809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120381203503653154103035925 5642868914233741598579809)
    ·
      refine ⟨4232151685675306198934857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5642868914233741598579809 4232151685675306198934857)
      ·
        refine ⟨3174113764256479649201143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232151685675306198934857 3174113764256479649201143)
        ·
          refine ⟨4761170646384719473801715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174113764256479649201143 4761170646384719473801715)
          ·
            refine ⟨7141755969577079210702573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761170646384719473801715 7141755969577079210702573)
            ·
              refine ⟨2678158488591404704013465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141755969577079210702573 2678158488591404704013465)
              ·
                refine ⟨2008618866443553528010099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678158488591404704013465 2008618866443553528010099)
                ·
                  refine ⟨3012928299665330292015149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008618866443553528010099 3012928299665330292015149)
                  ·
                    refine ⟨1129848112374498859505681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012928299665330292015149 1129848112374498859505681)
                    ·
                      rfl

theorem cell22_3300557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3300557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300557 prefixEnd_3300557 := by exact prefixLift 3300557
  have htrace : WordTrace (prefixWord ++ tailWord_3300557) baseStart_3300557 baseEnd_3300557 := by
    simpa [prefixWord, tailWord_3300557, baseEnd_3300557] using wordTrace_append hprefix tailTrace_3300557
  have hstable : (prefixWord ++ tailWord_3300557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300557).length < 2 ^ (prefixWord ++ tailWord_3300557).sum := by decide
  have hdescent : baseEnd_3300557 < baseStart_3300557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300575 : List Nat := [1, 1, 2, 3, 2, 1, 3, 9]
def baseStart_3300575 : Nat := 118140960795 + 3300575 * 2 ^ 59
def prefixEnd_3300575 : Nat := 4983230072969 + 3 ^ 40 * 3300575 * 2
def baseEnd_3300575 : Nat := 125539363793594756950625

theorem tailTrace_3300575 : CollatzResearch.WordTrace tailWord_3300575 prefixEnd_3300575 125539363793594756950625 := by
  unfold tailWord_3300575
  simp only [CollatzResearch.WordTrace]
  refine ⟨120381860017587943177191179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80254573345058628784794119 120381860017587943177191179)
  ·
    refine ⟨180572790026381914765786769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120381860017587943177191179 180572790026381914765786769)
    ·
      refine ⟨135429592519786436074340077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180572790026381914765786769 135429592519786436074340077)
      ·
        refine ⟨50786097194919913527877529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135429592519786436074340077 50786097194919913527877529)
        ·
          refine ⟨38089572896189935145908147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50786097194919913527877529 38089572896189935145908147)
          ·
            refine ⟨57134359344284902718862221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38089572896189935145908147 57134359344284902718862221)
            ·
              refine ⟨21425384754106838519573333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57134359344284902718862221 21425384754106838519573333)
              ·
                refine ⟨125539363793594756950625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21425384754106838519573333 125539363793594756950625)
                ·
                  rfl

theorem cell22_3300575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 9].length) (baseStart_3300575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300575 prefixEnd_3300575 := by exact prefixLift 3300575
  have htrace : WordTrace (prefixWord ++ tailWord_3300575) baseStart_3300575 baseEnd_3300575 := by
    simpa [prefixWord, tailWord_3300575, baseEnd_3300575] using wordTrace_append hprefix tailTrace_3300575
  have hstable : (prefixWord ++ tailWord_3300575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300575).length < 2 ^ (prefixWord ++ tailWord_3300575).sum := by decide
  have hdescent : baseEnd_3300575 < baseStart_3300575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300583 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3300583 : Nat := 118140960795 + 3300583 * 2 ^ 59
def prefixEnd_3300583 : Nat := 4983230072969 + 3 ^ 40 * 3300583 * 2
def baseEnd_3300583 : Nat := 1129857012705843458355601

theorem tailTrace_3300583 : CollatzResearch.WordTrace tailWord_3300583 prefixEnd_3300583 1129857012705843458355601 := by
  unfold tailWord_3300583
  simp only [CollatzResearch.WordTrace]
  refine ⟨120382151801558960543482403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80254767867705973695654935 120382151801558960543482403)
  ·
    refine ⟨180573227702338440815223605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120382151801558960543482403 180573227702338440815223605)
    ·
      refine ⟨16928740097094228826427213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180573227702338440815223605 16928740097094228826427213)
      ·
        refine ⟨6348277536410335809910205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16928740097094228826427213 6348277536410335809910205)
        ·
          refine ⟨2380604076153875928716327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6348277536410335809910205 2380604076153875928716327)
          ·
            refine ⟨3570906114230813893074491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380604076153875928716327 3570906114230813893074491)
            ·
              refine ⟨5356359171346220839611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570906114230813893074491 5356359171346220839611737)
              ·
                refine ⟨4017269378509665629708803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356359171346220839611737 4017269378509665629708803)
                ·
                  refine ⟨6025904067764498444563205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017269378509665629708803 6025904067764498444563205)
                  ·
                    refine ⟨1129857012705843458355601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6025904067764498444563205 1129857012705843458355601)
                    ·
                      rfl

theorem cell22_3300583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3300583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300583 prefixEnd_3300583 := by exact prefixLift 3300583
  have htrace : WordTrace (prefixWord ++ tailWord_3300583) baseStart_3300583 baseEnd_3300583 := by
    simpa [prefixWord, tailWord_3300583, baseEnd_3300583] using wordTrace_append hprefix tailTrace_3300583
  have hstable : (prefixWord ++ tailWord_3300583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300583).length < 2 ^ (prefixWord ++ tailWord_3300583).sum := by decide
  have hdescent : baseEnd_3300583 < baseStart_3300583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300622 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3300622 : Nat := 118140960795 + 3300622 * 2 ^ 59
def prefixEnd_3300622 : Nat := 4983230072969 + 3 ^ 40 * 3300622 * 2
def baseEnd_3300622 : Nat := 1129870363202860356630481

theorem tailTrace_3300622 : CollatzResearch.WordTrace tailWord_3300622 prefixEnd_3300622 1129870363202860356630481 := by
  unfold tailWord_3300622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15047946781052208775519015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80255716165611780136101413 15047946781052208775519015)
  ·
    refine ⟨22571920171578313163278523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15047946781052208775519015 22571920171578313163278523)
    ·
      refine ⟨33857880257367469744917785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22571920171578313163278523 33857880257367469744917785)
      ·
        refine ⟨25393410193025602308688339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33857880257367469744917785 25393410193025602308688339)
        ·
          refine ⟨38090115289538403463032509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393410193025602308688339 38090115289538403463032509)
          ·
            refine ⟨14283793233576901298637191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38090115289538403463032509 14283793233576901298637191)
            ·
              refine ⟨21425689850365351947955787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14283793233576901298637191 21425689850365351947955787)
              ·
                refine ⟨32138534775548027921933681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21425689850365351947955787 32138534775548027921933681)
                ·
                  refine ⟨24103901081661020941450261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32138534775548027921933681 24103901081661020941450261)
                  ·
                    refine ⟨1129870363202860356630481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24103901081661020941450261 1129870363202860356630481)
                    ·
                      rfl

theorem cell22_3300622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3300622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300622 prefixEnd_3300622 := by exact prefixLift 3300622
  have htrace : WordTrace (prefixWord ++ tailWord_3300622) baseStart_3300622 baseEnd_3300622 := by
    simpa [prefixWord, tailWord_3300622, baseEnd_3300622] using wordTrace_append hprefix tailTrace_3300622
  have hstable : (prefixWord ++ tailWord_3300622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300622).length < 2 ^ (prefixWord ++ tailWord_3300622).sum := by decide
  have hdescent : baseEnd_3300622 < baseStart_3300622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300658 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3300658 : Nat := 118140960795 + 3300658 * 2 ^ 59
def prefixEnd_3300658 : Nat := 4983230072969 + 3 ^ 40 * 3300658 * 2
def baseEnd_3300658 : Nat := 1129882686738568262730371

theorem tailTrace_3300658 : CollatzResearch.WordTrace tailWord_3300658 prefixEnd_3300658 1129882686738568262730371 := by
  unfold tailWord_3300658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096221819071812088115657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80256591517524832234975085 30096221819071812088115657)
  ·
    refine ⟨22572166364303859066086743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30096221819071812088115657 22572166364303859066086743)
    ·
      refine ⟨33858249546455788599130115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22572166364303859066086743 33858249546455788599130115)
      ·
        refine ⟨50787374319683682898695173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33858249546455788599130115 50787374319683682898695173)
        ·
          refine ⟨9522632684940690543505345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50787374319683682898695173 9522632684940690543505345)
          ·
            refine ⟨7141974513705517907629009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9522632684940690543505345 7141974513705517907629009)
            ·
              refine ⟨5356480885279138430721757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7141974513705517907629009 5356480885279138430721757)
              ·
                refine ⟨2008680331979676911520659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5356480885279138430721757 2008680331979676911520659)
                ·
                  refine ⟨3013020497969515367280989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008680331979676911520659 3013020497969515367280989)
                  ·
                    refine ⟨1129882686738568262730371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013020497969515367280989 1129882686738568262730371)
                    ·
                      rfl

theorem cell22_3300658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3300658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300658 prefixEnd_3300658 := by exact prefixLift 3300658
  have htrace : WordTrace (prefixWord ++ tailWord_3300658) baseStart_3300658 baseEnd_3300658 := by
    simpa [prefixWord, tailWord_3300658, baseEnd_3300658] using wordTrace_append hprefix tailTrace_3300658
  have hstable : (prefixWord ++ tailWord_3300658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300658).length < 2 ^ (prefixWord ++ tailWord_3300658).sum := by decide
  have hdescent : baseEnd_3300658 < baseStart_3300658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300716 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 4]
def baseStart_3300716 : Nat := 118140960795 + 3300716 * 2 ^ 59
def prefixEnd_3300716 : Nat := 4983230072969 + 3 ^ 40 * 3300716 * 2
def baseEnd_3300716 : Nat := 376634180441291814926731

theorem tailTrace_3300716 : CollatzResearch.WordTrace tailWord_3300716 prefixEnd_3300716 376634180441291814926731 := by
  unfold tailWord_3300716
  simp only [CollatzResearch.WordTrace]
  refine ⟨60193501355038562129037001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80258001806718082838716001 60193501355038562129037001)
  ·
    refine ⟨45145126016278921596777751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60193501355038562129037001 45145126016278921596777751)
    ·
      refine ⟨67717689024418382395166627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45145126016278921596777751 67717689024418382395166627)
      ·
        refine ⟨101576533536627573592749941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67717689024418382395166627 101576533536627573592749941)
        ·
          refine ⟨9522800019058835024320307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101576533536627573592749941 9522800019058835024320307)
          ·
            refine ⟨14284200028588252536480461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9522800019058835024320307 14284200028588252536480461)
            ·
              refine ⟨5356575010720594701180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14284200028588252536480461 5356575010720594701180173)
              ·
                refine ⟨2008715629020223012942565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5356575010720594701180173 2008715629020223012942565)
                ·
                  refine ⟨376634180441291814926731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008715629020223012942565 376634180441291814926731)
                  ·
                    rfl

theorem cell22_3300716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_3300716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300716 prefixEnd_3300716 := by exact prefixLift 3300716
  have htrace : WordTrace (prefixWord ++ tailWord_3300716) baseStart_3300716 baseEnd_3300716 := by
    simpa [prefixWord, tailWord_3300716, baseEnd_3300716] using wordTrace_append hprefix tailTrace_3300716
  have hstable : (prefixWord ++ tailWord_3300716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300716).length < 2 ^ (prefixWord ++ tailWord_3300716).sum := by decide
  have hdescent : baseEnd_3300716 < baseStart_3300716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300744 : List Nat := [2, 1, 3, 3, 1, 3, 2, 7]
def baseStart_3300744 : Nat := 118140960795 + 3300744 * 2 ^ 59
def prefixEnd_3300744 : Nat := 4983230072969 + 3 ^ 40 * 3300744 * 2
def baseEnd_3300744 : Nat := 125545791810676967231123

theorem tailTrace_3300744 : CollatzResearch.WordTrace tailWord_3300744 prefixEnd_3300744 125545791810676967231123 := by
  unfold tailWord_3300744
  simp only [CollatzResearch.WordTrace]
  refine ⟨60194011976987842520046643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80258682635983790026728857 60194011976987842520046643)
  ·
    refine ⟨90291017965481763780069965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60194011976987842520046643 90291017965481763780069965)
    ·
      refine ⟨33859131737055661417526237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90291017965481763780069965 33859131737055661417526237)
      ·
        refine ⟨12697174401395873031572339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33859131737055661417526237 12697174401395873031572339)
        ·
          refine ⟨19045761602093809547358509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12697174401395873031572339 19045761602093809547358509)
          ·
            refine ⟨7142160600785178580259441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19045761602093809547358509 7142160600785178580259441)
            ·
              refine ⟨5356620450588883935194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142160600785178580259441 5356620450588883935194581)
              ·
                refine ⟨125545791810676967231123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5356620450588883935194581 125545791810676967231123)
                ·
                  rfl

theorem cell22_3300744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_3300744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300744 prefixEnd_3300744 := by exact prefixLift 3300744
  have htrace : WordTrace (prefixWord ++ tailWord_3300744) baseStart_3300744 baseEnd_3300744 := by
    simpa [prefixWord, tailWord_3300744, baseEnd_3300744] using wordTrace_append hprefix tailTrace_3300744
  have hstable : (prefixWord ++ tailWord_3300744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300744).length < 2 ^ (prefixWord ++ tailWord_3300744).sum := by decide
  have hdescent : baseEnd_3300744 < baseStart_3300744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300759 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 5, 3]
def baseStart_3300759 : Nat := 118140960795 + 3300759 * 2 ^ 59
def prefixEnd_3300759 : Nat := 4983230072969 + 3 ^ 40 * 3300759 * 2
def baseEnd_3300759 : Nat := 1129917261102637665955061

theorem tailTrace_3300759 : CollatzResearch.WordTrace tailWord_3300759 prefixEnd_3300759 1129917261102637665955061 := by
  unfold tailWord_3300759
  simp only [CollatzResearch.WordTrace]
  refine ⟨120388571048921342601889331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80259047365947561734592887 120388571048921342601889331)
  ·
    refine ⟨180582856573382013902833997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120388571048921342601889331 180582856573382013902833997)
    ·
      refine ⟨67718571215018255213562749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180582856573382013902833997 67718571215018255213562749)
      ·
        refine ⟨25394464205631845705086031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67718571215018255213562749 25394464205631845705086031)
        ·
          refine ⟨38091696308447768557629047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25394464205631845705086031 38091696308447768557629047)
          ·
            refine ⟨57137544462671652836443571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38091696308447768557629047 57137544462671652836443571)
            ·
              refine ⟨85706316694007479254665357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57137544462671652836443571 85706316694007479254665357)
              ·
                refine ⟨32139868760252804720499509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85706316694007479254665357 32139868760252804720499509)
                ·
                  refine ⟨3013112696273700442546829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32139868760252804720499509 3013112696273700442546829)
                  ·
                    refine ⟨1129917261102637665955061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013112696273700442546829 1129917261102637665955061)
                    ·
                      rfl

theorem cell22_3300759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_3300759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300759 prefixEnd_3300759 := by exact prefixLift 3300759
  have htrace : WordTrace (prefixWord ++ tailWord_3300759) baseStart_3300759 baseEnd_3300759 := by
    simpa [prefixWord, tailWord_3300759, baseEnd_3300759] using wordTrace_append hprefix tailTrace_3300759
  have hstable : (prefixWord ++ tailWord_3300759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300759).length < 2 ^ (prefixWord ++ tailWord_3300759).sum := by decide
  have hdescent : baseEnd_3300759 < baseStart_3300759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300787 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_3300787 : Nat := 118140960795 + 3300787 * 2 ^ 59
def prefixEnd_3300787 : Nat := 4983230072969 + 3 ^ 40 * 3300787 * 2
def baseEnd_3300787 : Nat := 1129926846074854926254975

theorem tailTrace_3300787 : CollatzResearch.WordTrace tailWord_3300787 prefixEnd_3300787 1129926846074854926254975 := by
  unfold tailWord_3300787
  simp only [CollatzResearch.WordTrace]
  refine ⟨120389592292819903383908615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80259728195213268922605743 120389592292819903383908615)
  ·
    refine ⟨180584388439229855075862923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120389592292819903383908615 180584388439229855075862923)
    ·
      refine ⟨270876582658844782613794385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180584388439229855075862923 270876582658844782613794385)
      ·
        refine ⟨203157436994133586960345789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270876582658844782613794385 203157436994133586960345789)
        ·
          refine ⟨76184038872800095110129671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203157436994133586960345789 76184038872800095110129671)
          ·
            refine ⟨114276058309200142665194507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76184038872800095110129671 114276058309200142665194507)
            ·
              refine ⟨171414087463800213997791761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114276058309200142665194507 171414087463800213997791761)
              ·
                refine ⟨128560565597850160498343821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171414087463800213997791761 128560565597850160498343821)
                ·
                  refine ⟨48210212099193810186878933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128560565597850160498343821 48210212099193810186878933)
                  ·
                    refine ⟨1129926846074854926254975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48210212099193810186878933 1129926846074854926254975)
                    ·
                      rfl

theorem cell22_3300787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_3300787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300787 prefixEnd_3300787 := by exact prefixLift 3300787
  have htrace : WordTrace (prefixWord ++ tailWord_3300787) baseStart_3300787 baseEnd_3300787 := by
    simpa [prefixWord, tailWord_3300787, baseEnd_3300787] using wordTrace_append hprefix tailTrace_3300787
  have hstable : (prefixWord ++ tailWord_3300787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300787).length < 2 ^ (prefixWord ++ tailWord_3300787).sum := by decide
  have hdescent : baseEnd_3300787 < baseStart_3300787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300896 : List Nat := [2, 1, 1, 6, 1, 3, 8]
def baseStart_3300896 : Nat := 118140960795 + 3300896 * 2 ^ 59
def prefixEnd_3300896 : Nat := 4983230072969 + 3 ^ 40 * 3300896 * 2
def baseEnd_3300896 : Nat := 41850524407496850936283

theorem tailTrace_3300896 : CollatzResearch.WordTrace tailWord_3300896 prefixEnd_3300896 41850524407496850936283 := by
  unfold tailWord_3300896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60196783924712507499813271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80262378566283343333084361 60196783924712507499813271)
  ·
    refine ⟨90295175887068761249719907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60196783924712507499813271 90295175887068761249719907)
    ·
      refine ⟨135442763830603141874579861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90295175887068761249719907 135442763830603141874579861)
      ·
        refine ⟨6348879554559522275370931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135442763830603141874579861 6348879554559522275370931)
        ·
          refine ⟨9523319331839283413056397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6348879554559522275370931 9523319331839283413056397)
          ·
            refine ⟨3571244749439731279896149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9523319331839283413056397 3571244749439731279896149)
            ·
              refine ⟨41850524407496850936283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3571244749439731279896149 41850524407496850936283)
              ·
                rfl

theorem cell22_3300896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 8].length) (baseStart_3300896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300896 prefixEnd_3300896 := by exact prefixLift 3300896
  have htrace : WordTrace (prefixWord ++ tailWord_3300896) baseStart_3300896 baseEnd_3300896 := by
    simpa [prefixWord, tailWord_3300896, baseEnd_3300896] using wordTrace_append hprefix tailTrace_3300896
  have hstable : (prefixWord ++ tailWord_3300896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300896).length < 2 ^ (prefixWord ++ tailWord_3300896).sum := by decide
  have hdescent : baseEnd_3300896 < baseStart_3300896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300939 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_3300939 : Nat := 118140960795 + 3300939 * 2 ^ 59
def prefixEnd_3300939 : Nat := 4983230072969 + 3 ^ 40 * 3300939 * 2
def baseEnd_3300939 : Nat := 1129978878781177196454509

theorem tailTrace_3300939 : CollatzResearch.WordTrace tailWord_3300939 prefixEnd_3300939 1129978878781177196454509 := by
  unfold tailWord_3300939
  simp only [CollatzResearch.WordTrace]
  refine ⟨120395136188269233343441871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80263424125512822228961247 120395136188269233343441871)
  ·
    refine ⟨180592704282403850015162807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120395136188269233343441871 180592704282403850015162807)
    ·
      refine ⟨270889056423605775022744211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180592704282403850015162807 270889056423605775022744211)
      ·
        refine ⟨406333584635408662534116317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270889056423605775022744211 406333584635408662534116317)
        ·
          refine ⟨152375094238278248450293619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406333584635408662534116317 152375094238278248450293619)
          ·
            refine ⟨228562641357417372675440429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152375094238278248450293619 228562641357417372675440429)
            ·
              refine ⟨85710990509031514753290161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228562641357417372675440429 85710990509031514753290161)
              ·
                refine ⟨64283242881773636064967621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85710990509031514753290161 64283242881773636064967621)
                ·
                  refine ⟨12053108040332556762181429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64283242881773636064967621 12053108040332556762181429)
                  ·
                    refine ⟨1129978878781177196454509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053108040332556762181429 1129978878781177196454509)
                    ·
                      rfl

theorem cell22_3300939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_3300939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300939 prefixEnd_3300939 := by exact prefixLift 3300939
  have htrace : WordTrace (prefixWord ++ tailWord_3300939) baseStart_3300939 baseEnd_3300939 := by
    simpa [prefixWord, tailWord_3300939, baseEnd_3300939] using wordTrace_append hprefix tailTrace_3300939
  have hstable : (prefixWord ++ tailWord_3300939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300939).length < 2 ^ (prefixWord ++ tailWord_3300939).sum := by decide
  have hdescent : baseEnd_3300939 < baseStart_3300939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3300973 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3300973 : Nat := 118140960795 + 3300973 * 2 ^ 59
def prefixEnd_3300973 : Nat := 4983230072969 + 3 ^ 40 * 3300973 * 2
def baseEnd_3300973 : Nat := 1129990517676012441104405

theorem tailTrace_3300973 : CollatzResearch.WordTrace tailWord_3300973 prefixEnd_3300973 1129990517676012441104405 := by
  unfold tailWord_3300973
  simp only [CollatzResearch.WordTrace]
  refine ⟨120396376270146057150179573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80264250846764038100119715 120396376270146057150179573)
  ·
    refine ⟨11287160275326192857829335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120396376270146057150179573 11287160275326192857829335)
    ·
      refine ⟨16930740412989289286744003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11287160275326192857829335 16930740412989289286744003)
      ·
        refine ⟨25396110619483933930116005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930740412989289286744003 25396110619483933930116005)
        ·
          refine ⟨4761770741153237611896751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25396110619483933930116005 4761770741153237611896751)
          ·
            refine ⟨7142656111729856417845127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761770741153237611896751 7142656111729856417845127)
            ·
              refine ⟨10713984167594784626767691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7142656111729856417845127 10713984167594784626767691)
              ·
                refine ⟨16070976251392176940151537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10713984167594784626767691 16070976251392176940151537)
                ·
                  refine ⟨12053232188544132705113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16070976251392176940151537 12053232188544132705113653)
                  ·
                    refine ⟨1129990517676012441104405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053232188544132705113653 1129990517676012441104405)
                    ·
                      rfl

theorem cell22_3300973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3300973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3300973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3300973 prefixEnd_3300973 := by exact prefixLift 3300973
  have htrace : WordTrace (prefixWord ++ tailWord_3300973) baseStart_3300973 baseEnd_3300973 := by
    simpa [prefixWord, tailWord_3300973, baseEnd_3300973] using wordTrace_append hprefix tailTrace_3300973
  have hstable : (prefixWord ++ tailWord_3300973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3300973).length < 2 ^ (prefixWord ++ tailWord_3300973).sum := by decide
  have hdescent : baseEnd_3300973 < baseStart_3300973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3300973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301001 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_3301001 : Nat := 118140960795 + 3301001 * 2 ^ 59
def prefixEnd_3301001 : Nat := 4983230072969 + 3 ^ 40 * 3301001 * 2
def baseEnd_3301001 : Nat := 1130000102648229701404319

theorem tailTrace_3301001 : CollatzResearch.WordTrace tailWord_3301001 prefixEnd_3301001 1130000102648229701404319 := by
  unfold tailWord_3301001
  simp only [CollatzResearch.WordTrace]
  refine ⟨120397397514044617932198857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80264931676029745288132571 120397397514044617932198857)
  ·
    refine ⟨90298048135533463449149143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120397397514044617932198857 90298048135533463449149143)
    ·
      refine ⟨135447072203300195173723715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90298048135533463449149143 135447072203300195173723715)
      ·
        refine ⟨203170608304950292760585573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135447072203300195173723715 203170608304950292760585573)
        ·
          refine ⟨38094489057178179892609795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203170608304950292760585573 38094489057178179892609795)
          ·
            refine ⟨57141733585767269838914693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38094489057178179892609795 57141733585767269838914693)
            ·
              refine ⟨10714075047331363094796505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57141733585767269838914693 10714075047331363094796505)
              ·
                refine ⟨8035556285498522321097379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10714075047331363094796505 8035556285498522321097379)
                ·
                  refine ⟨12053334428247783481646069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035556285498522321097379 12053334428247783481646069)
                  ·
                    refine ⟨1130000102648229701404319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053334428247783481646069 1130000102648229701404319)
                    ·
                      rfl

theorem cell22_3301001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_3301001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301001 prefixEnd_3301001 := by exact prefixLift 3301001
  have htrace : WordTrace (prefixWord ++ tailWord_3301001) baseStart_3301001 baseEnd_3301001 := by
    simpa [prefixWord, tailWord_3301001, baseEnd_3301001] using wordTrace_append hprefix tailTrace_3301001
  have hstable : (prefixWord ++ tailWord_3301001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301001).length < 2 ^ (prefixWord ++ tailWord_3301001).sum := by decide
  have hdescent : baseEnd_3301001 < baseStart_3301001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301003 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 4]
def baseStart_3301003 : Nat := 118140960795 + 3301003 * 2 ^ 59
def prefixEnd_3301003 : Nat := 4983230072969 + 3 ^ 40 * 3301003 * 2
def baseEnd_3301003 : Nat := 376666929096367454284771

theorem tailTrace_3301003 : CollatzResearch.WordTrace tailWord_3301003 prefixEnd_3301003 376666929096367454284771 := by
  unfold tailWord_3301003
  simp only [CollatzResearch.WordTrace]
  refine ⟨120397470460037372273771663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80264980306691581515847775 120397470460037372273771663)
  ·
    refine ⟨180596205690056058410657495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120397470460037372273771663 180596205690056058410657495)
    ·
      refine ⟨270894308535084087615986243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180596205690056058410657495 270894308535084087615986243)
      ·
        refine ⟨406341462802626131423979365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270894308535084087615986243 406341462802626131423979365)
        ·
          refine ⟨76189024275492399641996131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406341462802626131423979365 76189024275492399641996131)
          ·
            refine ⟨114283536413238599462994197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76189024275492399641996131 114283536413238599462994197)
            ·
              refine ⟨5357040769370559349827853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114283536413238599462994197 5357040769370559349827853)
              ·
                refine ⟨2008890288513959756185445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5357040769370559349827853 2008890288513959756185445)
                ·
                  refine ⟨376666929096367454284771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008890288513959756185445 376666929096367454284771)
                  ·
                    rfl

theorem cell22_3301003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 4].length) (baseStart_3301003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301003 prefixEnd_3301003 := by exact prefixLift 3301003
  have htrace : WordTrace (prefixWord ++ tailWord_3301003) baseStart_3301003 baseEnd_3301003 := by
    simpa [prefixWord, tailWord_3301003, baseEnd_3301003] using wordTrace_append hprefix tailTrace_3301003
  have hstable : (prefixWord ++ tailWord_3301003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301003).length < 2 ^ (prefixWord ++ tailWord_3301003).sum := by decide
  have hdescent : baseEnd_3301003 < baseStart_3301003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301093 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 5]
def baseStart_3301093 : Nat := 118140960795 + 3301093 * 2 ^ 59
def prefixEnd_3301093 : Nat := 4983230072969 + 3 ^ 40 * 3301093 * 2
def baseEnd_3301093 : Nat := 376677198709457376034679

theorem tailTrace_3301093 : CollatzResearch.WordTrace tailWord_3301093 prefixEnd_3301093 376677198709457376034679 := by
  unfold tailWord_3301093
  simp only [CollatzResearch.WordTrace]
  refine ⟨120400753029711317644547933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80267168686474211763031955 120400753029711317644547933)
  ·
    refine ⟨45150282386141744116705475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120400753029711317644547933 45150282386141744116705475)
    ·
      refine ⟨67725423579212616175058213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45150282386141744116705475 67725423579212616175058213)
      ·
        refine ⟨12698516921102365532823415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67725423579212616175058213 12698516921102365532823415)
        ·
          refine ⟨19047775381653548299235123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12698516921102365532823415 19047775381653548299235123)
          ·
            refine ⟨28571663072480322448852685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19047775381653548299235123 28571663072480322448852685)
            ·
              refine ⟨10714373652180120918319757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28571663072480322448852685 10714373652180120918319757)
              ·
                refine ⟨4017890119567545344369909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10714373652180120918319757 4017890119567545344369909)
                ·
                  refine ⟨376677198709457376034679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017890119567545344369909 376677198709457376034679)
                  ·
                    rfl

theorem cell22_3301093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_3301093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301093 prefixEnd_3301093 := by exact prefixLift 3301093
  have htrace : WordTrace (prefixWord ++ tailWord_3301093) baseStart_3301093 baseEnd_3301093 := by
    simpa [prefixWord, tailWord_3301093, baseEnd_3301093] using wordTrace_append hprefix tailTrace_3301093
  have hstable : (prefixWord ++ tailWord_3301093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301093).length < 2 ^ (prefixWord ++ tailWord_3301093).sum := by decide
  have hdescent : baseEnd_3301093 < baseStart_3301093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301123 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 1, 4]
def baseStart_3301123 : Nat := 118140960795 + 3301123 * 2 ^ 59
def prefixEnd_3301123 : Nat := 4983230072969 + 3 ^ 40 * 3301123 * 2
def baseEnd_3301123 : Nat := 1130041865741462049853945

theorem tailTrace_3301123 : CollatzResearch.WordTrace tailWord_3301123 prefixEnd_3301123 1130041865741462049853945 := by
  unfold tailWord_3301123
  simp only [CollatzResearch.WordTrace]
  refine ⟨120401847219602632768140023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80267898146401755178760015 120401847219602632768140023)
  ·
    refine ⟨180602770829403949152210035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120401847219602632768140023 180602770829403949152210035)
    ·
      refine ⟨270904156244105923728315053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180602770829403949152210035 270904156244105923728315053)
      ·
        refine ⟨101589058591539721398118145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270904156244105923728315053 101589058591539721398118145)
        ·
          refine ⟨76191793943654791048588609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101589058591539721398118145 76191793943654791048588609)
          ·
            refine ⟨57143845457741093286441457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76191793943654791048588609 57143845457741093286441457)
            ·
              refine ⟨42857884093305819964831093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57143845457741093286441457 42857884093305819964831093)
              ·
                refine ⟨4017926633747420621702915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42857884093305819964831093 4017926633747420621702915)
                ·
                  refine ⟨6026889950621130932554373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017926633747420621702915 6026889950621130932554373)
                  ·
                    refine ⟨1130041865741462049853945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6026889950621130932554373 1130041865741462049853945)
                    ·
                      rfl

theorem cell22_3301123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 4].length) (baseStart_3301123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301123 prefixEnd_3301123 := by exact prefixLift 3301123
  have htrace : WordTrace (prefixWord ++ tailWord_3301123) baseStart_3301123 baseEnd_3301123 := by
    simpa [prefixWord, tailWord_3301123, baseEnd_3301123] using wordTrace_append hprefix tailTrace_3301123
  have hstable : (prefixWord ++ tailWord_3301123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301123).length < 2 ^ (prefixWord ++ tailWord_3301123).sum := by decide
  have hdescent : baseEnd_3301123 < baseStart_3301123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301153 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3301153 : Nat := 118140960795 + 3301153 * 2 ^ 59
def prefixEnd_3301153 : Nat := 4983230072969 + 3 ^ 40 * 3301153 * 2
def baseEnd_3301153 : Nat := 1130052135354551971603853

theorem tailTrace_3301153 : CollatzResearch.WordTrace tailWord_3301153 prefixEnd_3301153 1130052135354551971603853 := by
  unfold tailWord_3301153
  simp only [CollatzResearch.WordTrace]
  refine ⟨120402941409493947891732113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80268627606329298594488075 120402941409493947891732113)
  ·
    refine ⟨90302206057120460918799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120402941409493947891732113 90302206057120460918799085)
    ·
      refine ⟨33863327271420172844549657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90302206057120460918799085 33863327271420172844549657)
      ·
        refine ⟨25397495453565129633412243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33863327271420172844549657 25397495453565129633412243)
        ·
          refine ⟨38096243180347694450118365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25397495453565129633412243 38096243180347694450118365)
          ·
            refine ⟨14286091192630385418794387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38096243180347694450118365 14286091192630385418794387)
            ·
              refine ⟨21429136788945578128191581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286091192630385418794387 21429136788945578128191581)
              ·
                refine ⟨8035926295854591798071843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21429136788945578128191581 8035926295854591798071843)
                ·
                  refine ⟨12053889443781887697107765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035926295854591798071843 12053889443781887697107765)
                  ·
                    refine ⟨1130052135354551971603853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053889443781887697107765 1130052135354551971603853)
                    ·
                      rfl

theorem cell22_3301153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3301153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301153 prefixEnd_3301153 := by exact prefixLift 3301153
  have htrace : WordTrace (prefixWord ++ tailWord_3301153) baseStart_3301153 baseEnd_3301153 := by
    simpa [prefixWord, tailWord_3301153, baseEnd_3301153] using wordTrace_append hprefix tailTrace_3301153
  have hstable : (prefixWord ++ tailWord_3301153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301153).length < 2 ^ (prefixWord ++ tailWord_3301153).sum := by decide
  have hdescent : baseEnd_3301153 < baseStart_3301153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301172 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3301172 : Nat := 118140960795 + 3301172 * 2 ^ 59
def prefixEnd_3301172 : Nat := 4983230072969 + 3 ^ 40 * 3301172 * 2
def baseEnd_3301172 : Nat := 376686213147614085126265

theorem tailTrace_3301172 : CollatzResearch.WordTrace tailWord_3301172 prefixEnd_3301172 376686213147614085126265 := by
  unfold tailWord_3301172
  simp only [CollatzResearch.WordTrace]
  refine ⟨60201817198212557068336885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80269089597616742757782513 60201817198212557068336885)
  ·
    refine ⟨5643920362332427225156583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60201817198212557068336885 5643920362332427225156583)
    ·
      refine ⟨8465880543498640837734875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5643920362332427225156583 8465880543498640837734875)
      ·
        refine ⟨12698820815247961256602313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8465880543498640837734875 12698820815247961256602313)
        ·
          refine ⟨9524115611435970942451735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12698820815247961256602313 9524115611435970942451735)
          ·
            refine ⟨14286173417153956413677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524115611435970942451735 14286173417153956413677603)
            ·
              refine ⟨21429260125730934620516405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14286173417153956413677603 21429260125730934620516405)
              ·
                refine ⟨2008993136787275120673413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21429260125730934620516405 2008993136787275120673413)
                ·
                  refine ⟨376686213147614085126265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008993136787275120673413 376686213147614085126265)
                  ·
                    rfl

theorem cell22_3301172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3301172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301172 prefixEnd_3301172 := by exact prefixLift 3301172
  have htrace : WordTrace (prefixWord ++ tailWord_3301172) baseStart_3301172 baseEnd_3301172 := by
    simpa [prefixWord, tailWord_3301172, baseEnd_3301172] using wordTrace_append hprefix tailTrace_3301172
  have hstable : (prefixWord ++ tailWord_3301172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301172).length < 2 ^ (prefixWord ++ tailWord_3301172).sum := by decide
  have hdescent : baseEnd_3301172 < baseStart_3301172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301174 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3301174 : Nat := 118140960795 + 3301174 * 2 ^ 59
def prefixEnd_3301174 : Nat := 4983230072969 + 3 ^ 40 * 3301174 * 2
def baseEnd_3301174 : Nat := 1130059324083714916828789

theorem tailTrace_3301174 : CollatzResearch.WordTrace tailWord_3301174 prefixEnd_3301174 1130059324083714916828789 := by
  unfold tailWord_3301174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525231708901116779890411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80269138228278578985497717 7525231708901116779890411)
  ·
    refine ⟨11287847563351675169835617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7525231708901116779890411 11287847563351675169835617)
    ·
      refine ⟨8465885672513756377376713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11287847563351675169835617 8465885672513756377376713)
      ·
        refine ⟨6349414254385317283032535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8465885672513756377376713 6349414254385317283032535)
        ·
          refine ⟨9524121381577975924548803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6349414254385317283032535 9524121381577975924548803)
          ·
            refine ⟨14286182072366963886823205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524121381577975924548803 14286182072366963886823205)
            ·
              refine ⟨2678659138568805728779351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14286182072366963886823205 2678659138568805728779351)
              ·
                refine ⟨4017988707853208593169027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678659138568805728779351 4017988707853208593169027)
                ·
                  refine ⟨6026983061779812889753541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017988707853208593169027 6026983061779812889753541)
                  ·
                    refine ⟨1130059324083714916828789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6026983061779812889753541 1130059324083714916828789)
                    ·
                      rfl

theorem cell22_3301174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3301174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301174 prefixEnd_3301174 := by exact prefixLift 3301174
  have htrace : WordTrace (prefixWord ++ tailWord_3301174) baseStart_3301174 baseEnd_3301174 := by
    simpa [prefixWord, tailWord_3301174, baseEnd_3301174] using wordTrace_append hprefix tailTrace_3301174
  have hstable : (prefixWord ++ tailWord_3301174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301174).length < 2 ^ (prefixWord ++ tailWord_3301174).sum := by decide
  have hdescent : baseEnd_3301174 < baseStart_3301174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301183 : List Nat := [1, 1, 2, 2, 6, 1, 9]
def baseStart_3301183 : Nat := 118140960795 + 3301183 * 2 ^ 59
def prefixEnd_3301183 : Nat := 4983230072969 + 3 ^ 40 * 3301183 * 2
def baseEnd_3301183 : Nat := 41854163146949699753843

theorem tailTrace_3301183 : CollatzResearch.WordTrace tailWord_3301183 prefixEnd_3301183 41854163146949699753843 := by
  unfold tailWord_3301183
  simp only [CollatzResearch.WordTrace]
  refine ⟨120404035599385263015324203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80269357066256842010216135 120404035599385263015324203)
  ·
    refine ⟨180606053399077894522986305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120404035599385263015324203 180606053399077894522986305)
    ·
      refine ⟨135454540049308420892239729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180606053399077894522986305 135454540049308420892239729)
      ·
        refine ⟨101590905036981315669179797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135454540049308420892239729 101590905036981315669179797)
        ·
          refine ⟨4762073673608499171992803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101590905036981315669179797 4762073673608499171992803)
          ·
            refine ⟨7143110510412748757989205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762073673608499171992803 7143110510412748757989205)
            ·
              refine ⟨41854163146949699753843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7143110510412748757989205 41854163146949699753843)
              ·
                rfl

theorem cell22_3301183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 9].length) (baseStart_3301183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301183 prefixEnd_3301183 := by exact prefixLift 3301183
  have htrace : WordTrace (prefixWord ++ tailWord_3301183) baseStart_3301183 baseEnd_3301183 := by
    simpa [prefixWord, tailWord_3301183, baseEnd_3301183] using wordTrace_append hprefix tailTrace_3301183
  have hstable : (prefixWord ++ tailWord_3301183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301183).length < 2 ^ (prefixWord ++ tailWord_3301183).sum := by decide
  have hdescent : baseEnd_3301183 < baseStart_3301183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3301187 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 2, 3]
def baseStart_3301187 : Nat := 118140960795 + 3301187 * 2 ^ 59
def prefixEnd_3301187 : Nat := 4983230072969 + 3 ^ 40 * 3301187 * 2
def baseEnd_3301187 : Nat := 1130063774249387216253749

theorem tailTrace_3301187 : CollatzResearch.WordTrace tailWord_3301187 prefixEnd_3301187 1130063774249387216253749 := by
  unfold tailWord_3301187
  simp only [CollatzResearch.WordTrace]
  refine ⟨120404181491370771698469815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80269454327580514465646543 120404181491370771698469815)
  ·
    refine ⟨180606272237056157547704723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120404181491370771698469815 180606272237056157547704723)
    ·
      refine ⟨270909408355584236321557085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180606272237056157547704723 270909408355584236321557085)
      ·
        refine ⟨101591028133344088620583907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270909408355584236321557085 101591028133344088620583907)
        ·
          refine ⟨152386542200016132930875861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101591028133344088620583907 152386542200016132930875861)
          ·
            refine ⟨3571559582812878115567403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 152386542200016132930875861 3571559582812878115567403)
            ·
              refine ⟨5357339374219317173351105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571559582812878115567403 5357339374219317173351105)
              ·
                refine ⟨4018004530664487880013329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357339374219317173351105 4018004530664487880013329)
                ·
                  refine ⟨3013503397998365910009997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018004530664487880013329 3013503397998365910009997)
                  ·
                    refine ⟨1130063774249387216253749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013503397998365910009997 1130063774249387216253749)
                    ·
                      rfl

theorem cell22_3301187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 3].length) (baseStart_3301187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3301187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3301187 prefixEnd_3301187 := by exact prefixLift 3301187
  have htrace : WordTrace (prefixWord ++ tailWord_3301187) baseStart_3301187 baseEnd_3301187 := by
    simpa [prefixWord, tailWord_3301187, baseEnd_3301187] using wordTrace_append hprefix tailTrace_3301187
  have hstable : (prefixWord ++ tailWord_3301187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3301187).length < 2 ^ (prefixWord ++ tailWord_3301187).sum := by decide
  have hdescent : baseEnd_3301187 < baseStart_3301187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3301187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
