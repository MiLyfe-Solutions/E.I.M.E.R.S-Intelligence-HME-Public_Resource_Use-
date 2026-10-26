import V185TrunkScan22Chunk176

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1579605 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 9]
def baseStart_1579605 : Nat := 118140960795 + 1579605 * 2 ^ 59
def prefixEnd_1579605 : Nat := 4983230072969 + 3 ^ 40 * 1579605 * 2
def baseEnd_1579605 : Nat := 180243690943421671527341

theorem tailTrace_1579605 : CollatzResearch.WordTrace tailWord_1579605 prefixEnd_1579605 180243690943421671527341 := by
  unfold tailWord_1579605
  simp only [CollatzResearch.WordTrace]
  refine ⟨57612927442368334901220269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38408618294912223267480179 57612927442368334901220269)
  ·
    refine ⟨21604847790888125587957601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57612927442368334901220269 21604847790888125587957601)
    ·
      refine ⟨16203635843166094190968201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21604847790888125587957601 16203635843166094190968201)
      ·
        refine ⟨12152726882374570643226151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16203635843166094190968201 12152726882374570643226151)
        ·
          refine ⟨18229090323561855964839227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152726882374570643226151 18229090323561855964839227)
          ·
            refine ⟨27343635485342783947258841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229090323561855964839227 27343635485342783947258841)
            ·
              refine ⟨20507726614007087960444131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27343635485342783947258841 20507726614007087960444131)
              ·
                refine ⟨30761589921010631940666197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20507726614007087960444131 30761589921010631940666197)
                ·
                  refine ⟨180243690943421671527341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30761589921010631940666197 180243690943421671527341)
                  ·
                    rfl

theorem cell22_1579605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_1579605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579605 prefixEnd_1579605 := by exact prefixLift 1579605
  have htrace : WordTrace (prefixWord ++ tailWord_1579605) baseStart_1579605 baseEnd_1579605 := by
    simpa [prefixWord, tailWord_1579605, baseEnd_1579605] using wordTrace_append hprefix tailTrace_1579605
  have hstable : (prefixWord ++ tailWord_1579605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579605).length < 2 ^ (prefixWord ++ tailWord_1579605).sum := by decide
  have hdescent : baseEnd_1579605 < baseStart_1579605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579626 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1579626 : Nat := 118140960795 + 1579626 * 2 ^ 59
def prefixEnd_1579626 : Nat := 4983230072969 + 3 ^ 40 * 1579626 * 2
def baseEnd_1579626 : Nat := 540738261559427959806959

theorem tailTrace_1579626 : CollatzResearch.WordTrace tailWord_1579626 prefixEnd_1579626 540738261559427959806959 := by
  unfold tailWord_1579626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403423343823063871933683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38409128916861503658489821 14403423343823063871933683)
  ·
    refine ⟨21605135015734595807900525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14403423343823063871933683 21605135015734595807900525)
    ·
      refine ⟨8101925630900473427962697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21605135015734595807900525 8101925630900473427962697)
      ·
        refine ⟨6076444223175355070972023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8101925630900473427962697 6076444223175355070972023)
        ·
          refine ⟨9114666334763032606458035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076444223175355070972023 9114666334763032606458035)
          ·
            refine ⟨13671999502144548909687053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114666334763032606458035 13671999502144548909687053)
            ·
              refine ⟨5126999813304205841132645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13671999502144548909687053 5126999813304205841132645)
              ·
                refine ⟨961312464994538595212371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5126999813304205841132645 961312464994538595212371)
                ·
                  refine ⟨1441968697491807892818557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961312464994538595212371 1441968697491807892818557)
                  ·
                    refine ⟨540738261559427959806959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441968697491807892818557 540738261559427959806959)
                    ·
                      rfl

theorem cell22_1579626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1579626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579626 prefixEnd_1579626 := by exact prefixLift 1579626
  have htrace : WordTrace (prefixWord ++ tailWord_1579626) baseStart_1579626 baseEnd_1579626 := by
    simpa [prefixWord, tailWord_1579626, baseEnd_1579626] using wordTrace_append hprefix tailTrace_1579626
  have hstable : (prefixWord ++ tailWord_1579626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579626).length < 2 ^ (prefixWord ++ tailWord_1579626).sum := by decide
  have hdescent : baseEnd_1579626 < baseStart_1579626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1579665 : Nat := 118140960795 + 1579665 * 2 ^ 59
def prefixEnd_1579665 : Nat := 4983230072969 + 3 ^ 40 * 1579665 * 2
def baseEnd_1579665 : Nat := 540751612056444858081839

theorem tailTrace_1579665 : CollatzResearch.WordTrace tailWord_1579665 prefixEnd_1579665 540751612056444858081839 := by
  unfold tailWord_1579665
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615115822150965148404449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38410077214767310098936299 57615115822150965148404449)
  ·
    refine ⟨43211336866613223861303337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57615115822150965148404449 43211336866613223861303337)
    ·
      refine ⟨32408502649959917895977503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43211336866613223861303337 32408502649959917895977503)
      ·
        refine ⟨48612753974939876843966255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32408502649959917895977503 48612753974939876843966255)
        ·
          refine ⟨72919130962409815265949383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48612753974939876843966255 72919130962409815265949383)
          ·
            refine ⟨109378696443614722898924075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72919130962409815265949383 109378696443614722898924075)
            ·
              refine ⟨164068044665422084348386113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109378696443614722898924075 164068044665422084348386113)
              ·
                refine ⟨123051033499066563261289585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164068044665422084348386113 123051033499066563261289585)
                ·
                  refine ⟨92288275124299922445967189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123051033499066563261289585 92288275124299922445967189)
                  ·
                    refine ⟨540751612056444858081839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92288275124299922445967189 540751612056444858081839)
                    ·
                      rfl

theorem cell22_1579665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1579665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579665 prefixEnd_1579665 := by exact prefixLift 1579665
  have htrace : WordTrace (prefixWord ++ tailWord_1579665) baseStart_1579665 baseEnd_1579665 := by
    simpa [prefixWord, tailWord_1579665, baseEnd_1579665] using wordTrace_append hprefix tailTrace_1579665
  have hstable : (prefixWord ++ tailWord_1579665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579665).length < 2 ^ (prefixWord ++ tailWord_1579665).sum := by decide
  have hdescent : baseEnd_1579665 < baseStart_1579665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579684 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1579684 : Nat := 118140960795 + 1579684 * 2 ^ 59
def prefixEnd_1579684 : Nat := 4983230072969 + 3 ^ 40 * 1579684 * 2
def baseEnd_1579684 : Nat := 180252705381578380618927

theorem tailTrace_1579684 : CollatzResearch.WordTrace tailWord_1579684 prefixEnd_1579684 180252705381578380618927 := by
  unfold tailWord_1579684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28807904404541065696673053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38410539206054754262230737 28807904404541065696673053)
  ·
    refine ⟨10802964151702899636252395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28807904404541065696673053 10802964151702899636252395)
    ·
      refine ⟨16204446227554349454378593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802964151702899636252395 16204446227554349454378593)
      ·
        refine ⟨12153334670665762090783945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16204446227554349454378593 12153334670665762090783945)
        ·
          refine ⟨9115001002999321568087959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12153334670665762090783945 9115001002999321568087959)
          ·
            refine ⟨13672501504498982352131939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115001002999321568087959 13672501504498982352131939)
            ·
              refine ⟨20508752256748473528197909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672501504498982352131939 20508752256748473528197909)
              ·
                refine ⟨961347762035084696634277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20508752256748473528197909 961347762035084696634277)
                ·
                  refine ⟨180252705381578380618927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961347762035084696634277 180252705381578380618927)
                  ·
                    rfl

theorem cell22_1579684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1579684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579684 prefixEnd_1579684 := by exact prefixLift 1579684
  have htrace : WordTrace (prefixWord ++ tailWord_1579684) baseStart_1579684 baseEnd_1579684 := by
    simpa [prefixWord, tailWord_1579684, baseEnd_1579684] using wordTrace_append hprefix tailTrace_1579684
  have hstable : (prefixWord ++ tailWord_1579684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579684).length < 2 ^ (prefixWord ++ tailWord_1579684).sum := by decide
  have hdescent : baseEnd_1579684 < baseStart_1579684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579699 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 5]
def baseStart_1579699 : Nat := 118140960795 + 1579699 * 2 ^ 59
def prefixEnd_1579699 : Nat := 4983230072969 + 3 ^ 40 * 1579699 * 2
def baseEnd_1579699 : Nat := 540763250951280102731735

theorem tailTrace_1579699 : CollatzResearch.WordTrace tailWord_1579699 prefixEnd_1579699 540763250951280102731735 := by
  unfold tailWord_1579699
  simp only [CollatzResearch.WordTrace]
  refine ⟨57616355904027788955142151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38410903936018525970094767 57616355904027788955142151)
  ·
    refine ⟨86424533856041683432713227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57616355904027788955142151 86424533856041683432713227)
    ·
      refine ⟨129636800784062525149069841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86424533856041683432713227 129636800784062525149069841)
      ·
        refine ⟨97227600588046893861802381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129636800784062525149069841 97227600588046893861802381)
        ·
          refine ⟨36460350220517585198175893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97227600588046893861802381 36460350220517585198175893)
          ·
            refine ⟨1709078916586761806164495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36460350220517585198175893 1709078916586761806164495)
            ·
              refine ⟨2563618374880142709246743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709078916586761806164495 2563618374880142709246743)
              ·
                refine ⟨3845427562320214063870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563618374880142709246743 3845427562320214063870115)
                ·
                  refine ⟨5768141343480321095805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845427562320214063870115 5768141343480321095805173)
                  ·
                    refine ⟨540763250951280102731735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768141343480321095805173 540763250951280102731735)
                    ·
                      rfl

theorem cell22_1579699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 5].length) (baseStart_1579699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579699 prefixEnd_1579699 := by exact prefixLift 1579699
  have htrace : WordTrace (prefixWord ++ tailWord_1579699) baseStart_1579699 baseEnd_1579699 := by
    simpa [prefixWord, tailWord_1579699, baseEnd_1579699] using wordTrace_append hprefix tailTrace_1579699
  have hstable : (prefixWord ++ tailWord_1579699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579699).length < 2 ^ (prefixWord ++ tailWord_1579699).sum := by decide
  have hdescent : baseEnd_1579699 < baseStart_1579699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579712 : List Nat := [2, 1, 1, 2, 4, 3, 1, 8]
def baseStart_1579712 : Nat := 118140960795 + 1579712 * 2 ^ 59
def prefixEnd_1579712 : Nat := 4983230072969 + 3 ^ 40 * 1579712 * 2
def baseEnd_1579712 : Nat := 60085300124105822461855

theorem tailTrace_1579712 : CollatzResearch.WordTrace tailWord_1579712 prefixEnd_1579712 60085300124105822461855 := by
  unfold tailWord_1579712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808415026490346087682695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38411220035320461450243593 28808415026490346087682695)
  ·
    refine ⟨43212622539735519131524043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28808415026490346087682695 43212622539735519131524043)
    ·
      refine ⟨64818933809603278697286065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43212622539735519131524043 64818933809603278697286065)
      ·
        refine ⟨48614200357202459022964549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64818933809603278697286065 48614200357202459022964549)
        ·
          refine ⟨9115162566975461066805853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48614200357202459022964549 9115162566975461066805853)
          ·
            refine ⟨3418185962615797900052195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9115162566975461066805853 3418185962615797900052195)
            ·
              refine ⟨5127278943923696850078293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418185962615797900052195 5127278943923696850078293)
              ·
                refine ⟨60085300124105822461855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5127278943923696850078293 60085300124105822461855)
                ·
                  rfl

theorem cell22_1579712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_1579712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579712 prefixEnd_1579712 := by exact prefixLift 1579712
  have htrace : WordTrace (prefixWord ++ tailWord_1579712) baseStart_1579712 baseEnd_1579712 := by
    simpa [prefixWord, tailWord_1579712, baseEnd_1579712] using wordTrace_append hprefix tailTrace_1579712
  have hstable : (prefixWord ++ tailWord_1579712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579712).length < 2 ^ (prefixWord ++ tailWord_1579712).sum := by decide
  have hdescent : baseEnd_1579712 < baseStart_1579712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579765 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1579765 : Nat := 118140960795 + 1579765 * 2 ^ 59
def prefixEnd_1579765 : Nat := 4983230072969 + 3 ^ 40 * 1579765 * 2
def baseEnd_1579765 : Nat := 540785844100077930581533

theorem tailTrace_1579765 : CollatzResearch.WordTrace tailWord_1579765 prefixEnd_1579765 540785844100077930581533 := by
  unfold tailWord_1579765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57618763121788682227044749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38412508747859121484696499 57618763121788682227044749)
  ·
    refine ⟨21607036170670755835141781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57618763121788682227044749 21607036170670755835141781)
    ·
      refine ⟨1012829820500191679772271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21607036170670755835141781 1012829820500191679772271)
      ·
        refine ⟨1519244730750287519658407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012829820500191679772271 1519244730750287519658407)
        ·
          refine ⟨2278867096125431279487611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519244730750287519658407 2278867096125431279487611)
          ·
            refine ⟨3418300644188146919231417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278867096125431279487611 3418300644188146919231417)
            ·
              refine ⟨2563725483141110189423563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418300644188146919231417 2563725483141110189423563)
              ·
                refine ⟨3845588224711665284135345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563725483141110189423563 3845588224711665284135345)
                ·
                  refine ⟨2884191168533748963101509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845588224711665284135345 2884191168533748963101509)
                  ·
                    refine ⟨540785844100077930581533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2884191168533748963101509 540785844100077930581533)
                    ·
                      rfl

theorem cell22_1579765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1579765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579765 prefixEnd_1579765 := by exact prefixLift 1579765
  have htrace : WordTrace (prefixWord ++ tailWord_1579765) baseStart_1579765 baseEnd_1579765 := by
    simpa [prefixWord, tailWord_1579765, baseEnd_1579765] using wordTrace_append hprefix tailTrace_1579765
  have hstable : (prefixWord ++ tailWord_1579765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579765).length < 2 ^ (prefixWord ++ tailWord_1579765).sum := by decide
  have hdescent : baseEnd_1579765 < baseStart_1579765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579804 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1579804 : Nat := 118140960795 + 1579804 * 2 ^ 59
def prefixEnd_1579804 : Nat := 4983230072969 + 3 ^ 40 * 1579804 * 2
def baseEnd_1579804 : Nat := 540799194597094828856413

theorem tailTrace_1579804 : CollatzResearch.WordTrace tailWord_1579804 prefixEnd_1579804 540799194597094828856413 := by
  unfold tailWord_1579804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28810092784323695943857233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38413457045764927925142977 28810092784323695943857233)
  ·
    refine ⟨21607569588242771957892925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28810092784323695943857233 21607569588242771957892925)
    ·
      refine ⟨8102838595591039484209847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21607569588242771957892925 8102838595591039484209847)
      ·
        refine ⟨12154257893386559226314771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102838595591039484209847 12154257893386559226314771)
        ·
          refine ⟨18231386840079838839472157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12154257893386559226314771 18231386840079838839472157)
          ·
            refine ⟨6836770065029939564802059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18231386840079838839472157 6836770065029939564802059)
            ·
              refine ⟨10255155097544909347203089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836770065029939564802059 10255155097544909347203089)
              ·
                refine ⟨7691366323158682010402317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10255155097544909347203089 7691366323158682010402317)
                ·
                  refine ⟨2884262371184505753900869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7691366323158682010402317 2884262371184505753900869)
                  ·
                    refine ⟨540799194597094828856413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2884262371184505753900869 540799194597094828856413)
                    ·
                      rfl

theorem cell22_1579804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1579804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579804 prefixEnd_1579804 := by exact prefixLift 1579804
  have htrace : WordTrace (prefixWord ++ tailWord_1579804) baseStart_1579804 baseEnd_1579804 := by
    simpa [prefixWord, tailWord_1579804, baseEnd_1579804] using wordTrace_append hprefix tailTrace_1579804
  have hstable : (prefixWord ++ tailWord_1579804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579804).length < 2 ^ (prefixWord ++ tailWord_1579804).sum := by decide
  have hdescent : baseEnd_1579804 < baseStart_1579804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_1579817 : Nat := 118140960795 + 1579817 * 2 ^ 59
def prefixEnd_1579817 : Nat := 4983230072969 + 3 ^ 40 * 1579817 * 2
def baseEnd_1579817 : Nat := 540803644762767128281373

theorem tailTrace_1579817 : CollatzResearch.WordTrace tailWord_1579817 prefixEnd_1579817 540803644762767128281373 := by
  unfold tailWord_1579817
  simp only [CollatzResearch.WordTrace]
  refine ⟨57620659717600295107937705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38413773145066863405291803 57620659717600295107937705)
  ·
    refine ⟨43215494788200221330953279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57620659717600295107937705 43215494788200221330953279)
    ·
      refine ⟨64823242182300331996429919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43215494788200221330953279 64823242182300331996429919)
      ·
        refine ⟨97234863273450497994644879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64823242182300331996429919 97234863273450497994644879)
        ·
          refine ⟨145852294910175746991967319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97234863273450497994644879 145852294910175746991967319)
          ·
            refine ⟨218778442365263620487950979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145852294910175746991967319 218778442365263620487950979)
            ·
              refine ⟨328167663547895430731926469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218778442365263620487950979 328167663547895430731926469)
              ·
                refine ⟨61531436915230393262236213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328167663547895430731926469 61531436915230393262236213)
                ·
                  refine ⟨5768572210802849368334645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61531436915230393262236213 5768572210802849368334645)
                  ·
                    refine ⟨540803644762767128281373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768572210802849368334645 540803644762767128281373)
                    ·
                      rfl

theorem cell22_1579817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_1579817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579817 prefixEnd_1579817 := by exact prefixLift 1579817
  have htrace : WordTrace (prefixWord ++ tailWord_1579817) baseStart_1579817 baseEnd_1579817 := by
    simpa [prefixWord, tailWord_1579817, baseEnd_1579817] using wordTrace_append hprefix tailTrace_1579817
  have hstable : (prefixWord ++ tailWord_1579817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579817).length < 2 ^ (prefixWord ++ tailWord_1579817).sum := by decide
  have hdescent : baseEnd_1579817 < baseStart_1579817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579838 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1579838 : Nat := 118140960795 + 1579838 * 2 ^ 59
def prefixEnd_1579838 : Nat := 4983230072969 + 3 ^ 40 * 1579838 * 2
def baseEnd_1579838 : Nat := 540810833491930073506309

theorem tailTrace_1579838 : CollatzResearch.WordTrace tailWord_1579838 prefixEnd_1579838 540810833491930073506309 := by
  unfold tailWord_1579838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202678206315526961806521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38414283767016143796301445 7202678206315526961806521)
  ·
    refine ⟨5402008654736645221354891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7202678206315526961806521 5402008654736645221354891)
    ·
      refine ⟨8103012982104967832032337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5402008654736645221354891 8103012982104967832032337)
      ·
        refine ⟨6077259736578725874024253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8103012982104967832032337 6077259736578725874024253)
        ·
          refine ⟨2278972401217022202759095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6077259736578725874024253 2278972401217022202759095)
          ·
            refine ⟨3418458601825533304138643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278972401217022202759095 3418458601825533304138643)
            ·
              refine ⟨5127687902738299956207965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418458601825533304138643 5127687902738299956207965)
              ·
                refine ⟨1922882963526862483577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5127687902738299956207965 1922882963526862483577987)
                ·
                  refine ⟨2884324445290293725366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922882963526862483577987 2884324445290293725366981)
                  ·
                    refine ⟨540810833491930073506309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2884324445290293725366981 540810833491930073506309)
                    ·
                      rfl

theorem cell22_1579838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1579838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579838 prefixEnd_1579838 := by exact prefixLift 1579838
  have htrace : WordTrace (prefixWord ++ tailWord_1579838) baseStart_1579838 baseEnd_1579838 := by
    simpa [prefixWord, tailWord_1579838, baseEnd_1579838] using wordTrace_append hprefix tailTrace_1579838
  have hstable : (prefixWord ++ tailWord_1579838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579838).length < 2 ^ (prefixWord ++ tailWord_1579838).sum := by decide
  have hdescent : baseEnd_1579838 < baseStart_1579838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579853 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1579853 : Nat := 118140960795 + 1579853 * 2 ^ 59
def prefixEnd_1579853 : Nat := 4983230072969 + 3 ^ 40 * 1579853 * 2
def baseEnd_1579853 : Nat := 180271989432825011460421

theorem tailTrace_1579853 : CollatzResearch.WordTrace tailWord_1579853 prefixEnd_1579853 180271989432825011460421 := by
  unfold tailWord_1579853
  simp only [CollatzResearch.WordTrace]
  refine ⟨57621972745469873256248213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38414648496979915504165475 57621972745469873256248213)
  ·
    refine ⟨2701029972443900308886635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57621972745469873256248213 2701029972443900308886635)
    ·
      refine ⟨4051544958665850463329953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701029972443900308886635 4051544958665850463329953)
      ·
        refine ⟨3038658718999387847497465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051544958665850463329953 3038658718999387847497465)
        ·
          refine ⟨2278994039249540885623099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038658718999387847497465 2278994039249540885623099)
          ·
            refine ⟨3418491058874311328434649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278994039249540885623099 3418491058874311328434649)
            ·
              refine ⟨2563868294155733496325987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418491058874311328434649 2563868294155733496325987)
              ·
                refine ⟨3845802441233600244488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563868294155733496325987 3845802441233600244488981)
                ·
                  refine ⟨180271989432825011460421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3845802441233600244488981 180271989432825011460421)
                  ·
                    rfl

theorem cell22_1579853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1579853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579853 prefixEnd_1579853 := by exact prefixLift 1579853
  have htrace : WordTrace (prefixWord ++ tailWord_1579853) baseStart_1579853 baseEnd_1579853 := by
    simpa [prefixWord, tailWord_1579853, baseEnd_1579853] using wordTrace_append hprefix tailTrace_1579853
  have hstable : (prefixWord ++ tailWord_1579853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579853).length < 2 ^ (prefixWord ++ tailWord_1579853).sum := by decide
  have hdescent : baseEnd_1579853 < baseStart_1579853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579868 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1579868 : Nat := 118140960795 + 1579868 * 2 ^ 59
def prefixEnd_1579868 : Nat := 4983230072969 + 3 ^ 40 * 1579868 * 2
def baseEnd_1579868 : Nat := 540821103105019995256217

theorem tailTrace_1579868 : CollatzResearch.WordTrace tailWord_1579868 prefixEnd_1579868 540821103105019995256217 := by
  unfold tailWord_1579868
  simp only [CollatzResearch.WordTrace]
  refine ⟨28811259920207765409022129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38415013226943687212029505 28811259920207765409022129)
  ·
    refine ⟨21608444940155824056766597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28811259920207765409022129 21608444940155824056766597)
    ·
      refine ⟨4051583426279217010643737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21608444940155824056766597 4051583426279217010643737)
      ·
        refine ⟨3038687569709412757982803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051583426279217010643737 3038687569709412757982803)
        ·
          refine ⟨4558031354564119136974205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038687569709412757982803 4558031354564119136974205)
          ·
            refine ⟨1709261757961544676365327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4558031354564119136974205 1709261757961544676365327)
            ·
              refine ⟨2563892636942317014547991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709261757961544676365327 2563892636942317014547991)
              ·
                refine ⟨3845838955413475521821987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563892636942317014547991 3845838955413475521821987)
                ·
                  refine ⟨5768758433120213282732981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845838955413475521821987 5768758433120213282732981)
                  ·
                    refine ⟨540821103105019995256217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768758433120213282732981 540821103105019995256217)
                    ·
                      rfl

theorem cell22_1579868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1579868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579868 prefixEnd_1579868 := by exact prefixLift 1579868
  have htrace : WordTrace (prefixWord ++ tailWord_1579868) baseStart_1579868 baseEnd_1579868 := by
    simpa [prefixWord, tailWord_1579868, baseEnd_1579868] using wordTrace_append hprefix tailTrace_1579868
  have hstable : (prefixWord ++ tailWord_1579868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579868).length < 2 ^ (prefixWord ++ tailWord_1579868).sum := by decide
  have hdescent : baseEnd_1579868 < baseStart_1579868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579909 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 7]
def baseStart_1579909 : Nat := 118140960795 + 1579909 * 2 ^ 59
def prefixEnd_1579909 : Nat := 4983230072969 + 3 ^ 40 * 1579909 * 2
def baseEnd_1579909 : Nat := 180278379414303184993697

theorem tailTrace_1579909 : CollatzResearch.WordTrace tailWord_1579909 prefixEnd_1579909 180278379414303184993697 := by
  unfold tailWord_1579909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57624015233266994820286781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38416010155511329880191187 57624015233266994820286781)
  ·
    refine ⟨21609005712475123057607543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57624015233266994820286781 21609005712475123057607543)
    ·
      refine ⟨32413508568712684586411315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21609005712475123057607543 32413508568712684586411315)
      ·
        refine ⟨48620262853069026879616973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32413508568712684586411315 48620262853069026879616973)
        ·
          refine ⟨18232598569900885079856365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48620262853069026879616973 18232598569900885079856365)
          ·
            refine ⟨6837224463712831904946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18232598569900885079856365 6837224463712831904946137)
            ·
              refine ⟨5127918347784623928709603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6837224463712831904946137 5127918347784623928709603)
              ·
                refine ⟨7691877521676935893064405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127918347784623928709603 7691877521676935893064405)
                ·
                  refine ⟨180278379414303184993697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7691877521676935893064405 180278379414303184993697)
                  ·
                    rfl

theorem cell22_1579909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_1579909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579909 prefixEnd_1579909 := by exact prefixLift 1579909
  have htrace : WordTrace (prefixWord ++ tailWord_1579909) baseStart_1579909 baseEnd_1579909 := by
    simpa [prefixWord, tailWord_1579909, baseEnd_1579909] using wordTrace_append hprefix tailTrace_1579909
  have hstable : (prefixWord ++ tailWord_1579909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579909).length < 2 ^ (prefixWord ++ tailWord_1579909).sum := by decide
  have hdescent : baseEnd_1579909 < baseStart_1579909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579913 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_1579913 : Nat := 118140960795 + 1579913 * 2 ^ 59
def prefixEnd_1579913 : Nat := 4983230072969 + 3 ^ 40 * 1579913 * 2
def baseEnd_1579913 : Nat := 540836507524654877881079

theorem tailTrace_1579913 : CollatzResearch.WordTrace tailWord_1579913 prefixEnd_1579913 540836507524654877881079 := by
  unfold tailWord_1579913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57624161125252503503432393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38416107416835002335621595 57624161125252503503432393)
  ·
    refine ⟨43218120843939377627574295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57624161125252503503432393 43218120843939377627574295)
    ·
      refine ⟨64827181265909066441361443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43218120843939377627574295 64827181265909066441361443)
      ·
        refine ⟨97240771898863599662042165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64827181265909066441361443 97240771898863599662042165)
        ·
          refine ⟨9116322365518462468316453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97240771898863599662042165 9116322365518462468316453)
          ·
            refine ⟨1709310443534711712809335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9116322365518462468316453 1709310443534711712809335)
            ·
              refine ⟨2563965665302067569214003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709310443534711712809335 2563965665302067569214003)
              ·
                refine ⟨3845948497953101353821005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563965665302067569214003 3845948497953101353821005)
                ·
                  refine ⟨1442230686732413007682877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845948497953101353821005 1442230686732413007682877)
                  ·
                    refine ⟨540836507524654877881079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442230686732413007682877 540836507524654877881079)
                    ·
                      rfl

theorem cell22_1579913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_1579913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579913 prefixEnd_1579913 := by exact prefixLift 1579913
  have htrace : WordTrace (prefixWord ++ tailWord_1579913) baseStart_1579913 baseEnd_1579913 := by
    simpa [prefixWord, tailWord_1579913, baseEnd_1579913] using wordTrace_append hprefix tailTrace_1579913
  have hstable : (prefixWord ++ tailWord_1579913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579913).length < 2 ^ (prefixWord ++ tailWord_1579913).sum := by decide
  have hdescent : baseEnd_1579913 < baseStart_1579913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579971 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 4]
def baseStart_1579971 : Nat := 118140960795 + 1579971 * 2 ^ 59
def prefixEnd_1579971 : Nat := 4983230072969 + 3 ^ 40 * 1579971 * 2
def baseEnd_1579971 : Nat := 180285454036654019976967

theorem tailTrace_1579971 : CollatzResearch.WordTrace tailWord_1579971 prefixEnd_1579971 180285454036654019976967 := by
  unfold tailWord_1579971
  simp only [CollatzResearch.WordTrace]
  refine ⟨57626276559042379409043767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38417517706028252939362511 57626276559042379409043767)
  ·
    refine ⟨86439414838563569113565651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57626276559042379409043767 86439414838563569113565651)
    ·
      refine ⟨129659122257845353670348477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86439414838563569113565651 129659122257845353670348477)
      ·
        refine ⟨48622170846692007626380679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129659122257845353670348477 48622170846692007626380679)
        ·
          refine ⟨72933256270038011439571019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48622170846692007626380679 72933256270038011439571019)
          ·
            refine ⟨109399884405057017159356529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72933256270038011439571019 109399884405057017159356529)
            ·
              refine ⟨82049913303792762869517397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109399884405057017159356529 82049913303792762869517397)
              ·
                refine ⟨961522421528821439877157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 82049913303792762869517397 961522421528821439877157)
                ·
                  refine ⟨180285454036654019976967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961522421528821439877157 180285454036654019976967)
                  ·
                    rfl

theorem cell22_1579971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 4].length) (baseStart_1579971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579971 prefixEnd_1579971 := by exact prefixLift 1579971
  have htrace : WordTrace (prefixWord ++ tailWord_1579971) baseStart_1579971 baseEnd_1579971 := by
    simpa [prefixWord, tailWord_1579971, baseEnd_1579971] using wordTrace_append hprefix tailTrace_1579971
  have hstable : (prefixWord ++ tailWord_1579971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579971).length < 2 ^ (prefixWord ++ tailWord_1579971).sum := by decide
  have hdescent : baseEnd_1579971 < baseStart_1579971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579984 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_1579984 : Nat := 118140960795 + 1579984 * 2 ^ 59
def prefixEnd_1579984 : Nat := 4983230072969 + 3 ^ 40 * 1579984 * 2
def baseEnd_1579984 : Nat := 540860812275634359355861

theorem tailTrace_1579984 : CollatzResearch.WordTrace tailWord_1579984 prefixEnd_1579984 540860812275634359355861 := by
  unfold tailWord_1579984
  simp only [CollatzResearch.WordTrace]
  refine ⟨28813375353997641314633503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38417833805330188419511337 28813375353997641314633503)
  ·
    refine ⟨43220063030996461971950255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28813375353997641314633503 43220063030996461971950255)
    ·
      refine ⟨64830094546494692957925383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43220063030996461971950255 64830094546494692957925383)
      ·
        refine ⟨97245141819742039436888075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64830094546494692957925383 97245141819742039436888075)
        ·
          refine ⟨145867712729613059155332113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97245141819742039436888075 145867712729613059155332113)
          ·
            refine ⟨109400784547209794366499085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145867712729613059155332113 109400784547209794366499085)
            ·
              refine ⟨41025294205203672887437157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109400784547209794366499085 41025294205203672887437157)
              ·
                refine ⟨7692242663475688666394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41025294205203672887437157 7692242663475688666394467)
                ·
                  refine ⟨11538363995213532999591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7692242663475688666394467 11538363995213532999591701)
                  ·
                    refine ⟨540860812275634359355861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11538363995213532999591701 540860812275634359355861)
                    ·
                      rfl

theorem cell22_1579984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_1579984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1579984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1579984 prefixEnd_1579984 := by exact prefixLift 1579984
  have htrace : WordTrace (prefixWord ++ tailWord_1579984) baseStart_1579984 baseEnd_1579984 := by
    simpa [prefixWord, tailWord_1579984, baseEnd_1579984] using wordTrace_append hprefix tailTrace_1579984
  have hstable : (prefixWord ++ tailWord_1579984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579984).length < 2 ^ (prefixWord ++ tailWord_1579984).sum := by decide
  have hdescent : baseEnd_1579984 < baseStart_1579984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580078 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1580078 : Nat := 118140960795 + 1580078 * 2 ^ 59
def prefixEnd_1580078 : Nat := 4983230072969 + 3 ^ 40 * 1580078 * 2
def baseEnd_1580078 : Nat := 180297663465549815835191

theorem tailTrace_1580078 : CollatzResearch.WordTrace tailWord_1580078 prefixEnd_1580078 180297663465549815835191 := by
  unfold tailWord_1580078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203772396206842085398611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38420119446436491122125925 7203772396206842085398611)
  ·
    refine ⟨10805658594310263128097917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7203772396206842085398611 10805658594310263128097917)
    ·
      refine ⟨4052121972866348673036719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10805658594310263128097917 4052121972866348673036719)
      ·
        refine ⟨6078182959299523009555079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052121972866348673036719 6078182959299523009555079)
        ·
          refine ⟨9117274438949284514332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078182959299523009555079 9117274438949284514332619)
          ·
            refine ⟨13675911658423926771498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117274438949284514332619 13675911658423926771498929)
            ·
              refine ⟨10256933743817945078624197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13675911658423926771498929 10256933743817945078624197)
              ·
                refine ⟨1923175076965864702242037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10256933743817945078624197 1923175076965864702242037)
                ·
                  refine ⟨180297663465549815835191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923175076965864702242037 180297663465549815835191)
                  ·
                    rfl

theorem cell22_1580078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1580078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580078 prefixEnd_1580078 := by exact prefixLift 1580078
  have htrace : WordTrace (prefixWord ++ tailWord_1580078) baseStart_1580078 baseEnd_1580078 := by
    simpa [prefixWord, tailWord_1580078, baseEnd_1580078] using wordTrace_append hprefix tailTrace_1580078
  have hstable : (prefixWord ++ tailWord_1580078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580078).length < 2 ^ (prefixWord ++ tailWord_1580078).sum := by decide
  have hdescent : baseEnd_1580078 < baseStart_1580078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580082 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_1580082 : Nat := 118140960795 + 1580082 * 2 ^ 59
def prefixEnd_1580082 : Nat := 4983230072969 + 3 ^ 40 * 1580082 * 2
def baseEnd_1580082 : Nat := 540894359678394770405561

theorem tailTrace_1580082 : CollatzResearch.WordTrace tailWord_1580082 prefixEnd_1580082 540894359678394770405561 := by
  unfold tailWord_1580082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407581265410061341583625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38420216707760163577556333 14407581265410061341583625)
  ·
    refine ⟨10805685949057546006187719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14407581265410061341583625 10805685949057546006187719)
    ·
      refine ⟨16208528923586319009281579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10805685949057546006187719 16208528923586319009281579)
      ·
        refine ⟨24312793385379478513922369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16208528923586319009281579 24312793385379478513922369)
        ·
          refine ⟨18234595039034608885441777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24312793385379478513922369 18234595039034608885441777)
          ·
            refine ⟨13675946279275956664081333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18234595039034608885441777 13675946279275956664081333)
            ·
              refine ⟨1282119963682120937257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13675946279275956664081333 1282119963682120937257625)
              ·
                refine ⟨961589972761590702943219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282119963682120937257625 961589972761590702943219)
                ·
                  refine ⟨1442384959142386054414829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961589972761590702943219 1442384959142386054414829)
                  ·
                    refine ⟨540894359678394770405561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442384959142386054414829 540894359678394770405561)
                    ·
                      rfl

theorem cell22_1580082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_1580082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580082 prefixEnd_1580082 := by exact prefixLift 1580082
  have htrace : WordTrace (prefixWord ++ tailWord_1580082) baseStart_1580082 baseEnd_1580082 := by
    simpa [prefixWord, tailWord_1580082, baseEnd_1580082] using wordTrace_append hprefix tailTrace_1580082
  have hstable : (prefixWord ++ tailWord_1580082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580082).length < 2 ^ (prefixWord ++ tailWord_1580082).sum := by decide
  have hdescent : baseEnd_1580082 < baseStart_1580082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580106 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_1580106 : Nat := 118140960795 + 1580106 * 2 ^ 59
def prefixEnd_1580106 : Nat := 4983230072969 + 3 ^ 40 * 1580106 * 2
def baseEnd_1580106 : Nat := 180300858456288902601829

theorem tailTrace_1580106 : CollatzResearch.WordTrace tailWord_1580106 prefixEnd_1580106 180300858456288902601829 := by
  unfold tailWord_1580106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407800103388324366302043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38420800275702198310138781 14407800103388324366302043)
  ·
    refine ⟨21611700155082486549453065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14407800103388324366302043 21611700155082486549453065)
    ·
      refine ⟨16208775116311864912089799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21611700155082486549453065 16208775116311864912089799)
      ·
        refine ⟨24313162674467797368134699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16208775116311864912089799 24313162674467797368134699)
        ·
          refine ⟨36469744011701696052202049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24313162674467797368134699 36469744011701696052202049)
          ·
            refine ⟨27352308008776272039151537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36469744011701696052202049 27352308008776272039151537)
            ·
              refine ⟨20514231006582204029363653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27352308008776272039151537 20514231006582204029363653)
              ·
                refine ⟨3846418313734163255505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20514231006582204029363653 3846418313734163255505685)
                ·
                  refine ⟨180300858456288902601829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3846418313734163255505685 180300858456288902601829)
                  ·
                    rfl

theorem cell22_1580106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_1580106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580106 prefixEnd_1580106 := by exact prefixLift 1580106
  have htrace : WordTrace (prefixWord ++ tailWord_1580106) baseStart_1580106 baseEnd_1580106 := by
    simpa [prefixWord, tailWord_1580106, baseEnd_1580106] using wordTrace_append hprefix tailTrace_1580106
  have hstable : (prefixWord ++ tailWord_1580106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580106).length < 2 ^ (prefixWord ++ tailWord_1580106).sum := by decide
  have hdescent : baseEnd_1580106 < baseStart_1580106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580181 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1580181 : Nat := 118140960795 + 1580181 * 2 ^ 59
def prefixEnd_1580181 : Nat := 4983230072969 + 3 ^ 40 * 1580181 * 2
def baseEnd_1580181 : Nat := 540928249401591512180257

theorem tailTrace_1580181 : CollatzResearch.WordTrace tailWord_1580181 prefixEnd_1580181 540928249401591512180257 := by
  unfold tailWord_1580181
  simp only [CollatzResearch.WordTrace]
  refine ⟨57633935888281585274188397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38422623925521056849458931 57633935888281585274188397)
  ·
    refine ⟨21612725958105594477820649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57633935888281585274188397 21612725958105594477820649)
    ·
      refine ⟨16209544468579195858365487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21612725958105594477820649 16209544468579195858365487)
      ·
        refine ⟨24314316702868793787548231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16209544468579195858365487 24314316702868793787548231)
        ·
          refine ⟨36471475054303190681322347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24314316702868793787548231 36471475054303190681322347)
          ·
            refine ⟨54707212581454786021983521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36471475054303190681322347 54707212581454786021983521)
            ·
              refine ⟨41030409436091089516487641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54707212581454786021983521 41030409436091089516487641)
              ·
                refine ⟨30772807077068317137365731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41030409436091089516487641 30772807077068317137365731)
                ·
                  refine ⟨46159210615602475706048597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30772807077068317137365731 46159210615602475706048597)
                  ·
                    refine ⟨540928249401591512180257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46159210615602475706048597 540928249401591512180257)
                    ·
                      rfl

theorem cell22_1580181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1580181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580181 prefixEnd_1580181 := by exact prefixLift 1580181
  have htrace : WordTrace (prefixWord ++ tailWord_1580181) baseStart_1580181 baseEnd_1580181 := by
    simpa [prefixWord, tailWord_1580181, baseEnd_1580181] using wordTrace_append hprefix tailTrace_1580181
  have hstable : (prefixWord ++ tailWord_1580181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580181).length < 2 ^ (prefixWord ++ tailWord_1580181).sum := by decide
  have hdescent : baseEnd_1580181 < baseStart_1580181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580234 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_1580234 : Nat := 118140960795 + 1580234 * 2 ^ 59
def prefixEnd_1580234 : Nat := 4983230072969 + 3 ^ 40 * 1580234 * 2
def baseEnd_1580234 : Nat := 540946392384717040605095

theorem tailTrace_1580234 : CollatzResearch.WordTrace tailWord_1580234 prefixEnd_1580234 540946392384717040605095 := by
  unfold tailWord_1580234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408967239272393831466939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38423912638059716883911837 14408967239272393831466939)
  ·
    refine ⟨21613450858908590747200409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14408967239272393831466939 21613450858908590747200409)
    ·
      refine ⟨16210088144181443060400307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21613450858908590747200409 16210088144181443060400307)
      ·
        refine ⟨24315132216272164590600461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16210088144181443060400307 24315132216272164590600461)
        ·
          refine ⟨9118174581102061721475173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24315132216272164590600461 9118174581102061721475173)
          ·
            refine ⟨1709657733956636572776595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9118174581102061721475173 1709657733956636572776595)
            ·
              refine ⟨2564486600934954859164893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709657733956636572776595 2564486600934954859164893)
              ·
                refine ⟨961682475350608072186835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2564486600934954859164893 961682475350608072186835)
                ·
                  refine ⟨1442523713025912108280253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961682475350608072186835 1442523713025912108280253)
                  ·
                    refine ⟨540946392384717040605095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442523713025912108280253 540946392384717040605095)
                    ·
                      rfl

theorem cell22_1580234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_1580234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580234 prefixEnd_1580234 := by exact prefixLift 1580234
  have htrace : WordTrace (prefixWord ++ tailWord_1580234) baseStart_1580234 baseEnd_1580234 := by
    simpa [prefixWord, tailWord_1580234, baseEnd_1580234] using wordTrace_append hprefix tailTrace_1580234
  have hstable : (prefixWord ++ tailWord_1580234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580234).length < 2 ^ (prefixWord ++ tailWord_1580234).sum := by decide
  have hdescent : baseEnd_1580234 < baseStart_1580234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580273 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1580273 : Nat := 118140960795 + 1580273 * 2 ^ 59
def prefixEnd_1580273 : Nat := 4983230072969 + 3 ^ 40 * 1580273 * 2
def baseEnd_1580273 : Nat := 540959742881733938879975

theorem tailTrace_1580273 : CollatzResearch.WordTrace tailWord_1580273 prefixEnd_1580273 540959742881733938879975 := by
  unfold tailWord_1580273
  simp only [CollatzResearch.WordTrace]
  refine ⟨57637291403948284986537473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38424860935965523324358315 57637291403948284986537473)
  ·
    refine ⟨43227968552961213739903105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57637291403948284986537473 43227968552961213739903105)
    ·
      refine ⟨32420976414720910304927329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43227968552961213739903105 32420976414720910304927329)
      ·
        refine ⟨24315732311040682728695497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32420976414720910304927329 24315732311040682728695497)
        ·
          refine ⟨18236799233280512046521623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24315732311040682728695497 18236799233280512046521623)
          ·
            refine ⟨27355198849920768069782435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236799233280512046521623 27355198849920768069782435)
            ·
              refine ⟨41032798274881152104673653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27355198849920768069782435 41032798274881152104673653)
              ·
                refine ⟨3846824838270108009813155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41032798274881152104673653 3846824838270108009813155)
                ·
                  refine ⟨5770237257405162014719733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846824838270108009813155 5770237257405162014719733)
                  ·
                    refine ⟨540959742881733938879975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5770237257405162014719733 540959742881733938879975)
                    ·
                      rfl

theorem cell22_1580273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1580273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580273 prefixEnd_1580273 := by exact prefixLift 1580273
  have htrace : WordTrace (prefixWord ++ tailWord_1580273) baseStart_1580273 baseEnd_1580273 := by
    simpa [prefixWord, tailWord_1580273, baseEnd_1580273] using wordTrace_append hprefix tailTrace_1580273
  have hstable : (prefixWord ++ tailWord_1580273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580273).length < 2 ^ (prefixWord ++ tailWord_1580273).sum := by decide
  have hdescent : baseEnd_1580273 < baseStart_1580273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580393 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 8]
def baseStart_1580393 : Nat := 118140960795 + 1580393 * 2 ^ 59
def prefixEnd_1580393 : Nat := 4983230072969 + 3 ^ 40 * 1580393 * 2
def baseEnd_1580393 : Nat := 180333607111364541959869

theorem tailTrace_1580393 : CollatzResearch.WordTrace tailWord_1580393 prefixEnd_1580393 180333607111364541959869 := by
  unfold tailWord_1580393
  simp only [CollatzResearch.WordTrace]
  refine ⟨57641668163513545480905833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38427778775675696987270555 57641668163513545480905833)
  ·
    refine ⟨43231251122635159110679375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57641668163513545480905833 43231251122635159110679375)
    ·
      refine ⟨64846876683952738666019063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43231251122635159110679375 64846876683952738666019063)
      ·
        refine ⟨97270315025929107999028595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64846876683952738666019063 97270315025929107999028595)
        ·
          refine ⟨145905472538893661998542893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97270315025929107999028595 145905472538893661998542893)
          ·
            refine ⟨54714552202085123249453585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145905472538893661998542893 54714552202085123249453585)
            ·
              refine ⟨41035914151563842437090189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54714552202085123249453585 41035914151563842437090189)
              ·
                refine ⟨15388467806836440913908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41035914151563842437090189 15388467806836440913908821)
                ·
                  refine ⟨180333607111364541959869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15388467806836440913908821 180333607111364541959869)
                  ·
                    rfl

theorem cell22_1580393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_1580393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580393 prefixEnd_1580393 := by exact prefixLift 1580393
  have htrace : WordTrace (prefixWord ++ tailWord_1580393) baseStart_1580393 baseEnd_1580393 := by
    simpa [prefixWord, tailWord_1580393, baseEnd_1580393] using wordTrace_append hprefix tailTrace_1580393
  have hstable : (prefixWord ++ tailWord_1580393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580393).length < 2 ^ (prefixWord ++ tailWord_1580393).sum := by decide
  have hdescent : baseEnd_1580393 < baseStart_1580393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580455 : List Nat := [1, 1, 6, 1, 1, 1, 1, 10]
def baseStart_1580455 : Nat := 118140960795 + 1580455 * 2 ^ 59
def prefixEnd_1580455 : Nat := 4983230072969 + 3 ^ 40 * 1580455 * 2
def baseEnd_1580455 : Nat := 60113560577905125647713

theorem tailTrace_1580455 : CollatzResearch.WordTrace tailWord_1580455 prefixEnd_1580455 60113560577905125647713 := by
  unfold tailWord_1580455
  simp only [CollatzResearch.WordTrace]
  refine ⟨57643929489288930069662819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38429286326192620046441879 57643929489288930069662819)
  ·
    refine ⟨86465894233933395104494229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57643929489288930069662819 86465894233933395104494229)
    ·
      refine ⟨4053088792215627895523167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86465894233933395104494229 4053088792215627895523167)
      ·
        refine ⟨6079633188323441843284751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053088792215627895523167 6079633188323441843284751)
        ·
          refine ⟨9119449782485162764927127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079633188323441843284751 9119449782485162764927127)
          ·
            refine ⟨13679174673727744147390691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119449782485162764927127 13679174673727744147390691)
            ·
              refine ⟨20518762010591616221086037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13679174673727744147390691 20518762010591616221086037)
              ·
                refine ⟨60113560577905125647713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20518762010591616221086037 60113560577905125647713)
                ·
                  rfl

theorem cell22_1580455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 10].length) (baseStart_1580455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580455 prefixEnd_1580455 := by exact prefixLift 1580455
  have htrace : WordTrace (prefixWord ++ tailWord_1580455) baseStart_1580455 baseEnd_1580455 := by
    simpa [prefixWord, tailWord_1580455, baseEnd_1580455] using wordTrace_append hprefix tailTrace_1580455
  have hstable : (prefixWord ++ tailWord_1580455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580455).length < 2 ^ (prefixWord ++ tailWord_1580455).sum := by decide
  have hdescent : baseEnd_1580455 < baseStart_1580455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580476 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1580476 : Nat := 118140960795 + 1580476 * 2 ^ 59
def prefixEnd_1580476 : Nat := 4983230072969 + 3 ^ 40 * 1580476 * 2
def baseEnd_1580476 : Nat := 541029233930309076054353

theorem tailTrace_1580476 : CollatzResearch.WordTrace tailWord_1580476 prefixEnd_1580476 541029233930309076054353 := by
  unfold tailWord_1580476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822347711106425328088641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38429796948141900437451521 28822347711106425328088641)
  ·
    refine ⟨21616760783329818996066481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28822347711106425328088641 21616760783329818996066481)
    ·
      refine ⟨16212570587497364247049861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21616760783329818996066481 16212570587497364247049861)
      ·
        refine ⟨3039856985155755796321849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16212570587497364247049861 3039856985155755796321849)
        ·
          refine ⟨2279892738866816847241387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3039856985155755796321849 2279892738866816847241387)
          ·
            refine ⟨3419839108300225270862081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279892738866816847241387 3419839108300225270862081)
            ·
              refine ⟨2564879331225168953146561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3419839108300225270862081 2564879331225168953146561)
              ·
                refine ⟨1923659498418876714859921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564879331225168953146561 1923659498418876714859921)
                ·
                  refine ⟨1442744623814157536144941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923659498418876714859921 1442744623814157536144941)
                  ·
                    refine ⟨541029233930309076054353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442744623814157536144941 541029233930309076054353)
                    ·
                      rfl

theorem cell22_1580476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1580476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580476 prefixEnd_1580476 := by exact prefixLift 1580476
  have htrace : WordTrace (prefixWord ++ tailWord_1580476) baseStart_1580476 baseEnd_1580476 := by
    simpa [prefixWord, tailWord_1580476, baseEnd_1580476] using wordTrace_append hprefix tailTrace_1580476
  have hstable : (prefixWord ++ tailWord_1580476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580476).length < 2 ^ (prefixWord ++ tailWord_1580476).sum := by decide
  have hdescent : baseEnd_1580476 < baseStart_1580476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580487 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 3, 3]
def baseStart_1580487 : Nat := 118140960795 + 1580487 * 2 ^ 59
def prefixEnd_1580487 : Nat := 4983230072969 + 3 ^ 40 * 1580487 * 2
def baseEnd_1580487 : Nat := 541032999455108714029319

theorem tailTrace_1580487 : CollatzResearch.WordTrace tailWord_1580487 prefixEnd_1580487 541032999455108714029319 := by
  unfold tailWord_1580487
  simp only [CollatzResearch.WordTrace]
  refine ⟨57645096625172999534827715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38430064416781999689885143 57645096625172999534827715)
  ·
    refine ⟨86467644937759499302241573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57645096625172999534827715 86467644937759499302241573)
    ·
      refine ⟨16212683425829906119170295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86467644937759499302241573 16212683425829906119170295)
      ·
        refine ⟨24319025138744859178755443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212683425829906119170295 24319025138744859178755443)
        ·
          refine ⟨36478537708117288768133165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24319025138744859178755443 36478537708117288768133165)
          ·
            refine ⟨13679451640543983288049937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36478537708117288768133165 13679451640543983288049937)
            ·
              refine ⟨10259588730407987466037453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679451640543983288049937 10259588730407987466037453)
              ·
                refine ⟨3847345773902995299764045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10259588730407987466037453 3847345773902995299764045)
                ·
                  refine ⟨1442754665213623237411517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3847345773902995299764045 1442754665213623237411517)
                  ·
                    refine ⟨541032999455108714029319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442754665213623237411517 541032999455108714029319)
                    ·
                      rfl

theorem cell22_1580487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_1580487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580487 prefixEnd_1580487 := by exact prefixLift 1580487
  have htrace : WordTrace (prefixWord ++ tailWord_1580487) baseStart_1580487 baseEnd_1580487 := by
    simpa [prefixWord, tailWord_1580487, baseEnd_1580487] using wordTrace_append hprefix tailTrace_1580487
  have hstable : (prefixWord ++ tailWord_1580487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580487).length < 2 ^ (prefixWord ++ tailWord_1580487).sum := by decide
  have hdescent : baseEnd_1580487 < baseStart_1580487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580534 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1580534 : Nat := 118140960795 + 1580534 * 2 ^ 59
def prefixEnd_1580534 : Nat := 4983230072969 + 3 ^ 40 * 1580534 * 2
def baseEnd_1580534 : Nat := 180349696171872086034725

theorem tailTrace_1580534 : CollatzResearch.WordTrace tailWord_1580534 prefixEnd_1580534 180349696171872086034725 := by
  unfold tailWord_1580534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602925678500170410111791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38431207237335151041192437 3602925678500170410111791)
  ·
    refine ⟨5404388517750255615167687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3602925678500170410111791 5404388517750255615167687)
    ·
      refine ⟨8106582776625383422751531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404388517750255615167687 8106582776625383422751531)
      ·
        refine ⟨12159874164938075134127297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8106582776625383422751531 12159874164938075134127297)
        ·
          refine ⟨9119905623703556350595473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12159874164938075134127297 9119905623703556350595473)
          ·
            refine ⟨6839929217777667262946605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9119905623703556350595473 6839929217777667262946605)
            ·
              refine ⟨2564973456666625223604977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839929217777667262946605 2564973456666625223604977)
              ·
                refine ⟨1923730092499968917703733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564973456666625223604977 1923730092499968917703733)
                ·
                  refine ⟨180349696171872086034725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923730092499968917703733 180349696171872086034725)
                  ·
                    rfl

theorem cell22_1580534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1580534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580534 prefixEnd_1580534 := by exact prefixLift 1580534
  have htrace : WordTrace (prefixWord ++ tailWord_1580534) baseStart_1580534 baseEnd_1580534 := by
    simpa [prefixWord, tailWord_1580534, baseEnd_1580534] using wordTrace_append hprefix tailTrace_1580534
  have hstable : (prefixWord ++ tailWord_1580534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580534).length < 2 ^ (prefixWord ++ tailWord_1580534).sum := by decide
  have hdescent : baseEnd_1580534 < baseStart_1580534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580594 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1580594 : Nat := 118140960795 + 1580594 * 2 ^ 59
def prefixEnd_1580594 : Nat := 4983230072969 + 3 ^ 40 * 1580594 * 2
def baseEnd_1580594 : Nat := 541069627741796101603991

theorem tailTrace_1580594 : CollatzResearch.WordTrace tailWord_1580594 prefixEnd_1580594 541069627741796101603991 := by
  unfold tailWord_1580594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412249808946339202243209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38432666157190237872648557 14412249808946339202243209)
  ·
    refine ⟨10809187356709754401682407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14412249808946339202243209 10809187356709754401682407)
    ·
      refine ⟨16213781035064631602523611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809187356709754401682407 16213781035064631602523611)
      ·
        refine ⟨24320671552596947403785417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16213781035064631602523611 24320671552596947403785417)
        ·
          refine ⟨18240503664447710552839063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24320671552596947403785417 18240503664447710552839063)
          ·
            refine ⟨27360755496671565829258595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240503664447710552839063 27360755496671565829258595)
            ·
              refine ⟨41041133245007348743887893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27360755496671565829258595 41041133245007348743887893)
              ·
                refine ⟨1923803120859719472369745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41041133245007348743887893 1923803120859719472369745)
                ·
                  refine ⟨1442852340644789604277309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923803120859719472369745 1442852340644789604277309)
                  ·
                    refine ⟨541069627741796101603991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442852340644789604277309 541069627741796101603991)
                    ·
                      rfl

theorem cell22_1580594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1580594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580594 prefixEnd_1580594 := by exact prefixLift 1580594
  have htrace : WordTrace (prefixWord ++ tailWord_1580594) baseStart_1580594 baseEnd_1580594 := by
    simpa [prefixWord, tailWord_1580594, baseEnd_1580594] using wordTrace_append hprefix tailTrace_1580594
  have hstable : (prefixWord ++ tailWord_1580594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580594).length < 2 ^ (prefixWord ++ tailWord_1580594).sum := by decide
  have hdescent : baseEnd_1580594 < baseStart_1580594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580607 : List Nat := [1, 1, 2, 2, 3, 4, 2, 7]
def baseStart_1580607 : Nat := 118140960795 + 1580607 * 2 ^ 59
def prefixEnd_1580607 : Nat := 4983230072969 + 3 ^ 40 * 1580607 * 2
def baseEnd_1580607 : Nat := 60119341989718711225439

theorem tailTrace_1580607 : CollatzResearch.WordTrace tailWord_1580607 prefixEnd_1580607 60119341989718711225439 := by
  unfold tailWord_1580607
  simp only [CollatzResearch.WordTrace]
  refine ⟨57649473384738260029196075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38432982256492173352797383 57649473384738260029196075)
  ·
    refine ⟨86474210077107390043794113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57649473384738260029196075 86474210077107390043794113)
    ·
      refine ⟨64855657557830542532845585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86474210077107390043794113 64855657557830542532845585)
      ·
        refine ⟨48641743168372906899634189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64855657557830542532845585 48641743168372906899634189)
        ·
          refine ⟨18240653688139840087362821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48641743168372906899634189 18240653688139840087362821)
          ·
            refine ⟨3420122566526220016380529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18240653688139840087362821 3420122566526220016380529)
            ·
              refine ⟨2565091924894665012285397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420122566526220016380529 2565091924894665012285397)
              ·
                refine ⟨60119341989718711225439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2565091924894665012285397 60119341989718711225439)
                ·
                  rfl

theorem cell22_1580607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 7].length) (baseStart_1580607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580607 prefixEnd_1580607 := by exact prefixLift 1580607
  have htrace : WordTrace (prefixWord ++ tailWord_1580607) baseStart_1580607 baseEnd_1580607 := by
    simpa [prefixWord, tailWord_1580607, baseEnd_1580607] using wordTrace_append hprefix tailTrace_1580607
  have hstable : (prefixWord ++ tailWord_1580607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580607).length < 2 ^ (prefixWord ++ tailWord_1580607).sum := by decide
  have hdescent : baseEnd_1580607 < baseStart_1580607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580667 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_1580667 : Nat := 118140960795 + 1580667 * 2 ^ 59
def prefixEnd_1580667 : Nat := 4983230072969 + 3 ^ 40 * 1580667 * 2
def baseEnd_1580667 : Nat := 541094617133648244528767

theorem tailTrace_1580667 : CollatzResearch.WordTrace tailWord_1580667 prefixEnd_1580667 541094617133648244528767 := by
  unfold tailWord_1580667
  simp only [CollatzResearch.WordTrace]
  refine ⟨57651661764520890276380255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38434441176347260184253503 57651661764520890276380255)
  ·
    refine ⟨86477492646781335414570383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57651661764520890276380255 86477492646781335414570383)
    ·
      refine ⟨129716238970172003121855575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86477492646781335414570383 129716238970172003121855575)
      ·
        refine ⟨194574358455258004682783363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129716238970172003121855575 194574358455258004682783363)
        ·
          refine ⟨291861537682887007024175045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194574358455258004682783363 291861537682887007024175045)
          ·
            refine ⟨54724038315541313817032821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291861537682887007024175045 54724038315541313817032821)
            ·
              refine ⟨5130378592081998170346827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54724038315541313817032821 5130378592081998170346827)
              ·
                refine ⟨7695567888122997255520241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130378592081998170346827 7695567888122997255520241)
                ·
                  refine ⟨5771675916092247941640181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695567888122997255520241 5771675916092247941640181)
                  ·
                    refine ⟨541094617133648244528767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5771675916092247941640181 541094617133648244528767)
                    ·
                      rfl

theorem cell22_1580667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_1580667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580667 prefixEnd_1580667 := by exact prefixLift 1580667
  have htrace : WordTrace (prefixWord ++ tailWord_1580667) baseStart_1580667 baseEnd_1580667 := by
    simpa [prefixWord, tailWord_1580667, baseEnd_1580667] using wordTrace_append hprefix tailTrace_1580667
  have hstable : (prefixWord ++ tailWord_1580667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580667).length < 2 ^ (prefixWord ++ tailWord_1580667).sum := by decide
  have hdescent : baseEnd_1580667 < baseStart_1580667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580669 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 5]
def baseStart_1580669 : Nat := 118140960795 + 1580669 * 2 ^ 59
def prefixEnd_1580669 : Nat := 4983230072969 + 3 ^ 40 * 1580669 * 2
def baseEnd_1580669 : Nat := 180365100591506968659587

theorem tailTrace_1580669 : CollatzResearch.WordTrace tailWord_1580669 prefixEnd_1580669 180365100591506968659587 := by
  unfold tailWord_1580669
  simp only [CollatzResearch.WordTrace]
  refine ⟨57651734710513644617953061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38434489807009096411968707 57651734710513644617953061)
  ·
    refine ⟨10809700258221308365866199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57651734710513644617953061 10809700258221308365866199)
    ·
      refine ⟨16214550387331962548799299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809700258221308365866199 16214550387331962548799299)
      ·
        refine ⟨24321825580997943823198949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16214550387331962548799299 24321825580997943823198949)
        ·
          refine ⟨4560342296437114466849803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24321825580997943823198949 4560342296437114466849803)
          ·
            refine ⟨6840513444655671700274705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560342296437114466849803 6840513444655671700274705)
            ·
              refine ⟨5130385083491753775206029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840513444655671700274705 5130385083491753775206029)
              ·
                refine ⟨1923894406309407665702261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5130385083491753775206029 1923894406309407665702261)
                ·
                  refine ⟨180365100591506968659587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923894406309407665702261 180365100591506968659587)
                  ·
                    rfl

theorem cell22_1580669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_1580669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580669 prefixEnd_1580669 := by exact prefixLift 1580669
  have htrace : WordTrace (prefixWord ++ tailWord_1580669) baseStart_1580669 baseEnd_1580669 := by
    simpa [prefixWord, tailWord_1580669, baseEnd_1580669] using wordTrace_append hprefix tailTrace_1580669
  have hstable : (prefixWord ++ tailWord_1580669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580669).length < 2 ^ (prefixWord ++ tailWord_1580669).sum := by decide
  have hdescent : baseEnd_1580669 < baseStart_1580669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580690 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1580690 : Nat := 118140960795 + 1580690 * 2 ^ 59
def prefixEnd_1580690 : Nat := 4983230072969 + 3 ^ 40 * 1580690 * 2
def baseEnd_1580690 : Nat := 541102490503683851203697

theorem tailTrace_1580690 : CollatzResearch.WordTrace tailWord_1580690 prefixEnd_1580690 541102490503683851203697 := by
  unfold tailWord_1580690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413125160859391301116881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38435000428958376802978349 14413125160859391301116881)
  ·
    refine ⟨10809843870644543475837661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14413125160859391301116881 10809843870644543475837661)
    ·
      refine ⟨4053691451491703803439123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10809843870644543475837661 4053691451491703803439123)
      ·
        refine ⟨6080537177237555705158685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053691451491703803439123 6080537177237555705158685)
        ·
          refine ⟨2280201441464083389434507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6080537177237555705158685 2280201441464083389434507)
          ·
            refine ⟨3420302162196125084151761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280201441464083389434507 3420302162196125084151761)
            ·
              refine ⟨2565226621647093813113821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420302162196125084151761 2565226621647093813113821)
              ·
                refine ⟨961959983117660179917683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565226621647093813113821 961959983117660179917683)
                ·
                  refine ⟨1442939974676490269876525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961959983117660179917683 1442939974676490269876525)
                  ·
                    refine ⟨541102490503683851203697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442939974676490269876525 541102490503683851203697)
                    ·
                      rfl

theorem cell22_1580690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1580690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580690 prefixEnd_1580690 := by exact prefixLift 1580690
  have htrace : WordTrace (prefixWord ++ tailWord_1580690) baseStart_1580690 baseEnd_1580690 := by
    simpa [prefixWord, tailWord_1580690, baseEnd_1580690] using wordTrace_append hprefix tailTrace_1580690
  have hstable : (prefixWord ++ tailWord_1580690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580690).length < 2 ^ (prefixWord ++ tailWord_1580690).sum := by decide
  have hdescent : baseEnd_1580690 < baseStart_1580690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580703 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 5]
def baseStart_1580703 : Nat := 118140960795 + 1580703 * 2 ^ 59
def prefixEnd_1580703 : Nat := 4983230072969 + 3 ^ 40 * 1580703 * 2
def baseEnd_1580703 : Nat := 180368980223118716876219

theorem tailTrace_1580703 : CollatzResearch.WordTrace tailWord_1580703 prefixEnd_1580703 180368980223118716876219 := by
  unfold tailWord_1580703
  simp only [CollatzResearch.WordTrace]
  refine ⟨57652974792390468424690763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38435316528260312283127175 57652974792390468424690763)
  ·
    refine ⟨86479462188585702637036145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57652974792390468424690763 86479462188585702637036145)
    ·
      refine ⟨64859596641439276977777109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86479462188585702637036145 64859596641439276977777109)
      ·
        refine ⟨1520146796283733054166651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64859596641439276977777109 1520146796283733054166651)
        ·
          refine ⟨2280220194425599581249977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520146796283733054166651 2280220194425599581249977)
          ·
            refine ⟨1710165145819199685937483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280220194425599581249977 1710165145819199685937483)
            ·
              refine ⟨2565247718728799528906225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710165145819199685937483 2565247718728799528906225)
              ·
                refine ⟨1923935789046599646679669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565247718728799528906225 1923935789046599646679669)
                ·
                  refine ⟨180368980223118716876219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923935789046599646679669 180368980223118716876219)
                  ·
                    rfl

theorem cell22_1580703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].length) (baseStart_1580703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580703 prefixEnd_1580703 := by exact prefixLift 1580703
  have htrace : WordTrace (prefixWord ++ tailWord_1580703) baseStart_1580703 baseEnd_1580703 := by
    simpa [prefixWord, tailWord_1580703, baseEnd_1580703] using wordTrace_append hprefix tailTrace_1580703
  have hstable : (prefixWord ++ tailWord_1580703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580703).length < 2 ^ (prefixWord ++ tailWord_1580703).sum := by decide
  have hdescent : baseEnd_1580703 < baseStart_1580703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580729 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_1580729 : Nat := 118140960795 + 1580729 * 2 ^ 59
def prefixEnd_1580729 : Nat := 4983230072969 + 3 ^ 40 * 1580729 * 2
def baseEnd_1580729 : Nat := 541115841000700749478577

theorem tailTrace_1580729 : CollatzResearch.WordTrace tailWord_1580729 prefixEnd_1580729 541115841000700749478577 := by
  unfold tailWord_1580729
  simp only [CollatzResearch.WordTrace]
  refine ⟨57653923090296274865137241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38435948726864183243424827 57653923090296274865137241)
  ·
    refine ⟨43240442317722206148852931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57653923090296274865137241 43240442317722206148852931)
    ·
      refine ⟨64860663476583309223279397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43240442317722206148852931 64860663476583309223279397)
      ·
        refine ⟨12161374401859370479364887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64860663476583309223279397 12161374401859370479364887)
        ·
          refine ⟨18242061602789055719047331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161374401859370479364887 18242061602789055719047331)
          ·
            refine ⟨27363092404183583578570997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18242061602789055719047331 27363092404183583578570997)
            ·
              refine ⟨2565289912892210960491031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27363092404183583578570997 2565289912892210960491031)
              ·
                refine ⟨3847934869338316440736547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565289912892210960491031 3847934869338316440736547)
                ·
                  refine ⟨5771902304007474661104821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847934869338316440736547 5771902304007474661104821)
                  ·
                    refine ⟨541115841000700749478577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5771902304007474661104821 541115841000700749478577)
                    ·
                      rfl

theorem cell22_1580729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_1580729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580729 prefixEnd_1580729 := by exact prefixLift 1580729
  have htrace : WordTrace (prefixWord ++ tailWord_1580729) baseStart_1580729 baseEnd_1580729 := by
    simpa [prefixWord, tailWord_1580729, baseEnd_1580729] using wordTrace_append hprefix tailTrace_1580729
  have hstable : (prefixWord ++ tailWord_1580729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580729).length < 2 ^ (prefixWord ++ tailWord_1580729).sum := by decide
  have hdescent : baseEnd_1580729 < baseStart_1580729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580744 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1580744 : Nat := 118140960795 + 1580744 * 2 ^ 59
def prefixEnd_1580744 : Nat := 4983230072969 + 3 ^ 40 * 1580744 * 2
def baseEnd_1580744 : Nat := 541120975807245710353531

theorem tailTrace_1580744 : CollatzResearch.WordTrace tailWord_1580744 prefixEnd_1580744 541120975807245710353531 := by
  unfold tailWord_1580744
  simp only [CollatzResearch.WordTrace]
  refine ⟨28827235092620966213466643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38436313456827954951288857 28827235092620966213466643)
  ·
    refine ⟨43240852638931449320199965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28827235092620966213466643 43240852638931449320199965)
    ·
      refine ⟨16215319739599293495074987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43240852638931449320199965 16215319739599293495074987)
      ·
        refine ⟨24322979609398940242612481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16215319739599293495074987 24322979609398940242612481)
        ·
          refine ⟨18242234707049205181959361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24322979609398940242612481 18242234707049205181959361)
          ·
            refine ⟨13681676030286903886469521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18242234707049205181959361 13681676030286903886469521)
            ·
              refine ⟨10261257022715177914852141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13681676030286903886469521 10261257022715177914852141)
              ·
                refine ⟨3847971383518191718069553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10261257022715177914852141 3847971383518191718069553)
                ·
                  refine ⟨2885978537638643788552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847971383518191718069553 2885978537638643788552165)
                  ·
                    refine ⟨541120975807245710353531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2885978537638643788552165 541120975807245710353531)
                    ·
                      rfl

theorem cell22_1580744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1580744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580744 prefixEnd_1580744 := by exact prefixLift 1580744
  have htrace : WordTrace (prefixWord ++ tailWord_1580744) baseStart_1580744 baseEnd_1580744 := by
    simpa [prefixWord, tailWord_1580744, baseEnd_1580744] using wordTrace_append hprefix tailTrace_1580744
  have hstable : (prefixWord ++ tailWord_1580744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580744).length < 2 ^ (prefixWord ++ tailWord_1580744).sum := by decide
  have hdescent : baseEnd_1580744 < baseStart_1580744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580765 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 6]
def baseStart_1580765 : Nat := 118140960795 + 1580765 * 2 ^ 59
def prefixEnd_1580765 : Nat := 4983230072969 + 3 ^ 40 * 1580765 * 2
def baseEnd_1580765 : Nat := 180376054845469551859489

theorem tailTrace_1580765 : CollatzResearch.WordTrace tailWord_1580765 prefixEnd_1580765 180376054845469551859489 := by
  unfold tailWord_1580765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57655236118165853013447749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38436824078777235342298499 57655236118165853013447749)
  ·
    refine ⟨10810356772156097440021453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57655236118165853013447749 10810356772156097440021453)
    ·
      refine ⟨4053883789558536540008045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10810356772156097440021453 4053883789558536540008045)
      ·
        refine ⟨1520206421084451202503017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4053883789558536540008045 1520206421084451202503017)
        ·
          refine ⟨1140154815813338401877263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520206421084451202503017 1140154815813338401877263)
          ·
            refine ⟨1710232223720007602815895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140154815813338401877263 1710232223720007602815895)
            ·
              refine ⟨2565348335580011404223843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710232223720007602815895 2565348335580011404223843)
              ·
                refine ⟨3848022503370017106335765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565348335580011404223843 3848022503370017106335765)
                ·
                  refine ⟨180376054845469551859489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3848022503370017106335765 180376054845469551859489)
                  ·
                    rfl

theorem cell22_1580765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_1580765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580765 prefixEnd_1580765 := by exact prefixLift 1580765
  have htrace : WordTrace (prefixWord ++ tailWord_1580765) baseStart_1580765 baseEnd_1580765 := by
    simpa [prefixWord, tailWord_1580765, baseEnd_1580765] using wordTrace_append hprefix tailTrace_1580765
  have hstable : (prefixWord ++ tailWord_1580765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580765).length < 2 ^ (prefixWord ++ tailWord_1580765).sum := by decide
  have hdescent : baseEnd_1580765 < baseStart_1580765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580808 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_1580808 : Nat := 118140960795 + 1580808 * 2 ^ 59
def prefixEnd_1580808 : Nat := 4983230072969 + 3 ^ 40 * 1580808 * 2
def baseEnd_1580808 : Nat := 541142884315170876753335

theorem tailTrace_1580808 : CollatzResearch.WordTrace tailWord_1580808 prefixEnd_1580808 541142884315170876753335 := by
  unfold tailWord_1580808
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828402228505035678631539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38437869638006714238175385 28828402228505035678631539)
  ·
    refine ⟨43242603342757553517947309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28828402228505035678631539 43242603342757553517947309)
    ·
      refine ⟨16215976253534082569230241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43242603342757553517947309 16215976253534082569230241)
      ·
        refine ⟨12161982190150561926922681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16215976253534082569230241 12161982190150561926922681)
        ·
          refine ⟨9121486642612921445192011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12161982190150561926922681 9121486642612921445192011)
          ·
            refine ⟨13682229963919382167788017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121486642612921445192011 13682229963919382167788017)
            ·
              refine ⟨10261672472939536625841013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13682229963919382167788017 10261672472939536625841013)
              ·
                refine ⟨962031794338081558672595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10261672472939536625841013 962031794338081558672595)
                ·
                  refine ⟨1443047691507122338008893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962031794338081558672595 1443047691507122338008893)
                  ·
                    refine ⟨541142884315170876753335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443047691507122338008893 541142884315170876753335)
                    ·
                      rfl

theorem cell22_1580808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_1580808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580808 prefixEnd_1580808 := by exact prefixLift 1580808
  have htrace : WordTrace (prefixWord ++ tailWord_1580808) baseStart_1580808 baseEnd_1580808 := by
    simpa [prefixWord, tailWord_1580808, baseEnd_1580808] using wordTrace_append hprefix tailTrace_1580808
  have hstable : (prefixWord ++ tailWord_1580808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580808).length < 2 ^ (prefixWord ++ tailWord_1580808).sum := by decide
  have hdescent : baseEnd_1580808 < baseStart_1580808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580821 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 5]
def baseStart_1580821 : Nat := 118140960795 + 1580821 * 2 ^ 59
def prefixEnd_1580821 : Nat := 4983230072969 + 3 ^ 40 * 1580821 * 2
def baseEnd_1580821 : Nat := 180382444826947725392765

theorem tailTrace_1580821 : CollatzResearch.WordTrace tailWord_1580821 prefixEnd_1580821 180382444826947725392765 := by
  unfold tailWord_1580821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57657278605962974577486317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38438185737308649718324211 57657278605962974577486317)
  ·
    refine ⟨21621479477236115466557369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57657278605962974577486317 21621479477236115466557369)
    ·
      refine ⟨16216109607927086599918027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21621479477236115466557369 16216109607927086599918027)
      ·
        refine ⟨24324164411890629899877041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16216109607927086599918027 24324164411890629899877041)
        ·
          refine ⟨18243123308917972424907781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24324164411890629899877041 18243123308917972424907781)
          ·
            refine ⟨3420585620422119829670209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18243123308917972424907781 3420585620422119829670209)
            ·
              refine ⟨2565439215316589872252657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420585620422119829670209 2565439215316589872252657)
              ·
                refine ⟨1924079411487442404189493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565439215316589872252657 1924079411487442404189493)
                ·
                  refine ⟨180382444826947725392765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1924079411487442404189493 180382444826947725392765)
                  ·
                    rfl

theorem cell22_1580821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_1580821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580821 prefixEnd_1580821 := by exact prefixLift 1580821
  have htrace : WordTrace (prefixWord ++ tailWord_1580821) baseStart_1580821 baseEnd_1580821 := by
    simpa [prefixWord, tailWord_1580821, baseEnd_1580821] using wordTrace_append hprefix tailTrace_1580821
  have hstable : (prefixWord ++ tailWord_1580821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580821).length < 2 ^ (prefixWord ++ tailWord_1580821).sum := by decide
  have hdescent : baseEnd_1580821 < baseStart_1580821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580836 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1580836 : Nat := 118140960795 + 1580836 * 2 ^ 59
def prefixEnd_1580836 : Nat := 4983230072969 + 3 ^ 40 * 1580836 * 2
def baseEnd_1580836 : Nat := 541152469287388137053249

theorem tailTrace_1580836 : CollatzResearch.WordTrace tailWord_1580836 prefixEnd_1580836 541152469287388137053249 := by
  unfold tailWord_1580836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828912850454316069641181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38438550467272421426188241 28828912850454316069641181)
  ·
    refine ⟨10810842318920368526115443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28828912850454316069641181 10810842318920368526115443)
    ·
      refine ⟨16216263478380552789173165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810842318920368526115443 16216263478380552789173165)
      ·
        refine ⟨6081098804392707295939937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16216263478380552789173165 6081098804392707295939937)
        ·
          refine ⟨4560824103294530471954953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081098804392707295939937 4560824103294530471954953)
          ·
            refine ⟨3420618077470897853966215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560824103294530471954953 3420618077470897853966215)
            ·
              refine ⟨5130927116206346780949323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420618077470897853966215 5130927116206346780949323)
              ·
                refine ⟨7696390674309520171423985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130927116206346780949323 7696390674309520171423985)
                ·
                  refine ⟨5772293005732140128567989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696390674309520171423985 5772293005732140128567989)
                  ·
                    refine ⟨541152469287388137053249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5772293005732140128567989 541152469287388137053249)
                    ·
                      rfl

theorem cell22_1580836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1580836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580836 prefixEnd_1580836 := by exact prefixLift 1580836
  have htrace : WordTrace (prefixWord ++ tailWord_1580836) baseStart_1580836 baseEnd_1580836 := by
    simpa [prefixWord, tailWord_1580836, baseEnd_1580836] using wordTrace_append hprefix tailTrace_1580836
  have hstable : (prefixWord ++ tailWord_1580836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580836).length < 2 ^ (prefixWord ++ tailWord_1580836).sum := by decide
  have hdescent : baseEnd_1580836 < baseStart_1580836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580849 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 8]
def baseStart_1580849 : Nat := 118140960795 + 1580849 * 2 ^ 59
def prefixEnd_1580849 : Nat := 4983230072969 + 3 ^ 40 * 1580849 * 2
def baseEnd_1580849 : Nat := 180385639817686812159403

theorem tailTrace_1580849 : CollatzResearch.WordTrace tailWord_1580849 prefixEnd_1580849 180385639817686812159403 := by
  unfold tailWord_1580849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57658299849861535359505601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38438866566574356906337067 57658299849861535359505601)
  ·
    refine ⟨43243724887396151519629201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57658299849861535359505601 43243724887396151519629201)
    ·
      refine ⟨32432793665547113639721901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43243724887396151519629201 32432793665547113639721901)
      ·
        refine ⟨12162297624580167614895713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32432793665547113639721901 12162297624580167614895713)
        ·
          refine ⟨9121723218435125711171785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12162297624580167614895713 9121723218435125711171785)
          ·
            refine ⟨6841292413826344283378839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9121723218435125711171785 6841292413826344283378839)
            ·
              refine ⟨10261938620739516425068259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841292413826344283378839 10261938620739516425068259)
              ·
                refine ⟨15392907931109274637602389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261938620739516425068259 15392907931109274637602389)
                ·
                  refine ⟨180385639817686812159403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15392907931109274637602389 180385639817686812159403)
                  ·
                    rfl

theorem cell22_1580849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_1580849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580849 prefixEnd_1580849 := by exact prefixLift 1580849
  have htrace : WordTrace (prefixWord ++ tailWord_1580849) baseStart_1580849 baseEnd_1580849 := by
    simpa [prefixWord, tailWord_1580849, baseEnd_1580849] using wordTrace_append hprefix tailTrace_1580849
  have hstable : (prefixWord ++ tailWord_1580849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580849).length < 2 ^ (prefixWord ++ tailWord_1580849).sum := by decide
  have hdescent : baseEnd_1580849 < baseStart_1580849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580898 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1580898 : Nat := 118140960795 + 1580898 * 2 ^ 59
def prefixEnd_1580898 : Nat := 4983230072969 + 3 ^ 40 * 1580898 * 2
def baseEnd_1580898 : Nat := 541173693154440642003059

theorem tailTrace_1580898 : CollatzResearch.WordTrace tailWord_1580898 prefixEnd_1580898 541173693154440642003059 := by
  unfold tailWord_1580898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415021756671004182009837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38440058017789344485359565 14415021756671004182009837)
  ·
    refine ⟨5405633158751626568253689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14415021756671004182009837 5405633158751626568253689)
    ·
      refine ⟨4054224869063719926190267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5405633158751626568253689 4054224869063719926190267)
      ·
        refine ⟨6081337303595579889285401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054224869063719926190267 6081337303595579889285401)
        ·
          refine ⟨4561002977696684916964051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081337303595579889285401 4561002977696684916964051)
          ·
            refine ⟨6841504466545027375446077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561002977696684916964051 6841504466545027375446077)
            ·
              refine ⟨2565564174954385265792279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841504466545027375446077 2565564174954385265792279)
              ·
                refine ⟨3848346262431577898688419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565564174954385265792279 3848346262431577898688419)
                ·
                  refine ⟨5772519393647366848032629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848346262431577898688419 5772519393647366848032629)
                  ·
                    refine ⟨541173693154440642003059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5772519393647366848032629 541173693154440642003059)
                    ·
                      rfl

theorem cell22_1580898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1580898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580898 prefixEnd_1580898 := by exact prefixLift 1580898
  have htrace : WordTrace (prefixWord ++ tailWord_1580898) baseStart_1580898 baseEnd_1580898 := by
    simpa [prefixWord, tailWord_1580898, baseEnd_1580898] using wordTrace_append hprefix tailTrace_1580898
  have hstable : (prefixWord ++ tailWord_1580898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580898).length < 2 ^ (prefixWord ++ tailWord_1580898).sum := by decide
  have hdescent : baseEnd_1580898 < baseStart_1580898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580924 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1580924 : Nat := 118140960795 + 1580924 * 2 ^ 59
def prefixEnd_1580924 : Nat := 4983230072969 + 3 ^ 40 * 1580924 * 2
def baseEnd_1580924 : Nat := 541182593485785240852979

theorem tailTrace_1580924 : CollatzResearch.WordTrace tailWord_1580924 prefixEnd_1580924 541182593485785240852979 := by
  unfold tailWord_1580924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28830517662294911584242913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38440690216393215445657217 28830517662294911584242913)
  ·
    refine ⟨21622888246721183688182185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28830517662294911584242913 21622888246721183688182185)
    ·
      refine ⟨16217166185040887766136639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21622888246721183688182185 16217166185040887766136639)
      ·
        refine ⟨24325749277561331649204959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217166185040887766136639 24325749277561331649204959)
        ·
          refine ⟨36488623916341997473807439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24325749277561331649204959 36488623916341997473807439)
          ·
            refine ⟨54732935874512996210711159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36488623916341997473807439 54732935874512996210711159)
            ·
              refine ⟨82099403811769494316066739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54732935874512996210711159 82099403811769494316066739)
              ·
                refine ⟨123149105717654241474100109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82099403811769494316066739 123149105717654241474100109)
                ·
                  refine ⟨46180914644120340552787541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123149105717654241474100109 46180914644120340552787541)
                  ·
                    refine ⟨541182593485785240852979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46180914644120340552787541 541182593485785240852979)
                    ·
                      rfl

theorem cell22_1580924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1580924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1580924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1580924 prefixEnd_1580924 := by exact prefixLift 1580924
  have htrace : WordTrace (prefixWord ++ tailWord_1580924) baseStart_1580924 baseEnd_1580924 := by
    simpa [prefixWord, tailWord_1580924, baseEnd_1580924] using wordTrace_append hprefix tailTrace_1580924
  have hstable : (prefixWord ++ tailWord_1580924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580924).length < 2 ^ (prefixWord ++ tailWord_1580924).sum := by decide
  have hdescent : baseEnd_1580924 < baseStart_1580924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581018 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_1581018 : Nat := 118140960795 + 1581018 * 2 ^ 59
def prefixEnd_1581018 : Nat := 4983230072969 + 3 ^ 40 * 1581018 * 2
def baseEnd_1581018 : Nat := 180404923868933443000897

theorem tailTrace_1581018 : CollatzResearch.WordTrace tailWord_1581018 prefixEnd_1581018 180404923868933443000897 := by
  unfold tailWord_1581018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416115946562319305601927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38442975857499518148271805 14416115946562319305601927)
  ·
    refine ⟨21624173919843478958402891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14416115946562319305601927 21624173919843478958402891)
    ·
      refine ⟨32436260879765218437604337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21624173919843478958402891 32436260879765218437604337)
      ·
        refine ⟨24327195659823913828203253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32436260879765218437604337 24327195659823913828203253)
        ·
          refine ⟨2280674593108491921394055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24327195659823913828203253 2280674593108491921394055)
          ·
            refine ⟨3421011889662737882091083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280674593108491921394055 3421011889662737882091083)
            ·
              refine ⟨5131517834494106823136625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421011889662737882091083 5131517834494106823136625)
              ·
                refine ⟨3848638375870580117352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5131517834494106823136625 3848638375870580117352469)
                ·
                  refine ⟨180404923868933443000897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3848638375870580117352469 180404923868933443000897)
                  ·
                    rfl

theorem cell22_1581018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_1581018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581018 prefixEnd_1581018 := by exact prefixLift 1581018
  have htrace : WordTrace (prefixWord ++ tailWord_1581018) baseStart_1581018 baseEnd_1581018 := by
    simpa [prefixWord, tailWord_1581018, baseEnd_1581018] using wordTrace_append hprefix tailTrace_1581018
  have hstable : (prefixWord ++ tailWord_1581018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581018).length < 2 ^ (prefixWord ++ tailWord_1581018).sum := by decide
  have hdescent : baseEnd_1581018 < baseStart_1581018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581037 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1581037 : Nat := 118140960795 + 1581037 * 2 ^ 59
def prefixEnd_1581037 : Nat := 4983230072969 + 3 ^ 40 * 1581037 * 2
def baseEnd_1581037 : Nat := 541221275695090612777633

theorem tailTrace_1581037 : CollatzResearch.WordTrace tailWord_1581037 prefixEnd_1581037 541221275695090612777633 := by
  unfold tailWord_1581037
  simp only [CollatzResearch.WordTrace]
  refine ⟨57665156773180443467349365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38443437848786962311566243 57665156773180443467349365)
  ·
    refine ⟨5406108447485666575064003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57665156773180443467349365 5406108447485666575064003)
    ·
      refine ⟨8109162671228499862596005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406108447485666575064003 8109162671228499862596005)
      ·
        refine ⟨1520468000855343724236751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8109162671228499862596005 1520468000855343724236751)
        ·
          refine ⟨2280702001283015586355127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520468000855343724236751 2280702001283015586355127)
          ·
            refine ⟨3421053001924523379532691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280702001283015586355127 3421053001924523379532691)
            ·
              refine ⟨5131579502886785069299037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421053001924523379532691 5131579502886785069299037)
              ·
                refine ⟨1924342313582544400987139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5131579502886785069299037 1924342313582544400987139)
                ·
                  refine ⟨2886513470373816601480709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924342313582544400987139 2886513470373816601480709)
                  ·
                    refine ⟨541221275695090612777633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886513470373816601480709 541221275695090612777633)
                    ·
                      rfl

theorem cell22_1581037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1581037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581037 prefixEnd_1581037 := by exact prefixLift 1581037
  have htrace : WordTrace (prefixWord ++ tailWord_1581037) baseStart_1581037 baseEnd_1581037 := by
    simpa [prefixWord, tailWord_1581037, baseEnd_1581037] using wordTrace_append hprefix tailTrace_1581037
  have hstable : (prefixWord ++ tailWord_1581037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581037).length < 2 ^ (prefixWord ++ tailWord_1581037).sum := by decide
  have hdescent : baseEnd_1581037 < baseStart_1581037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581091 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 9]
def baseStart_1581091 : Nat := 118140960795 + 1581091 * 2 ^ 59
def prefixEnd_1581091 : Nat := 4983230072969 + 3 ^ 40 * 1581091 * 2
def baseEnd_1581091 : Nat := 180413253666217490642489

theorem tailTrace_1581091 : CollatzResearch.WordTrace tailWord_1581091 prefixEnd_1581091 180413253666217490642489 := by
  unfold tailWord_1581091
  simp only [CollatzResearch.WordTrace]
  refine ⟨57667126314984810689815127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38444750876656540459876751 57667126314984810689815127)
  ·
    refine ⟨86500689472477216034722691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57667126314984810689815127 86500689472477216034722691)
    ·
      refine ⟨129751034208715824052084037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86500689472477216034722691 129751034208715824052084037)
      ·
        refine ⟨24328318914134217009765757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129751034208715824052084037 24328318914134217009765757)
        ·
          refine ⟨9123119592800331378662159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24328318914134217009765757 9123119592800331378662159)
          ·
            refine ⟨13684679389200497067993239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123119592800331378662159 13684679389200497067993239)
            ·
              refine ⟨20527019083800745601989859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13684679389200497067993239 20527019083800745601989859)
              ·
                refine ⟨30790528625701118402984789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20527019083800745601989859 30790528625701118402984789)
                ·
                  refine ⟨180413253666217490642489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30790528625701118402984789 180413253666217490642489)
                  ·
                    rfl

theorem cell22_1581091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 9].length) (baseStart_1581091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581091 prefixEnd_1581091 := by exact prefixLift 1581091
  have htrace : WordTrace (prefixWord ++ tailWord_1581091) baseStart_1581091 baseEnd_1581091 := by
    simpa [prefixWord, tailWord_1581091, baseEnd_1581091] using wordTrace_append hprefix tailTrace_1581091
  have hstable : (prefixWord ++ tailWord_1581091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581091).length < 2 ^ (prefixWord ++ tailWord_1581091).sum := by decide
  have hdescent : baseEnd_1581091 < baseStart_1581091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581112 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1581112 : Nat := 118140960795 + 1581112 * 2 ^ 59
def prefixEnd_1581112 : Nat := 4983230072969 + 3 ^ 40 * 1581112 * 2
def baseEnd_1581112 : Nat := 541246949727815417152403

theorem tailTrace_1581112 : CollatzResearch.WordTrace tailWord_1581112 prefixEnd_1581112 541246949727815417152403 := by
  unfold tailWord_1581112
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833946123954365638164795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38445261498605820850886393 28833946123954365638164795)
  ·
    refine ⟨43250919185931548457247193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833946123954365638164795 43250919185931548457247193)
    ·
      refine ⟨32438189389448661342935395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43250919185931548457247193 32438189389448661342935395)
      ·
        refine ⟨48657284084172992014403093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32438189389448661342935395 48657284084172992014403093)
        ·
          refine ⟨2280810191445609000675145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48657284084172992014403093 2280810191445609000675145)
          ·
            refine ⟨1710607643584206750506359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280810191445609000675145 1710607643584206750506359)
            ·
              refine ⟨2565911465376310125759539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710607643584206750506359 2565911465376310125759539)
              ·
                refine ⟨3848867198064465188639309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565911465376310125759539 3848867198064465188639309)
                ·
                  refine ⟨1443325199274174445739741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3848867198064465188639309 1443325199274174445739741)
                  ·
                    refine ⟨541246949727815417152403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443325199274174445739741 541246949727815417152403)
                    ·
                      rfl

theorem cell22_1581112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1581112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581112 prefixEnd_1581112 := by exact prefixLift 1581112
  have htrace : WordTrace (prefixWord ++ tailWord_1581112) baseStart_1581112 baseEnd_1581112 := by
    simpa [prefixWord, tailWord_1581112, baseEnd_1581112] using wordTrace_append hprefix tailTrace_1581112
  have hstable : (prefixWord ++ tailWord_1581112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581112).length < 2 ^ (prefixWord ++ tailWord_1581112).sum := by decide
  have hdescent : baseEnd_1581112 < baseStart_1581112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581249 : List Nat := [1, 2, 6, 1, 2, 2, 2, 6]
def baseStart_1581249 : Nat := 118140960795 + 1581249 * 2 ^ 59
def prefixEnd_1581249 : Nat := 4983230072969 + 3 ^ 40 * 1581249 * 2
def baseEnd_1581249 : Nat := 60143760847510302941887

theorem tailTrace_1581249 : CollatzResearch.WordTrace tailWord_1581249 prefixEnd_1581249 60143760847510302941887 := by
  unfold tailWord_1581249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57672889048412403674066801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38448592698941602449377867 57672889048412403674066801)
  ·
    refine ⟨43254666786309302755550101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57672889048412403674066801 43254666786309302755550101)
    ·
      refine ⟨2027562505608248566666411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43254666786309302755550101 2027562505608248566666411)
      ·
        refine ⟨3041343758412372849999617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027562505608248566666411 3041343758412372849999617)
        ·
          refine ⟨2281007818809279637499713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041343758412372849999617 2281007818809279637499713)
          ·
            refine ⟨1710755864106959728124785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281007818809279637499713 1710755864106959728124785)
            ·
              refine ⟨1283066898080219796093589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710755864106959728124785 1283066898080219796093589)
              ·
                refine ⟨60143760847510302941887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1283066898080219796093589 60143760847510302941887)
                ·
                  rfl

theorem cell22_1581249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 6].length) (baseStart_1581249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581249 prefixEnd_1581249 := by exact prefixLift 1581249
  have htrace : WordTrace (prefixWord ++ tailWord_1581249) baseStart_1581249 baseEnd_1581249 := by
    simpa [prefixWord, tailWord_1581249, baseEnd_1581249] using wordTrace_append hprefix tailTrace_1581249
  have hstable : (prefixWord ++ tailWord_1581249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581249).length < 2 ^ (prefixWord ++ tailWord_1581249).sum := by decide
  have hdescent : baseEnd_1581249 < baseStart_1581249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581290 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1581290 : Nat := 118140960795 + 1581290 * 2 ^ 59
def prefixEnd_1581290 : Nat := 4983230072969 + 3 ^ 40 * 1581290 * 2
def baseEnd_1581290 : Nat := 541307882765482286201857

theorem tailTrace_1581290 : CollatzResearch.WordTrace tailWord_1581290 prefixEnd_1581290 541307882765482286201857 := by
  unfold tailWord_1581290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14418596110315966919077331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38449589627509245117539549 14418596110315966919077331)
  ·
    refine ⟨21627894165473950378615997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14418596110315966919077331 21627894165473950378615997)
    ·
      refine ⟨8110460312052731391980999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21627894165473950378615997 8110460312052731391980999)
      ·
        refine ⟨12165690468079097087971499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8110460312052731391980999 12165690468079097087971499)
        ·
          refine ⟨18248535702118645631957249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12165690468079097087971499 18248535702118645631957249)
          ·
            refine ⟨13686401776588984223967937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18248535702118645631957249 13686401776588984223967937)
            ·
              refine ⟨10264801332441738167975953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13686401776588984223967937 10264801332441738167975953)
              ·
                refine ⟨7698600999331303625981965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10264801332441738167975953 7698600999331303625981965)
                ·
                  refine ⟨2886975374749238859743237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7698600999331303625981965 2886975374749238859743237)
                  ·
                    refine ⟨541307882765482286201857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886975374749238859743237 541307882765482286201857)
                    ·
                      rfl

theorem cell22_1581290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1581290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581290 prefixEnd_1581290 := by exact prefixLift 1581290
  have htrace : WordTrace (prefixWord ++ tailWord_1581290) baseStart_1581290 baseEnd_1581290 := by
    simpa [prefixWord, tailWord_1581290, baseEnd_1581290] using wordTrace_append hprefix tailTrace_1581290
  have hstable : (prefixWord ++ tailWord_1581290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581290).length < 2 ^ (prefixWord ++ tailWord_1581290).sum := by decide
  have hdescent : baseEnd_1581290 < baseStart_1581290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581320 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1581320 : Nat := 118140960795 + 1581320 * 2 ^ 59
def prefixEnd_1581320 : Nat := 4983230072969 + 3 ^ 40 * 1581320 * 2
def baseEnd_1581320 : Nat := 541318152378572207951765

theorem tailTrace_1581320 : CollatzResearch.WordTrace tailWord_1581320 prefixEnd_1581320 541318152378572207951765 := by
  unfold tailWord_1581320
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837739315577591399950707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38450319087436788533267609 28837739315577591399950707)
  ·
    refine ⟨43256608973366387099926061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28837739315577591399950707 43256608973366387099926061)
    ·
      refine ⟨16221228365012395162472273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43256608973366387099926061 16221228365012395162472273)
      ·
        refine ⟨12165921273759296371854205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16221228365012395162472273 12165921273759296371854205)
        ·
          refine ⟨4562220477659736139445327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12165921273759296371854205 4562220477659736139445327)
          ·
            refine ⟨6843330716489604209167991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562220477659736139445327 6843330716489604209167991)
            ·
              refine ⟨10264996074734406313751987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843330716489604209167991 10264996074734406313751987)
              ·
                refine ⟨15397494112101609470627981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10264996074734406313751987 15397494112101609470627981)
                ·
                  refine ⟨5774060292038103551485493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15397494112101609470627981 5774060292038103551485493)
                  ·
                    refine ⟨541318152378572207951765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5774060292038103551485493 541318152378572207951765)
                    ·
                      rfl

theorem cell22_1581320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1581320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581320 prefixEnd_1581320 := by exact prefixLift 1581320
  have htrace : WordTrace (prefixWord ++ tailWord_1581320) baseStart_1581320 baseEnd_1581320 := by
    simpa [prefixWord, tailWord_1581320, baseEnd_1581320] using wordTrace_append hprefix tailTrace_1581320
  have hstable : (prefixWord ++ tailWord_1581320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581320).length < 2 ^ (prefixWord ++ tailWord_1581320).sum := by decide
  have hdescent : baseEnd_1581320 < baseStart_1581320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581354 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1581354 : Nat := 118140960795 + 1581354 * 2 ^ 59
def prefixEnd_1581354 : Nat := 4983230072969 + 3 ^ 40 * 1581354 * 2
def baseEnd_1581354 : Nat := 541329791273407452601661

theorem tailTrace_1581354 : CollatzResearch.WordTrace tailWord_1581354 prefixEnd_1581354 541329791273407452601661 := by
  unfold tailWord_1581354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419179678258001651659779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38451145808688004404426077 14419179678258001651659779)
  ·
    refine ⟨21628769517387002477489669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14419179678258001651659779 21628769517387002477489669)
    ·
      refine ⟨4055394284510062964529313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21628769517387002477489669 4055394284510062964529313)
      ·
        refine ⟨3041545713382547223396985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4055394284510062964529313 3041545713382547223396985)
        ·
          refine ⟨2281159285036910417547739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041545713382547223396985 2281159285036910417547739)
          ·
            refine ⟨3421738927555365626321609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281159285036910417547739 3421738927555365626321609)
            ·
              refine ⟨2566304195666524219741207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421738927555365626321609 2566304195666524219741207)
              ·
                refine ⟨3849456293499786329611811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566304195666524219741207 3849456293499786329611811)
                ·
                  refine ⟨5774184440249679494417717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849456293499786329611811 5774184440249679494417717)
                  ·
                    refine ⟨541329791273407452601661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5774184440249679494417717 541329791273407452601661)
                    ·
                      rfl

theorem cell22_1581354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1581354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581354 prefixEnd_1581354 := by exact prefixLift 1581354
  have htrace : WordTrace (prefixWord ++ tailWord_1581354) baseStart_1581354 baseEnd_1581354 := by
    simpa [prefixWord, tailWord_1581354, baseEnd_1581354] using wordTrace_append hprefix tailTrace_1581354
  have hstable : (prefixWord ++ tailWord_1581354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581354).length < 2 ^ (prefixWord ++ tailWord_1581354).sum := by decide
  have hdescent : baseEnd_1581354 < baseStart_1581354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581369 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_1581369 : Nat := 118140960795 + 1581369 * 2 ^ 59
def prefixEnd_1581369 : Nat := 4983230072969 + 3 ^ 40 * 1581369 * 2
def baseEnd_1581369 : Nat := 541334926079952413476615

theorem tailTrace_1581369 : CollatzResearch.WordTrace tailWord_1581369 prefixEnd_1581369 541334926079952413476615 := by
  unfold tailWord_1581369
  simp only [CollatzResearch.WordTrace]
  refine ⟨57677265807977664168435161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38451510538651776112290107 57677265807977664168435161)
  ·
    refine ⟨43257949355983248126326371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57677265807977664168435161 43257949355983248126326371)
    ·
      refine ⟨64886924033974872189489557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43257949355983248126326371 64886924033974872189489557)
      ·
        refine ⟨3041574564092572133882323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64886924033974872189489557 3041574564092572133882323)
        ·
          refine ⟨4562361846138858200823485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041574564092572133882323 4562361846138858200823485)
          ·
            refine ⟨1710885692302071825308807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4562361846138858200823485 1710885692302071825308807)
            ·
              refine ⟨2566328538453107737963211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710885692302071825308807 2566328538453107737963211)
              ·
                refine ⟨3849492807679661606944817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566328538453107737963211 3849492807679661606944817)
                ·
                  refine ⟨2887119605759746205208613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849492807679661606944817 2887119605759746205208613)
                  ·
                    refine ⟨541334926079952413476615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887119605759746205208613 541334926079952413476615)
                    ·
                      rfl

theorem cell22_1581369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_1581369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581369 prefixEnd_1581369 := by exact prefixLift 1581369
  have htrace : WordTrace (prefixWord ++ tailWord_1581369) baseStart_1581369 baseEnd_1581369 := by
    simpa [prefixWord, tailWord_1581369, baseEnd_1581369] using wordTrace_append hprefix tailTrace_1581369
  have hstable : (prefixWord ++ tailWord_1581369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581369).length < 2 ^ (prefixWord ++ tailWord_1581369).sum := by decide
  have hdescent : baseEnd_1581369 < baseStart_1581369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581395 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 5]
def baseStart_1581395 : Nat := 118140960795 + 1581395 * 2 ^ 59
def prefixEnd_1581395 : Nat := 4983230072969 + 3 ^ 40 * 1581395 * 2
def baseEnd_1581395 : Nat := 180447942137099004108845

theorem tailTrace_1581395 : CollatzResearch.WordTrace tailWord_1581395 prefixEnd_1581395 180447942137099004108845 := by
  unfold tailWord_1581395
  simp only [CollatzResearch.WordTrace]
  refine ⟨57678214105883470608881639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38452142737255647072587759 57678214105883470608881639)
  ·
    refine ⟨86517321158825205913322459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57678214105883470608881639 86517321158825205913322459)
    ·
      refine ⟨129775981738237808869983689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86517321158825205913322459 129775981738237808869983689)
      ·
        refine ⟨97331986303678356652487767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129775981738237808869983689 97331986303678356652487767)
        ·
          refine ⟨145997979455517534978731651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97331986303678356652487767 145997979455517534978731651)
          ·
            refine ⟨218996969183276302468097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145997979455517534978731651 218996969183276302468097477)
            ·
              refine ⟨41061931721864306712768277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218996969183276302468097477 41061931721864306712768277)
              ·
                refine ⟨1924778049462389377161013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41061931721864306712768277 1924778049462389377161013)
                ·
                  refine ⟨180447942137099004108845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1924778049462389377161013 180447942137099004108845)
                  ·
                    rfl

theorem cell22_1581395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].length) (baseStart_1581395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581395 prefixEnd_1581395 := by exact prefixLift 1581395
  have htrace : WordTrace (prefixWord ++ tailWord_1581395) baseStart_1581395 baseEnd_1581395 := by
    simpa [prefixWord, tailWord_1581395, baseEnd_1581395] using wordTrace_append hprefix tailTrace_1581395
  have hstable : (prefixWord ++ tailWord_1581395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581395).length < 2 ^ (prefixWord ++ tailWord_1581395).sum := by decide
  have hdescent : baseEnd_1581395 < baseStart_1581395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581399 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 1, 3]
def baseStart_1581399 : Nat := 118140960795 + 1581399 * 2 ^ 59
def prefixEnd_1581399 : Nat := 4983230072969 + 3 ^ 40 * 1581399 * 2
def baseEnd_1581399 : Nat := 541345195693042335226523

theorem tailTrace_1581399 : CollatzResearch.WordTrace tailWord_1581399 prefixEnd_1581399 541345195693042335226523 := by
  unfold tailWord_1581399
  simp only [CollatzResearch.WordTrace]
  refine ⟨57678359997868979292027251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38452239998579319528018167 57678359997868979292027251)
  ·
    refine ⟨86517539996803468938040877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57678359997868979292027251 86517539996803468938040877)
    ·
      refine ⟨32444077498801300851765329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86517539996803468938040877 32444077498801300851765329)
      ·
        refine ⟨24333058124100975638823997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32444077498801300851765329 24333058124100975638823997)
        ·
          refine ⟨9124896796537865864558999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24333058124100975638823997 9124896796537865864558999)
          ·
            refine ⟨13687345194806798796838499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124896796537865864558999 13687345194806798796838499)
            ·
              refine ⟨20531017792210198195257749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13687345194806798796838499 20531017792210198195257749)
              ·
                refine ⟨962391459009853040402707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20531017792210198195257749 962391459009853040402707)
                ·
                  refine ⟨1443587188514779560604061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962391459009853040402707 1443587188514779560604061)
                  ·
                    refine ⟨541345195693042335226523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443587188514779560604061 541345195693042335226523)
                    ·
                      rfl

theorem cell22_1581399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_1581399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581399 prefixEnd_1581399 := by exact prefixLift 1581399
  have htrace : WordTrace (prefixWord ++ tailWord_1581399) baseStart_1581399 baseEnd_1581399 := by
    simpa [prefixWord, tailWord_1581399, baseEnd_1581399] using wordTrace_append hprefix tailTrace_1581399
  have hstable : (prefixWord ++ tailWord_1581399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581399).length < 2 ^ (prefixWord ++ tailWord_1581399).sum := by decide
  have hdescent : baseEnd_1581399 < baseStart_1581399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581450 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1581450 : Nat := 118140960795 + 1581450 * 2 ^ 59
def prefixEnd_1581450 : Nat := 4983230072969 + 3 ^ 40 * 1581450 * 2
def baseEnd_1581450 : Nat := 541362654035295202201367

theorem tailTrace_1581450 : CollatzResearch.WordTrace tailWord_1581450 prefixEnd_1581450 541362654035295202201367 := by
  unfold tailWord_1581450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420055030171053750533451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38453480080456143334755869 14420055030171053750533451)
  ·
    refine ⟨21630082545256580625800177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420055030171053750533451 21630082545256580625800177)
    ·
      refine ⟨16222561908942435469350133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21630082545256580625800177 16222561908942435469350133)
      ·
        refine ⟨1520865178963353325251575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16222561908942435469350133 1520865178963353325251575)
        ·
          refine ⟨2281297768445029987877363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520865178963353325251575 2281297768445029987877363)
          ·
            refine ⟨3421946652667544981816045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281297768445029987877363 3421946652667544981816045)
            ·
              refine ⟨1283229994750329368181017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3421946652667544981816045 1283229994750329368181017)
              ·
                refine ⟨962422496062747026135763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283229994750329368181017 962422496062747026135763)
                ·
                  refine ⟨1443633744094120539203645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962422496062747026135763 1443633744094120539203645)
                  ·
                    refine ⟨541362654035295202201367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443633744094120539203645 541362654035295202201367)
                    ·
                      rfl

theorem cell22_1581450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1581450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581450 prefixEnd_1581450 := by exact prefixLift 1581450
  have htrace : WordTrace (prefixWord ++ tailWord_1581450) baseStart_1581450 baseEnd_1581450 := by
    simpa [prefixWord, tailWord_1581450, baseEnd_1581450] using wordTrace_append hprefix tailTrace_1581450
  have hstable : (prefixWord ++ tailWord_1581450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581450).length < 2 ^ (prefixWord ++ tailWord_1581450).sum := by decide
  have hdescent : baseEnd_1581450 < baseStart_1581450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581577 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_1581577 : Nat := 118140960795 + 1581577 * 2 ^ 59
def prefixEnd_1581577 : Nat := 4983230072969 + 3 ^ 40 * 1581577 * 2
def baseEnd_1581577 : Nat := 541406128730709204275977

theorem tailTrace_1581577 : CollatzResearch.WordTrace tailWord_1581577 prefixEnd_1581577 541406128730709204275977 := by
  unfold tailWord_1581577
  simp only [CollatzResearch.WordTrace]
  refine ⟨57684852191224115692006985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456568127482743794671323 57684852191224115692006985)
  ·
    refine ⟨43263639143418086769005239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57684852191224115692006985 43263639143418086769005239)
    ·
      refine ⟨64895458715127130153507859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43263639143418086769005239 64895458715127130153507859)
      ·
        refine ⟨97343188072690695230261789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64895458715127130153507859 97343188072690695230261789)
        ·
          refine ⟨36503695527259010711348171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97343188072690695230261789 36503695527259010711348171)
          ·
            refine ⟨54755543290888516067022257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36503695527259010711348171 54755543290888516067022257)
            ·
              refine ⟨41066657468166387050266693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54755543290888516067022257 41066657468166387050266693)
              ·
                refine ⟨7699998275281197571925005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41066657468166387050266693 7699998275281197571925005)
                ·
                  refine ⟨2887499353230449089471877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7699998275281197571925005 2887499353230449089471877)
                  ·
                    refine ⟨541406128730709204275977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887499353230449089471877 541406128730709204275977)
                    ·
                      rfl

theorem cell22_1581577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_1581577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581577 prefixEnd_1581577 := by exact prefixLift 1581577
  have htrace : WordTrace (prefixWord ++ tailWord_1581577) baseStart_1581577 baseEnd_1581577 := by
    simpa [prefixWord, tailWord_1581577, baseEnd_1581577] using wordTrace_append hprefix tailTrace_1581577
  have hstable : (prefixWord ++ tailWord_1581577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581577).length < 2 ^ (prefixWord ++ tailWord_1581577).sum := by decide
  have hdescent : baseEnd_1581577 < baseStart_1581577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581594 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1581594 : Nat := 118140960795 + 1581594 * 2 ^ 59
def prefixEnd_1581594 : Nat := 4983230072969 + 3 ^ 40 * 1581594 * 2
def baseEnd_1581594 : Nat := 541411948178126826600925

theorem tailTrace_1581594 : CollatzResearch.WordTrace tailWord_1581594 prefixEnd_1581594 541411948178126826600925 := by
  unfold tailWord_1581594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421368058040631898843959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38456981488108351730250557 14421368058040631898843959)
  ·
    refine ⟨21632052087060947848265939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14421368058040631898843959 21632052087060947848265939)
    ·
      refine ⟨32448078130591421772398909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21632052087060947848265939 32448078130591421772398909)
      ·
        refine ⟨12168029298971783164649591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32448078130591421772398909 12168029298971783164649591)
        ·
          refine ⟨18252043948457674746974387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168029298971783164649591 18252043948457674746974387)
          ·
            refine ⟨27378065922686512120461581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18252043948457674746974387 27378065922686512120461581)
            ·
              refine ⟨10266774721007442045173093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27378065922686512120461581 10266774721007442045173093)
              ·
                refine ⟨1925020260188895383469955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10266774721007442045173093 1925020260188895383469955)
                ·
                  refine ⟨2887530390283343075204933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925020260188895383469955 2887530390283343075204933)
                  ·
                    refine ⟨541411948178126826600925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887530390283343075204933 541411948178126826600925)
                    ·
                      rfl

theorem cell22_1581594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1581594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581594 prefixEnd_1581594 := by exact prefixLift 1581594
  have htrace : WordTrace (prefixWord ++ tailWord_1581594) baseStart_1581594 baseEnd_1581594 := by
    simpa [prefixWord, tailWord_1581594, baseEnd_1581594] using wordTrace_append hprefix tailTrace_1581594
  have hstable : (prefixWord ++ tailWord_1581594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581594).length < 2 ^ (prefixWord ++ tailWord_1581594).sum := by decide
  have hdescent : baseEnd_1581594 < baseStart_1581594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581624 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1581624 : Nat := 118140960795 + 1581624 * 2 ^ 59
def prefixEnd_1581624 : Nat := 4983230072969 + 3 ^ 40 * 1581624 * 2
def baseEnd_1581624 : Nat := 541422217791216748350833

theorem tailTrace_1581624 : CollatzResearch.WordTrace tailWord_1581624 prefixEnd_1581624 541422217791216748350833 := by
  unfold tailWord_1581624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843283211026921359483963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38457710948035895145978617 28843283211026921359483963)
  ·
    refine ⟨43264924816540382039225945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843283211026921359483963 43264924816540382039225945)
    ·
      refine ⟨32448693612405286529419459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43264924816540382039225945 32448693612405286529419459)
      ·
        refine ⟨48673040418607929794129189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32448693612405286529419459 48673040418607929794129189)
        ·
          refine ⟨9126195078488986836399223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48673040418607929794129189 9126195078488986836399223)
          ·
            refine ⟨13689292617733480254598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126195078488986836399223 13689292617733480254598835)
            ·
              refine ⟨20533938926600220381898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689292617733480254598835 20533938926600220381898253)
              ·
                refine ⟨7700227097475082643211845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20533938926600220381898253 7700227097475082643211845)
                ·
                  refine ⟨1443792580776577995602221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7700227097475082643211845 1443792580776577995602221)
                  ·
                    refine ⟨541422217791216748350833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443792580776577995602221 541422217791216748350833)
                    ·
                      rfl

theorem cell22_1581624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1581624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581624 prefixEnd_1581624 := by exact prefixLift 1581624
  have htrace : WordTrace (prefixWord ++ tailWord_1581624) baseStart_1581624 baseEnd_1581624 := by
    simpa [prefixWord, tailWord_1581624, baseEnd_1581624] using wordTrace_append hprefix tailTrace_1581624
  have hstable : (prefixWord ++ tailWord_1581624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581624).length < 2 ^ (prefixWord ++ tailWord_1581624).sum := by decide
  have hdescent : baseEnd_1581624 < baseStart_1581624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581637 : List Nat := [1, 3, 1, 1, 1, 5, 1, 9]
def baseStart_1581637 : Nat := 118140960795 + 1581637 * 2 ^ 59
def prefixEnd_1581637 : Nat := 4983230072969 + 3 ^ 40 * 1581637 * 2
def baseEnd_1581637 : Nat := 60158518661876560863977

theorem tailTrace_1581637 : CollatzResearch.WordTrace tailWord_1581637 prefixEnd_1581637 60158518661876560863977 := by
  unfold tailWord_1581637
  simp only [CollatzResearch.WordTrace]
  refine ⟨57687040571006745939191165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38458027047337830626127443 57687040571006745939191165)
  ·
    refine ⟨21632640214127529727196687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57687040571006745939191165 21632640214127529727196687)
    ·
      refine ⟨32448960321191294590795031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21632640214127529727196687 32448960321191294590795031)
      ·
        refine ⟨48673440481786941886192547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32448960321191294590795031 48673440481786941886192547)
        ·
          refine ⟨73010160722680412829288821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48673440481786941886192547 73010160722680412829288821)
          ·
            refine ⟨6844702567751288702745827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73010160722680412829288821 6844702567751288702745827)
            ·
              refine ⟨10267053851626933054118741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844702567751288702745827 10267053851626933054118741)
              ·
                refine ⟨60158518661876560863977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10267053851626933054118741 60158518661876560863977)
                ·
                  rfl

theorem cell22_1581637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 9].length) (baseStart_1581637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581637 prefixEnd_1581637 := by exact prefixLift 1581637
  have htrace : WordTrace (prefixWord ++ tailWord_1581637) baseStart_1581637 baseEnd_1581637 := by
    simpa [prefixWord, tailWord_1581637, baseEnd_1581637] using wordTrace_append hprefix tailTrace_1581637
  have hstable : (prefixWord ++ tailWord_1581637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581637).length < 2 ^ (prefixWord ++ tailWord_1581637).sum := by decide
  have hdescent : baseEnd_1581637 < baseStart_1581637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581699 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 5]
def baseStart_1581699 : Nat := 118140960795 + 1581699 * 2 ^ 59
def prefixEnd_1581699 : Nat := 4983230072969 + 3 ^ 40 * 1581699 * 2
def baseEnd_1581699 : Nat := 180482630607980517575201

theorem tailTrace_1581699 : CollatzResearch.WordTrace tailWord_1581699 prefixEnd_1581699 180482630607980517575201 := by
  unfold tailWord_1581699
  simp only [CollatzResearch.WordTrace]
  refine ⟨57689301896782130527948151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38459534597854753685298767 57689301896782130527948151)
  ·
    refine ⟨86533952845173195791922227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57689301896782130527948151 86533952845173195791922227)
    ·
      refine ⟨129800929267759793687883341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86533952845173195791922227 129800929267759793687883341)
      ·
        refine ⟨48675348475409922632956253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129800929267759793687883341 48675348475409922632956253)
        ·
          refine ⟨18253255678278720987358595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48675348475409922632956253 18253255678278720987358595)
          ·
            refine ⟨27379883517418081481037893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18253255678278720987358595 27379883517418081481037893)
            ·
              refine ⟨5133728159515890277694605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27379883517418081481037893 5133728159515890277694605)
              ·
                refine ⟨1925148059818458854135477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5133728159515890277694605 1925148059818458854135477)
                ·
                  refine ⟨180482630607980517575201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925148059818458854135477 180482630607980517575201)
                  ·
                    rfl

theorem cell22_1581699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].length) (baseStart_1581699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581699 prefixEnd_1581699 := by exact prefixLift 1581699
  have htrace : WordTrace (prefixWord ++ tailWord_1581699) baseStart_1581699 baseEnd_1581699 := by
    simpa [prefixWord, tailWord_1581699, baseEnd_1581699] using wordTrace_append hprefix tailTrace_1581699
  have hstable : (prefixWord ++ tailWord_1581699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581699).length < 2 ^ (prefixWord ++ tailWord_1581699).sum := by decide
  have hdescent : baseEnd_1581699 < baseStart_1581699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581791 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1581791 : Nat := 118140960795 + 1581791 * 2 ^ 59
def prefixEnd_1581791 : Nat := 4983230072969 + 3 ^ 40 * 1581791 * 2
def baseEnd_1581791 : Nat := 541479385304083979425321

theorem tailTrace_1581791 : CollatzResearch.WordTrace tailWord_1581791 prefixEnd_1581791 541479385304083979425321 := by
  unfold tailWord_1581791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57692657412448830240297227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38461771608299220160198151 57692657412448830240297227)
  ·
    refine ⟨86538986118673245360445841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57692657412448830240297227 86538986118673245360445841)
    ·
      refine ⟨64904239589004934020334381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86538986118673245360445841 64904239589004934020334381)
      ·
        refine ⟨24339089845876850257625393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64904239589004934020334381 24339089845876850257625393)
        ·
          refine ⟨18254317384407637693219045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24339089845876850257625393 18254317384407637693219045)
          ·
            refine ⟨3422684509576432067478571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18254317384407637693219045 3422684509576432067478571)
            ·
              refine ⟨5134026764364648101217857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422684509576432067478571 5134026764364648101217857)
              ·
                refine ⟨3850520073273486075913393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134026764364648101217857 3850520073273486075913393)
                ·
                  refine ⟨2887890054955114556935045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850520073273486075913393 2887890054955114556935045)
                  ·
                    refine ⟨541479385304083979425321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887890054955114556935045 541479385304083979425321)
                    ·
                      rfl

theorem cell22_1581791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1581791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581791 prefixEnd_1581791 := by exact prefixLift 1581791
  have htrace : WordTrace (prefixWord ++ tailWord_1581791) baseStart_1581791 baseEnd_1581791 := by
    simpa [prefixWord, tailWord_1581791, baseEnd_1581791] using wordTrace_append hprefix tailTrace_1581791
  have hstable : (prefixWord ++ tailWord_1581791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581791).length < 2 ^ (prefixWord ++ tailWord_1581791).sum := by decide
  have hdescent : baseEnd_1581791 < baseStart_1581791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581795 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 4]
def baseStart_1581795 : Nat := 118140960795 + 1581795 * 2 ^ 59
def prefixEnd_1581795 : Nat := 4983230072969 + 3 ^ 40 * 1581795 * 2
def baseEnd_1581795 : Nat := 180493584861943100775103

theorem tailTrace_1581795 : CollatzResearch.WordTrace tailWord_1581795 prefixEnd_1581795 180493584861943100775103 := by
  unfold tailWord_1581795
  simp only [CollatzResearch.WordTrace]
  refine ⟨57692803304434338923442839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38461868869622892615628559 57692803304434338923442839)
  ·
    refine ⟨86539204956651508385164259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57692803304434338923442839 86539204956651508385164259)
    ·
      refine ⟨129808807434977262577746389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86539204956651508385164259 129808807434977262577746389)
      ·
        refine ⟨3042393924257279591665931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 129808807434977262577746389 3042393924257279591665931)
        ·
          refine ⟨4563590886385919387498897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042393924257279591665931 4563590886385919387498897)
          ·
            refine ⟨3422693164789439540624173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563590886385919387498897 3422693164789439540624173)
            ·
              refine ⟨1283509936796039827734065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3422693164789439540624173 1283509936796039827734065)
              ·
                refine ⟨962632452597029870800549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283509936796039827734065 962632452597029870800549)
                ·
                  refine ⟨180493584861943100775103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962632452597029870800549 180493584861943100775103)
                  ·
                    rfl

theorem cell22_1581795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 4].length) (baseStart_1581795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581795 prefixEnd_1581795 := by exact prefixLift 1581795
  have htrace : WordTrace (prefixWord ++ tailWord_1581795) baseStart_1581795 baseEnd_1581795 := by
    simpa [prefixWord, tailWord_1581795, baseEnd_1581795] using wordTrace_append hprefix tailTrace_1581795
  have hstable : (prefixWord ++ tailWord_1581795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581795).length < 2 ^ (prefixWord ++ tailWord_1581795).sum := by decide
  have hdescent : baseEnd_1581795 < baseStart_1581795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581806 : List Nat := [4, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1581806 : Nat := 118140960795 + 1581806 * 2 ^ 59
def prefixEnd_1581806 : Nat := 4983230072969 + 3 ^ 40 * 1581806 * 2
def baseEnd_1581806 : Nat := 60164946678958771144475

theorem tailTrace_1581806 : CollatzResearch.WordTrace tailWord_1581806 prefixEnd_1581806 60164946678958771144475 := by
  unfold tailWord_1581806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211650563424310975261659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38462136338262991868062181 7211650563424310975261659)
  ·
    refine ⟨10817475845136466462892489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7211650563424310975261659 10817475845136466462892489)
    ·
      refine ⟨8113106883852349847169367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10817475845136466462892489 8113106883852349847169367)
      ·
        refine ⟨12169660325778524770754051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113106883852349847169367 12169660325778524770754051)
        ·
          refine ⟨18254490488667787156131077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12169660325778524770754051 18254490488667787156131077)
          ·
            refine ⟨3422716966625210091774577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18254490488667787156131077 3422716966625210091774577)
            ·
              refine ⟨2567037724968907568830933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422716966625210091774577 2567037724968907568830933)
              ·
                refine ⟨60164946678958771144475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2567037724968907568830933 60164946678958771144475)
                ·
                  rfl

theorem cell22_1581806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1581806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581806 prefixEnd_1581806 := by exact prefixLift 1581806
  have htrace : WordTrace (prefixWord ++ tailWord_1581806) baseStart_1581806 baseEnd_1581806 := by
    simpa [prefixWord, tailWord_1581806, baseEnd_1581806] using wordTrace_append hprefix tailTrace_1581806
  have hstable : (prefixWord ++ tailWord_1581806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581806).length < 2 ^ (prefixWord ++ tailWord_1581806).sum := by decide
  have hdescent : baseEnd_1581806 < baseStart_1581806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581810 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_1581810 : Nat := 118140960795 + 1581810 * 2 ^ 59
def prefixEnd_1581810 : Nat := 4983230072969 + 3 ^ 40 * 1581810 * 2
def baseEnd_1581810 : Nat := 541485889392374263200263

theorem tailTrace_1581810 : CollatzResearch.WordTrace tailWord_1581810 prefixEnd_1581810 541485889392374263200263 := by
  unfold tailWord_1581810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14423337599844999121309721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38462233599586664323492589 14423337599844999121309721)
  ·
    refine ⟨10817503199883749340982291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14423337599844999121309721 10817503199883749340982291)
    ·
      refine ⟨16226254799825624011473437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817503199883749340982291 16226254799825624011473437)
      ·
        refine ⟨6084845549934609004302539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16226254799825624011473437 6084845549934609004302539)
        ·
          refine ⟨9127268324901913506453809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084845549934609004302539 9127268324901913506453809)
          ·
            refine ⟨6845451243676435129840357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9127268324901913506453809 6845451243676435129840357)
            ·
              refine ⟨1283522108189331586845067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6845451243676435129840357 1283522108189331586845067)
              ·
                refine ⟨1925283162283997380267601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283522108189331586845067 1925283162283997380267601)
                ·
                  refine ⟨1443962371712998035200701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925283162283997380267601 1443962371712998035200701)
                  ·
                    refine ⟨541485889392374263200263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443962371712998035200701 541485889392374263200263)
                    ·
                      rfl

theorem cell22_1581810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_1581810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581810 prefixEnd_1581810 := by exact prefixLift 1581810
  have htrace : WordTrace (prefixWord ++ tailWord_1581810) baseStart_1581810 baseEnd_1581810 := by
    simpa [prefixWord, tailWord_1581810, baseEnd_1581810] using wordTrace_append hprefix tailTrace_1581810
  have hstable : (prefixWord ++ tailWord_1581810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581810).length < 2 ^ (prefixWord ++ tailWord_1581810).sum := by decide
  have hdescent : baseEnd_1581810 < baseStart_1581810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581821 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_1581821 : Nat := 118140960795 + 1581821 * 2 ^ 59
def prefixEnd_1581821 : Nat := 4983230072969 + 3 ^ 40 * 1581821 * 2
def baseEnd_1581821 : Nat := 541489654917173901175229

theorem tailTrace_1581821 : CollatzResearch.WordTrace tailWord_1581821 prefixEnd_1581821 541489654917173901175229 := by
  unfold tailWord_1581821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57693751602340145363889317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38462501068226763575926211 57693751602340145363889317)
  ·
    refine ⟨10817578425438777255729247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57693751602340145363889317 10817578425438777255729247)
    ·
      refine ⟨16226367638158165883593871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10817578425438777255729247 16226367638158165883593871)
      ·
        refine ⟨24339551457237248825390807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16226367638158165883593871 24339551457237248825390807)
        ·
          refine ⟨36509327185855873238086211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24339551457237248825390807 36509327185855873238086211)
          ·
            refine ⟨54763990778783809857129317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36509327185855873238086211 54763990778783809857129317)
            ·
              refine ⟨10268248271021964348211747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54763990778783809857129317 10268248271021964348211747)
              ·
                refine ⟨15402372406532946522317621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10268248271021964348211747 15402372406532946522317621)
                ·
                  refine ⟨1443972413112463736467277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15402372406532946522317621 1443972413112463736467277)
                  ·
                    refine ⟨541489654917173901175229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443972413112463736467277 541489654917173901175229)
                    ·
                      rfl

theorem cell22_1581821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_1581821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581821 prefixEnd_1581821 := by exact prefixLift 1581821
  have htrace : WordTrace (prefixWord ++ tailWord_1581821) baseStart_1581821 baseEnd_1581821 := by
    simpa [prefixWord, tailWord_1581821, baseEnd_1581821] using wordTrace_append hprefix tailTrace_1581821
  have hstable : (prefixWord ++ tailWord_1581821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581821).length < 2 ^ (prefixWord ++ tailWord_1581821).sum := by decide
  have hdescent : baseEnd_1581821 < baseStart_1581821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581855 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 1, 3]
def baseStart_1581855 : Nat := 118140960795 + 1581855 * 2 ^ 59
def prefixEnd_1581855 : Nat := 4983230072969 + 3 ^ 40 * 1581855 * 2
def baseEnd_1581855 : Nat := 541501293812009145825125

theorem tailTrace_1581855 : CollatzResearch.WordTrace tailWord_1581855 prefixEnd_1581855 541501293812009145825125 := by
  unfold tailWord_1581855
  simp only [CollatzResearch.WordTrace]
  refine ⟨57694991684216969170627019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38463327789477979447084679 57694991684216969170627019)
  ·
    refine ⟨86542487526325453755940529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57694991684216969170627019 86542487526325453755940529)
    ·
      refine ⟨64906865644744090316955397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86542487526325453755940529 64906865644744090316955397)
      ·
        refine ⟨12170037308389516934429137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64906865644744090316955397 12170037308389516934429137)
        ·
          refine ⟨9127527981292137700821853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12170037308389516934429137 9127527981292137700821853)
          ·
            refine ⟨3422822992984551637808195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9127527981292137700821853 3422822992984551637808195)
            ·
              refine ⟨5134234489476827456712293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422822992984551637808195 5134234489476827456712293)
              ·
                refine ⟨962668966776905148133555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5134234489476827456712293 962668966776905148133555)
                ·
                  refine ⟨1444003450165357722200333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962668966776905148133555 1444003450165357722200333)
                  ·
                    refine ⟨541501293812009145825125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444003450165357722200333 541501293812009145825125)
                    ·
                      rfl

theorem cell22_1581855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_1581855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581855 prefixEnd_1581855 := by exact prefixLift 1581855
  have htrace : WordTrace (prefixWord ++ tailWord_1581855) baseStart_1581855 baseEnd_1581855 := by
    simpa [prefixWord, tailWord_1581855, baseEnd_1581855] using wordTrace_append hprefix tailTrace_1581855
  have hstable : (prefixWord ++ tailWord_1581855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581855).length < 2 ^ (prefixWord ++ tailWord_1581855).sum := by decide
  have hdescent : baseEnd_1581855 < baseStart_1581855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581889 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1581889 : Nat := 118140960795 + 1581889 * 2 ^ 59
def prefixEnd_1581889 : Nat := 4983230072969 + 3 ^ 40 * 1581889 * 2
def baseEnd_1581889 : Nat := 541512932706844390475021

theorem tailTrace_1581889 : CollatzResearch.WordTrace tailWord_1581889 prefixEnd_1581889 541512932706844390475021 := by
  unfold tailWord_1581889
  simp only [CollatzResearch.WordTrace]
  refine ⟨57696231766093792977364721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38464154510729195318243147 57696231766093792977364721)
  ·
    refine ⟨43272173824570344733023541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57696231766093792977364721 43272173824570344733023541)
    ·
      refine ⟨4056766296053469818720957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43272173824570344733023541 4056766296053469818720957)
      ·
        refine ⟨1521287361020051182020359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4056766296053469818720957 1521287361020051182020359)
        ·
          refine ⟨2281931041530076773030539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521287361020051182020359 2281931041530076773030539)
          ·
            refine ⟨3422896562295115159545809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281931041530076773030539 3422896562295115159545809)
            ·
              refine ⟨2567172421721336369659357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422896562295115159545809 2567172421721336369659357)
              ·
                refine ⟨962689658145501138622259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567172421721336369659357 962689658145501138622259)
                ·
                  refine ⟨1444034487218251707933389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962689658145501138622259 1444034487218251707933389)
                  ·
                    refine ⟨541512932706844390475021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444034487218251707933389 541512932706844390475021)
                    ·
                      rfl

theorem cell22_1581889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1581889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581889 prefixEnd_1581889 := by exact prefixLift 1581889
  have htrace : WordTrace (prefixWord ++ tailWord_1581889) baseStart_1581889 baseEnd_1581889 := by
    simpa [prefixWord, tailWord_1581889, baseEnd_1581889] using wordTrace_append hprefix tailTrace_1581889
  have hstable : (prefixWord ++ tailWord_1581889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581889).length < 2 ^ (prefixWord ++ tailWord_1581889).sum := by decide
  have hdescent : baseEnd_1581889 < baseStart_1581889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581913 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 4]
def baseStart_1581913 : Nat := 118140960795 + 1581913 * 2 ^ 59
def prefixEnd_1581913 : Nat := 4983230072969 + 3 ^ 40 * 1581913 * 2
def baseEnd_1581913 : Nat := 180507049465772109291649

theorem tailTrace_1581913 : CollatzResearch.WordTrace tailWord_1581913 prefixEnd_1581913 180507049465772109291649 := by
  unfold tailWord_1581913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57697107118006845076238393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38464738078671230050825595 57697107118006845076238393)
  ·
    refine ⟨43272830338505133807178795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57697107118006845076238393 43272830338505133807178795)
    ·
      refine ⟨64909245507757700710768193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43272830338505133807178795 64909245507757700710768193)
      ·
        refine ⟨48681934130818275533076145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64909245507757700710768193 48681934130818275533076145)
        ·
          refine ⟨36511450598113706649807109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48681934130818275533076145 36511450598113706649807109)
          ·
            refine ⟨6845896987146319996838833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36511450598113706649807109 6845896987146319996838833)
            ·
              refine ⟨5134422740359739997629125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845896987146319996838833 5134422740359739997629125)
              ·
                refine ⟨962704263817451249555461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5134422740359739997629125 962704263817451249555461)
                ·
                  refine ⟨180507049465772109291649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962704263817451249555461 180507049465772109291649)
                  ·
                    rfl

theorem cell22_1581913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_1581913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581913 prefixEnd_1581913 := by exact prefixLift 1581913
  have htrace : WordTrace (prefixWord ++ tailWord_1581913) baseStart_1581913 baseEnd_1581913 := by
    simpa [prefixWord, tailWord_1581913, baseEnd_1581913] using wordTrace_append hprefix tailTrace_1581913
  have hstable : (prefixWord ++ tailWord_1581913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581913).length < 2 ^ (prefixWord ++ tailWord_1581913).sum := by decide
  have hdescent : baseEnd_1581913 < baseStart_1581913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581928 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1581928 : Nat := 118140960795 + 1581928 * 2 ^ 59
def prefixEnd_1581928 : Nat := 4983230072969 + 3 ^ 40 * 1581928 * 2
def baseEnd_1581928 : Nat := 541526283203861288749901

theorem tailTrace_1581928 : CollatzResearch.WordTrace tailWord_1581928 prefixEnd_1581928 541526283203861288749901 := by
  unfold tailWord_1581928
  simp only [CollatzResearch.WordTrace]
  refine ⟨28848827106476251319017219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38465102808635001758689625 28848827106476251319017219)
  ·
    refine ⟨43273240659714376978525829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28848827106476251319017219 43273240659714376978525829)
    ·
      refine ⟨8113732623696445683473593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43273240659714376978525829 8113732623696445683473593)
      ·
        refine ⟨6085299467772334262605195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8113732623696445683473593 6085299467772334262605195)
        ·
          refine ⟨9127949201658501393907793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6085299467772334262605195 9127949201658501393907793)
          ·
            refine ⟨6845961901243876045430845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9127949201658501393907793 6845961901243876045430845)
            ·
              refine ⟨2567235712966453517036567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6845961901243876045430845 2567235712966453517036567)
              ·
                refine ⟨3850853569449680275554851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567235712966453517036567 3850853569449680275554851)
                ·
                  refine ⟨5776280354174520413332277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850853569449680275554851 5776280354174520413332277)
                  ·
                    refine ⟨541526283203861288749901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776280354174520413332277 541526283203861288749901)
                    ·
                      rfl

theorem cell22_1581928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1581928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1581928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1581928 prefixEnd_1581928 := by exact prefixLift 1581928
  have htrace : WordTrace (prefixWord ++ tailWord_1581928) baseStart_1581928 baseEnd_1581928 := by
    simpa [prefixWord, tailWord_1581928, baseEnd_1581928] using wordTrace_append hprefix tailTrace_1581928
  have hstable : (prefixWord ++ tailWord_1581928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581928).length < 2 ^ (prefixWord ++ tailWord_1581928).sum := by decide
  have hdescent : baseEnd_1581928 < baseStart_1581928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582063 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 5]
def baseStart_1582063 : Nat := 118140960795 + 1582063 * 2 ^ 59
def prefixEnd_1582063 : Nat := 4983230072969 + 3 ^ 40 * 1582063 * 2
def baseEnd_1582063 : Nat := 541572496462765936624487

theorem tailTrace_1582063 : CollatzResearch.WordTrace tailWord_1582063 prefixEnd_1582063 541572496462765936624487 := by
  unfold tailWord_1582063
  simp only [CollatzResearch.WordTrace]
  refine ⟨57702578067463420694198843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38468385378308947129465895 57702578067463420694198843)
  ·
    refine ⟨86553867101195131041298265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57702578067463420694198843 86553867101195131041298265)
    ·
      refine ⟨64915400325896348280973699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86553867101195131041298265 64915400325896348280973699)
      ·
        refine ⟨97373100488844522421460549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64915400325896348280973699 97373100488844522421460549)
        ·
          refine ⟨18257456341658347954023853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97373100488844522421460549 18257456341658347954023853)
          ·
            refine ⟨6846546128121880482758945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18257456341658347954023853 6846546128121880482758945)
            ·
              refine ⟨5134909596091410362069209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846546128121880482758945 5134909596091410362069209)
              ·
                refine ⟨3851182197068557771551907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134909596091410362069209 3851182197068557771551907)
                ·
                  refine ⟨5776773295602836657327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851182197068557771551907 5776773295602836657327861)
                  ·
                    refine ⟨541572496462765936624487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776773295602836657327861 541572496462765936624487)
                    ·
                      rfl

theorem cell22_1582063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_1582063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582063 prefixEnd_1582063 := by exact prefixLift 1582063
  have htrace : WordTrace (prefixWord ++ tailWord_1582063) baseStart_1582063 baseEnd_1582063 := by
    simpa [prefixWord, tailWord_1582063, baseEnd_1582063] using wordTrace_append hprefix tailTrace_1582063
  have hstable : (prefixWord ++ tailWord_1582063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582063).length < 2 ^ (prefixWord ++ tailWord_1582063).sum := by decide
  have hdescent : baseEnd_1582063 < baseStart_1582063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582065 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 4]
def baseStart_1582065 : Nat := 118140960795 + 1582065 * 2 ^ 59
def prefixEnd_1582065 : Nat := 4983230072969 + 3 ^ 40 * 1582065 * 2
def baseEnd_1582065 : Nat := 180524393701212866024827

theorem tailTrace_1582065 : CollatzResearch.WordTrace tailWord_1582065 prefixEnd_1582065 180524393701212866024827 := by
  unfold tailWord_1582065
  simp only [CollatzResearch.WordTrace]
  refine ⟨57702651013456175035771649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38468434008970783357181099 57702651013456175035771649)
  ·
    refine ⟨43276988260092131276828737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57702651013456175035771649 43276988260092131276828737)
    ·
      refine ⟨32457741195069098457621553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43276988260092131276828737 32457741195069098457621553)
      ·
        refine ⟨24343305896301823843216165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32457741195069098457621553 24343305896301823843216165)
        ·
          refine ⟨4564369855556591970603031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24343305896301823843216165 4564369855556591970603031)
          ·
            refine ⟨6846554783334887955904547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564369855556591970603031 6846554783334887955904547)
            ·
              refine ⟨10269832175002331933856821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846554783334887955904547 10269832175002331933856821)
              ·
                refine ⟨962796766406468618799077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10269832175002331933856821 962796766406468618799077)
                ·
                  refine ⟨180524393701212866024827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962796766406468618799077 180524393701212866024827)
                  ·
                    rfl

theorem cell22_1582065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_1582065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582065 prefixEnd_1582065 := by exact prefixLift 1582065
  have htrace : WordTrace (prefixWord ++ tailWord_1582065) baseStart_1582065 baseEnd_1582065 := by
    simpa [prefixWord, tailWord_1582065, baseEnd_1582065] using wordTrace_append hprefix tailTrace_1582065
  have hstable : (prefixWord ++ tailWord_1582065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582065).length < 2 ^ (prefixWord ++ tailWord_1582065).sum := by decide
  have hdescent : baseEnd_1582065 < baseStart_1582065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582138 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_1582138 : Nat := 118140960795 + 1582138 * 2 ^ 59
def prefixEnd_1582138 : Nat := 4983230072969 + 3 ^ 40 * 1582138 * 2
def baseEnd_1582138 : Nat := 180532723498496913666419

theorem tailTrace_1582138 : CollatzResearch.WordTrace tailWord_1582138 prefixEnd_1582138 180532723498496913666419 := by
  unfold tailWord_1582138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426328385547927125794767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38470209028127805668786045 14426328385547927125794767)
  ·
    refine ⟨21639492578321890688692151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426328385547927125794767 21639492578321890688692151)
    ·
      refine ⟨32459238867482836033038227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21639492578321890688692151 32459238867482836033038227)
      ·
        refine ⟨48688858301224254049557341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32459238867482836033038227 48688858301224254049557341)
        ·
          refine ⟨18258321862959095268584003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48688858301224254049557341 18258321862959095268584003)
          ·
            refine ⟨27387482794438642902876005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18258321862959095268584003 27387482794438642902876005)
            ·
              refine ⟨5135153023957245544289251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27387482794438642902876005 5135153023957245544289251)
              ·
                refine ⟨7702729535935868316433877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135153023957245544289251 7702729535935868316433877)
                ·
                  refine ⟨180532723498496913666419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7702729535935868316433877 180532723498496913666419)
                  ·
                    rfl

theorem cell22_1582138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_1582138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582138 prefixEnd_1582138 := by exact prefixLift 1582138
  have htrace : WordTrace (prefixWord ++ tailWord_1582138) baseStart_1582138 baseEnd_1582138 := by
    simpa [prefixWord, tailWord_1582138, baseEnd_1582138] using wordTrace_append hprefix tailTrace_1582138
  have hstable : (prefixWord ++ tailWord_1582138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582138).length < 2 ^ (prefixWord ++ tailWord_1582138).sum := by decide
  have hdescent : baseEnd_1582138 < baseStart_1582138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582215 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 6, 3]
def baseStart_1582215 : Nat := 118140960795 + 1582215 * 2 ^ 59
def prefixEnd_1582215 : Nat := 4983230072969 + 3 ^ 40 * 1582215 * 2
def baseEnd_1582215 : Nat := 541624529169088206824021

theorem tailTrace_1582215 : CollatzResearch.WordTrace tailWord_1582215 prefixEnd_1582215 541624529169088206824021 := by
  unfold tailWord_1582215
  simp only [CollatzResearch.WordTrace]
  refine ⟨57708121962912750653732099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38472081308608500435821399 57708121962912750653732099)
  ·
    refine ⟨86562182944369125980598149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57708121962912750653732099 86562182944369125980598149)
    ·
      refine ⟨16230409302069211121362153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86562182944369125980598149 16230409302069211121362153)
      ·
        refine ⟨12172806976551908341021615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16230409302069211121362153 12172806976551908341021615)
        ·
          refine ⟨18259210464827862511532423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12172806976551908341021615 18259210464827862511532423)
          ·
            refine ⟨27388815697241793767298635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18259210464827862511532423 27388815697241793767298635)
            ·
              refine ⟨41083223545862690650947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27388815697241793767298635 41083223545862690650947953)
              ·
                refine ⟨30812417659397017988210965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41083223545862690650947953 30812417659397017988210965)
                ·
                  refine ⟨1444332077784235218197389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30812417659397017988210965 1444332077784235218197389)
                  ·
                    refine ⟨541624529169088206824021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444332077784235218197389 541624529169088206824021)
                    ·
                      rfl

theorem cell22_1582215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_1582215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582215 prefixEnd_1582215 := by exact prefixLift 1582215
  have htrace : WordTrace (prefixWord ++ tailWord_1582215) baseStart_1582215 baseEnd_1582215 := by
    simpa [prefixWord, tailWord_1582215, baseEnd_1582215] using wordTrace_append hprefix tailTrace_1582215
  have hstable : (prefixWord ++ tailWord_1582215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582215).length < 2 ^ (prefixWord ++ tailWord_1582215).sum := by decide
  have hdescent : baseEnd_1582215 < baseStart_1582215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582234 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_1582234 : Nat := 118140960795 + 1582234 * 2 ^ 59
def prefixEnd_1582234 : Nat := 4983230072969 + 3 ^ 40 * 1582234 * 2
def baseEnd_1582234 : Nat := 180543677752459496866321

theorem tailTrace_1582234 : CollatzResearch.WordTrace tailWord_1582234 prefixEnd_1582234 180543677752459496866321 := by
  unfold tailWord_1582234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427203737460979224668439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38472543299895944599115837 14427203737460979224668439)
  ·
    refine ⟨21640805606191468837002659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14427203737460979224668439 21640805606191468837002659)
    ·
      refine ⟨32461208409287203255503989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640805606191468837002659 32461208409287203255503989)
      ·
        refine ⟨3043238288370675305203499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32461208409287203255503989 3043238288370675305203499)
        ·
          refine ⟨4564857432556012957805249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043238288370675305203499 4564857432556012957805249)
          ·
            refine ⟨3423643074417009718353937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4564857432556012957805249 3423643074417009718353937)
            ·
              refine ⟨2567732305812757288765453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423643074417009718353937 2567732305812757288765453)
              ·
                refine ⟨962899614679783983287045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567732305812757288765453 962899614679783983287045)
                ·
                  refine ⟨180543677752459496866321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962899614679783983287045 180543677752459496866321)
                  ·
                    rfl

theorem cell22_1582234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_1582234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582234 prefixEnd_1582234 := by exact prefixLift 1582234
  have htrace : WordTrace (prefixWord ++ tailWord_1582234) baseStart_1582234 baseEnd_1582234 := by
    simpa [prefixWord, tailWord_1582234, baseEnd_1582234] using wordTrace_append hprefix tailTrace_1582234
  have hstable : (prefixWord ++ tailWord_1582234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582234).length < 2 ^ (prefixWord ++ tailWord_1582234).sum := by decide
  have hdescent : baseEnd_1582234 < baseStart_1582234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582243 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 9]
def baseStart_1582243 : Nat := 118140960795 + 1582243 * 2 ^ 59
def prefixEnd_1582243 : Nat := 4983230072969 + 3 ^ 40 * 1582243 * 2
def baseEnd_1582243 : Nat := 541634114141305467123935

theorem tailTrace_1582243 : CollatzResearch.WordTrace tailWord_1582243 prefixEnd_1582243 541634114141305467123935 := by
  unfold tailWord_1582243
  simp only [CollatzResearch.WordTrace]
  refine ⟨57709143206811311435751383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38472762137874207623834255 57709143206811311435751383)
  ·
    refine ⟨86563714810216967153627075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57709143206811311435751383 86563714810216967153627075)
    ·
      refine ⟨129845572215325450730440613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86563714810216967153627075 129845572215325450730440613)
      ·
        refine ⟨24346044790373522011957615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129845572215325450730440613 24346044790373522011957615)
        ·
          refine ⟨36519067185560283017936423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24346044790373522011957615 36519067185560283017936423)
          ·
            refine ⟨54778600778340424526904635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36519067185560283017936423 54778600778340424526904635)
            ·
              refine ⟨82167901167510636790356953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54778600778340424526904635 82167901167510636790356953)
              ·
                refine ⟨61625925875632977592767715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82167901167510636790356953 61625925875632977592767715)
                ·
                  refine ⟨92438888813449466389151573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61625925875632977592767715 92438888813449466389151573)
                  ·
                    refine ⟨541634114141305467123935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92438888813449466389151573 541634114141305467123935)
                    ·
                      rfl

theorem cell22_1582243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_1582243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582243 prefixEnd_1582243 := by exact prefixLift 1582243
  have htrace : WordTrace (prefixWord ++ tailWord_1582243) baseStart_1582243 baseEnd_1582243 := by
    simpa [prefixWord, tailWord_1582243, baseEnd_1582243] using wordTrace_append hprefix tailTrace_1582243
  have hstable : (prefixWord ++ tailWord_1582243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582243).length < 2 ^ (prefixWord ++ tailWord_1582243).sum := by decide
  have hdescent : baseEnd_1582243 < baseStart_1582243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582285 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1582285 : Nat := 118140960795 + 1582285 * 2 ^ 59
def prefixEnd_1582285 : Nat := 4983230072969 + 3 ^ 40 * 1582285 * 2
def baseEnd_1582285 : Nat := 180549497199877119191269

theorem tailTrace_1582285 : CollatzResearch.WordTrace tailWord_1582285 prefixEnd_1582285 180549497199877119191269 := by
  unfold tailWord_1582285
  simp only [CollatzResearch.WordTrace]
  refine ⟨57710675072659152608780309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38473783381772768405853539 57710675072659152608780309)
  ·
    refine ⟨2705187894030897778536577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57710675072659152608780309 2705187894030897778536577)
    ·
      refine ⟨2028890920523173333902433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2705187894030897778536577 2028890920523173333902433)
      ·
        refine ⟨1521668190392380000426825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028890920523173333902433 1521668190392380000426825)
        ·
          refine ⟨1141251142794285000320119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521668190392380000426825 1141251142794285000320119)
          ·
            refine ⟨1711876714191427500480179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141251142794285000320119 1711876714191427500480179)
            ·
              refine ⟨2567815071287141250720269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711876714191427500480179 2567815071287141250720269)
              ·
                refine ⟨962930651732677969020101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567815071287141250720269 962930651732677969020101)
                ·
                  refine ⟨180549497199877119191269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962930651732677969020101 180549497199877119191269)
                  ·
                    rfl

theorem cell22_1582285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1582285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582285 prefixEnd_1582285 := by exact prefixLift 1582285
  have htrace : WordTrace (prefixWord ++ tailWord_1582285) baseStart_1582285 baseEnd_1582285 := by
    simpa [prefixWord, tailWord_1582285, baseEnd_1582285] using wordTrace_append hprefix tailTrace_1582285
  have hstable : (prefixWord ++ tailWord_1582285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582285).length < 2 ^ (prefixWord ++ tailWord_1582285).sum := by decide
  have hdescent : baseEnd_1582285 < baseStart_1582285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582290 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_1582290 : Nat := 118140960795 + 1582290 * 2 ^ 59
def prefixEnd_1582290 : Nat := 4983230072969 + 3 ^ 40 * 1582290 * 2
def baseEnd_1582290 : Nat := 180550067733937670399597

theorem tailTrace_1582290 : CollatzResearch.WordTrace tailWord_1582290 prefixEnd_1582290 180550067733937670399597 := by
  unfold tailWord_1582290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427714359410259615678081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38473904958427358975141549 14427714359410259615678081)
  ·
    refine ⟨10820785769557694711758561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14427714359410259615678081 10820785769557694711758561)
    ·
      refine ⟨8115589327168271033818921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10820785769557694711758561 8115589327168271033818921)
      ·
        refine ⟨6086691995376203275364191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8115589327168271033818921 6086691995376203275364191)
        ·
          refine ⟨9130037993064304913046287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6086691995376203275364191 9130037993064304913046287)
          ·
            refine ⟨13695056989596457369569431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130037993064304913046287 13695056989596457369569431)
            ·
              refine ⟨20542585484394686054354147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13695056989596457369569431 20542585484394686054354147)
              ·
                refine ⟨30813878226592029081531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20542585484394686054354147 30813878226592029081531221)
                ·
                  refine ⟨180550067733937670399597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30813878226592029081531221 180550067733937670399597)
                  ·
                    rfl

theorem cell22_1582290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_1582290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582290 prefixEnd_1582290 := by exact prefixLift 1582290
  have htrace : WordTrace (prefixWord ++ tailWord_1582290) baseStart_1582290 baseEnd_1582290 := by
    simpa [prefixWord, tailWord_1582290, baseEnd_1582290] using wordTrace_append hprefix tailTrace_1582290
  have hstable : (prefixWord ++ tailWord_1582290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582290).length < 2 ^ (prefixWord ++ tailWord_1582290).sum := by decide
  have hdescent : baseEnd_1582290 < baseStart_1582290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582311 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1582311 : Nat := 118140960795 + 1582311 * 2 ^ 59
def prefixEnd_1582311 : Nat := 4983230072969 + 3 ^ 40 * 1582311 * 2
def baseEnd_1582311 : Nat := 541657391930975956423727

theorem tailTrace_1582311 : CollatzResearch.WordTrace tailWord_1582311 prefixEnd_1582311 541657391930975956423727 := by
  unfold tailWord_1582311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57711623370564959049226787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38474415580376639366151191 57711623370564959049226787)
  ·
    refine ⟨86567435055847438573840181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57711623370564959049226787 86567435055847438573840181)
    ·
      refine ⟨8115697036485697366297517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86567435055847438573840181 8115697036485697366297517)
      ·
        refine ⟨3043386388682136512361569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8115697036485697366297517 3043386388682136512361569)
        ·
          refine ⟨2282539791511602384271177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043386388682136512361569 2282539791511602384271177)
          ·
            refine ⟨1711904843633701788203383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282539791511602384271177 1711904843633701788203383)
            ·
              refine ⟨2567857265450552682305075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711904843633701788203383 2567857265450552682305075)
              ·
                refine ⟨3851785898175829023457613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567857265450552682305075 3851785898175829023457613)
                ·
                  refine ⟨1444419711815935883796605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3851785898175829023457613 1444419711815935883796605)
                  ·
                    refine ⟨541657391930975956423727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444419711815935883796605 541657391930975956423727)
                    ·
                      rfl

theorem cell22_1582311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1582311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582311 prefixEnd_1582311 := by exact prefixLift 1582311
  have htrace : WordTrace (prefixWord ++ tailWord_1582311) baseStart_1582311 baseEnd_1582311 := by
    simpa [prefixWord, tailWord_1582311, baseEnd_1582311] using wordTrace_append hprefix tailTrace_1582311
  have hstable : (prefixWord ++ tailWord_1582311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582311).length < 2 ^ (prefixWord ++ tailWord_1582311).sum := by decide
  have hdescent : baseEnd_1582311 < baseStart_1582311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582337 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1582337 : Nat := 118140960795 + 1582337 * 2 ^ 59
def prefixEnd_1582337 : Nat := 4983230072969 + 3 ^ 40 * 1582337 * 2
def baseEnd_1582337 : Nat := 541666292262320555273647

theorem tailTrace_1582337 : CollatzResearch.WordTrace tailWord_1582337 prefixEnd_1582337 541666292262320555273647 := by
  unfold tailWord_1582337
  simp only [CollatzResearch.WordTrace]
  refine ⟨57712571668470765489673265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38475047778980510326448843 57712571668470765489673265)
  ·
    refine ⟨43284428751353074117254949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57712571668470765489673265 43284428751353074117254949)
    ·
      refine ⟨8115830390878701396985303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43284428751353074117254949 8115830390878701396985303)
      ·
        refine ⟨12173745586318052095477955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115830390878701396985303 12173745586318052095477955)
        ·
          refine ⟨18260618379477078143216933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173745586318052095477955 18260618379477078143216933)
          ·
            refine ⟨3423865946151952151853175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18260618379477078143216933 3423865946151952151853175)
            ·
              refine ⟨5135798919227928227779763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423865946151952151853175 5135798919227928227779763)
              ·
                refine ⟨7703698378841892341669645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5135798919227928227779763 7703698378841892341669645)
                ·
                  refine ⟨2888886892065709628126117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7703698378841892341669645 2888886892065709628126117)
                  ·
                    refine ⟨541666292262320555273647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2888886892065709628126117 541666292262320555273647)
                    ·
                      rfl

theorem cell22_1582337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1582337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582337 prefixEnd_1582337 := by exact prefixLift 1582337
  have htrace : WordTrace (prefixWord ++ tailWord_1582337) baseStart_1582337 baseEnd_1582337 := by
    simpa [prefixWord, tailWord_1582337, baseEnd_1582337] using wordTrace_append hprefix tailTrace_1582337
  have hstable : (prefixWord ++ tailWord_1582337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582337).length < 2 ^ (prefixWord ++ tailWord_1582337).sum := by decide
  have hdescent : baseEnd_1582337 < baseStart_1582337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582399 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 2, 4]
def baseStart_1582399 : Nat := 118140960795 + 1582399 * 2 ^ 59
def prefixEnd_1582399 : Nat := 4983230072969 + 3 ^ 40 * 1582399 * 2
def baseEnd_1582399 : Nat := 541687516129373060223457

theorem tailTrace_1582399 : CollatzResearch.WordTrace tailWord_1582399 prefixEnd_1582399 541687516129373060223457 := by
  unfold tailWord_1582399
  simp only [CollatzResearch.WordTrace]
  refine ⟨57714832994246150078430251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38476555329497433385620167 57714832994246150078430251)
  ·
    refine ⟨86572249491369225117645377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57714832994246150078430251 86572249491369225117645377)
    ·
      refine ⟨64929187118526918838234033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86572249491369225117645377 64929187118526918838234033)
      ·
        refine ⟨48696890338895189128675525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64929187118526918838234033 48696890338895189128675525)
        ·
          refine ⟨9130666938542847961626661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48696890338895189128675525 9130666938542847961626661)
          ·
            refine ⟨1712000050976783992804999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9130666938542847961626661 1712000050976783992804999)
            ·
              refine ⟨2568000076465175989207499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712000050976783992804999 2568000076465175989207499)
              ·
                refine ⟨3852000114697763983811249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568000076465175989207499 3852000114697763983811249)
                ·
                  refine ⟨2889000086023322987858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3852000114697763983811249 2889000086023322987858437)
                  ·
                    refine ⟨541687516129373060223457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889000086023322987858437 541687516129373060223457)
                    ·
                      rfl

theorem cell22_1582399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_1582399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582399 prefixEnd_1582399 := by exact prefixLift 1582399
  have htrace : WordTrace (prefixWord ++ tailWord_1582399) baseStart_1582399 baseEnd_1582399 := by
    simpa [prefixWord, tailWord_1582399, baseEnd_1582399] using wordTrace_append hprefix tailTrace_1582399
  have hstable : (prefixWord ++ tailWord_1582399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582399).length < 2 ^ (prefixWord ++ tailWord_1582399).sum := by decide
  have hdescent : baseEnd_1582399 < baseStart_1582399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582536 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1582536 : Nat := 118140960795 + 1582536 * 2 ^ 59
def prefixEnd_1582536 : Nat := 4983230072969 + 3 ^ 40 * 1582536 * 2
def baseEnd_1582536 : Nat := 541734414029150369548037

theorem tailTrace_1582536 : CollatzResearch.WordTrace tailWord_1582536 prefixEnd_1582536 541734414029150369548037 := by
  unfold tailWord_1582536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28859914897374911238083731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38479886529833214984111641 28859914897374911238083731)
  ·
    refine ⟨43289872346062366857125597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28859914897374911238083731 43289872346062366857125597)
    ·
      refine ⟨16233702129773387571422099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43289872346062366857125597 16233702129773387571422099)
      ·
        refine ⟨24350553194660081357133149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233702129773387571422099 24350553194660081357133149)
        ·
          refine ⟨9131457447997530508924931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24350553194660081357133149 9131457447997530508924931)
          ·
            refine ⟨13697186171996295763387397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131457447997530508924931 13697186171996295763387397)
            ·
              refine ⟨2568222407249305455635137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13697186171996295763387397 2568222407249305455635137)
              ·
                refine ⟨1926166805436979091726353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568222407249305455635137 1926166805436979091726353)
                ·
                  refine ⟨1444625104077734318794765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1926166805436979091726353 1444625104077734318794765)
                  ·
                    refine ⟨541734414029150369548037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444625104077734318794765 541734414029150369548037)
                    ·
                      rfl

theorem cell22_1582536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1582536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582536 prefixEnd_1582536 := by exact prefixLift 1582536
  have htrace : WordTrace (prefixWord ++ tailWord_1582536) baseStart_1582536 baseEnd_1582536 := by
    simpa [prefixWord, tailWord_1582536, baseEnd_1582536] using wordTrace_append hprefix tailTrace_1582536
  have hstable : (prefixWord ++ tailWord_1582536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582536).length < 2 ^ (prefixWord ++ tailWord_1582536).sum := by decide
  have hdescent : baseEnd_1582536 < baseStart_1582536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582538 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_1582538 : Nat := 118140960795 + 1582538 * 2 ^ 59
def prefixEnd_1582538 : Nat := 4983230072969 + 3 ^ 40 * 1582538 * 2
def baseEnd_1582538 : Nat := 180578366223341010332677

theorem tailTrace_1582538 : CollatzResearch.WordTrace tailWord_1582538 prefixEnd_1582538 180578366223341010332677 := by
  unfold tailWord_1582538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429975685185644204435067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38479935160495051211826845 14429975685185644204435067)
  ·
    refine ⟨21644963527778466306652601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14429975685185644204435067 21644963527778466306652601)
    ·
      refine ⟨16233722645833849729989451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21644963527778466306652601 16233722645833849729989451)
      ·
        refine ⟨24350583968750774594984177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233722645833849729989451 24350583968750774594984177)
        ·
          refine ⟨18262937976563080946238133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24350583968750774594984177 18262937976563080946238133)
          ·
            refine ⟨1712150435302788838709825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18262937976563080946238133 1712150435302788838709825)
            ·
              refine ⟨1284112826477091629032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712150435302788838709825 1284112826477091629032369)
              ·
                refine ⟨963084619857818721774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284112826477091629032369 963084619857818721774277)
                ·
                  refine ⟨180578366223341010332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963084619857818721774277 180578366223341010332677)
                  ·
                    rfl

theorem cell22_1582538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_1582538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582538 prefixEnd_1582538 := by exact prefixLift 1582538
  have htrace : WordTrace (prefixWord ++ tailWord_1582538) baseStart_1582538 baseEnd_1582538 := by
    simpa [prefixWord, tailWord_1582538, baseEnd_1582538] using wordTrace_append hprefix tailTrace_1582538
  have hstable : (prefixWord ++ tailWord_1582538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582538).length < 2 ^ (prefixWord ++ tailWord_1582538).sum := by decide
  have hdescent : baseEnd_1582538 < baseStart_1582538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582611 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 5]
def baseStart_1582611 : Nat := 118140960795 + 1582611 * 2 ^ 59
def prefixEnd_1582611 : Nat := 4983230072969 + 3 ^ 40 * 1582611 * 2
def baseEnd_1582611 : Nat := 180586696020625057974269

theorem tailTrace_1582611 : CollatzResearch.WordTrace tailWord_1582611 prefixEnd_1582611 180586696020625057974269 := by
  unfold tailWord_1582611
  simp only [CollatzResearch.WordTrace]
  refine ⟨57722565269478110285147687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38481710179652073523431791 57722565269478110285147687)
  ·
    refine ⟨86583847904217165427721531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57722565269478110285147687 86583847904217165427721531)
    ·
      refine ⟨129875771856325748141582297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86583847904217165427721531 129875771856325748141582297)
      ·
        refine ⟨97406828892244311106186723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129875771856325748141582297 97406828892244311106186723)
        ·
          refine ⟨146110243338366466659280085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97406828892244311106186723 146110243338366466659280085)
          ·
            refine ⟨3424458828242964062326877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146110243338366466659280085 3424458828242964062326877)
            ·
              refine ⟨1284172060591111523372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3424458828242964062326877 1284172060591111523372579)
              ·
                refine ⟨1926258090886667285058869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284172060591111523372579 1926258090886667285058869)
                ·
                  refine ⟨180586696020625057974269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1926258090886667285058869 180586696020625057974269)
                  ·
                    rfl

theorem cell22_1582611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 5].length) (baseStart_1582611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582611 prefixEnd_1582611 := by exact prefixLift 1582611
  have htrace : WordTrace (prefixWord ++ tailWord_1582611) baseStart_1582611 baseEnd_1582611 := by
    simpa [prefixWord, tailWord_1582611, baseEnd_1582611] using wordTrace_append hprefix tailTrace_1582611
  have hstable : (prefixWord ++ tailWord_1582611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582611).length < 2 ^ (prefixWord ++ tailWord_1582611).sum := by decide
  have hdescent : baseEnd_1582611 < baseStart_1582611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582632 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1582632 : Nat := 118140960795 + 1582632 * 2 ^ 59
def prefixEnd_1582632 : Nat := 4983230072969 + 3 ^ 40 * 1582632 * 2
def baseEnd_1582632 : Nat := 541767276791038119147743

theorem tailTrace_1582632 : CollatzResearch.WordTrace tailWord_1582632 prefixEnd_1582632 541767276791038119147743 := by
  unfold tailWord_1582632
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861665601201015435831075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38482220801601353914441433 28861665601201015435831075)
  ·
    refine ⟨43292498401801523153746613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28861665601201015435831075 43292498401801523153746613)
    ·
      refine ⟨4058671725168892795663745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43292498401801523153746613 4058671725168892795663745)
      ·
        refine ⟨3044003793876669596747809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058671725168892795663745 3044003793876669596747809)
        ·
          refine ⟨2283002845407502197560857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044003793876669596747809 2283002845407502197560857)
          ·
            refine ⟨1712252134055626648170643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283002845407502197560857 1712252134055626648170643)
            ·
              refine ⟨2568378201083439972255965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712252134055626648170643 2568378201083439972255965)
              ·
                refine ⟨963141825406289989595987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568378201083439972255965 963141825406289989595987)
                ·
                  refine ⟨1444712738109434984393981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963141825406289989595987 1444712738109434984393981)
                  ·
                    refine ⟨541767276791038119147743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444712738109434984393981 541767276791038119147743)
                    ·
                      rfl

theorem cell22_1582632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1582632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582632 prefixEnd_1582632 := by exact prefixLift 1582632
  have htrace : WordTrace (prefixWord ++ tailWord_1582632) baseStart_1582632 baseEnd_1582632 := by
    simpa [prefixWord, tailWord_1582632, baseEnd_1582632] using wordTrace_append hprefix tailTrace_1582632
  have hstable : (prefixWord ++ tailWord_1582632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582632).length < 2 ^ (prefixWord ++ tailWord_1582632).sum := by decide
  have hdescent : baseEnd_1582632 < baseStart_1582632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582662 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1582662 : Nat := 118140960795 + 1582662 * 2 ^ 59
def prefixEnd_1582662 : Nat := 4983230072969 + 3 ^ 40 * 1582662 * 2
def baseEnd_1582662 : Nat := 180592515468042680299217

theorem tailTrace_1582662 : CollatzResearch.WordTrace tailWord_1582662 prefixEnd_1582662 180592515468042680299217 := by
  unfold tailWord_1582662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803888293509167062351695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38482950261528897330169493 1803888293509167062351695)
  ·
    refine ⟨2705832440263750593527543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1803888293509167062351695 2705832440263750593527543)
    ·
      refine ⟨4058748660395625890291315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705832440263750593527543 4058748660395625890291315)
      ·
        refine ⟨6088122990593438835436973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058748660395625890291315 6088122990593438835436973)
        ·
          refine ⟨2283046121472539563288865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6088122990593438835436973 2283046121472539563288865)
          ·
            refine ⟨1712284591104404672466649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283046121472539563288865 1712284591104404672466649)
            ·
              refine ⟨1284213443328303504349987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712284591104404672466649 1284213443328303504349987)
              ·
                refine ⟨1926320164992455256524981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284213443328303504349987 1926320164992455256524981)
                ·
                  refine ⟨180592515468042680299217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1926320164992455256524981 180592515468042680299217)
                  ·
                    rfl

theorem cell22_1582662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1582662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582662 prefixEnd_1582662 := by exact prefixLift 1582662
  have htrace : WordTrace (prefixWord ++ tailWord_1582662) baseStart_1582662 baseEnd_1582662 := by
    simpa [prefixWord, tailWord_1582662, baseEnd_1582662] using wordTrace_append hprefix tailTrace_1582662
  have hstable : (prefixWord ++ tailWord_1582662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582662).length < 2 ^ (prefixWord ++ tailWord_1582662).sum := by decide
  have hdescent : baseEnd_1582662 < baseStart_1582662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582701 : List Nat := [1, 5, 1, 1, 5, 9]
def baseStart_1582701 : Nat := 118140960795 + 1582701 * 2 ^ 59
def prefixEnd_1582701 : Nat := 4983230072969 + 3 ^ 40 * 1582701 * 2
def baseEnd_1582701 : Nat := 6688776504952406656451

theorem tailTrace_1582701 : CollatzResearch.WordTrace tailWord_1582701 prefixEnd_1582701 6688776504952406656451 := by
  unfold tailWord_1582701
  simp only [CollatzResearch.WordTrace]
  refine ⟨57725847839152055655923957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38483898559434703770615971 57725847839152055655923957)
  ·
    refine ⟨5411798234920505217742871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57725847839152055655923957 5411798234920505217742871)
    ·
      refine ⟨8117697352380757826614307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5411798234920505217742871 8117697352380757826614307)
      ·
        refine ⟨12176546028571136739921461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8117697352380757826614307 12176546028571136739921461)
        ·
          refine ⟨1141551190178544069367637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12176546028571136739921461 1141551190178544069367637)
          ·
            refine ⟨6688776504952406656451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1141551190178544069367637 6688776504952406656451)
            ·
              rfl

theorem cell22_1582701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 9].length) (baseStart_1582701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582701 prefixEnd_1582701 := by exact prefixLift 1582701
  have htrace : WordTrace (prefixWord ++ tailWord_1582701) baseStart_1582701 baseEnd_1582701 := by
    simpa [prefixWord, tailWord_1582701, baseEnd_1582701] using wordTrace_append hprefix tailTrace_1582701
  have hstable : (prefixWord ++ tailWord_1582701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582701).length < 2 ^ (prefixWord ++ tailWord_1582701).sum := by decide
  have hdescent : baseEnd_1582701 < baseStart_1582701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582716 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1582716 : Nat := 118140960795 + 1582716 * 2 ^ 59
def prefixEnd_1582716 : Nat := 4983230072969 + 3 ^ 40 * 1582716 * 2
def baseEnd_1582716 : Nat := 541796031707689900047485

theorem tailTrace_1582716 : CollatzResearch.WordTrace tailWord_1582716 prefixEnd_1582716 541796031707689900047485 := by
  unfold tailWord_1582716
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863197467048856608860001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38484263289398475478480001 28863197467048856608860001)
  ·
    refine ⟨21647398100286642456645001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28863197467048856608860001 21647398100286642456645001)
    ·
      refine ⟨16235548575214981842483751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21647398100286642456645001 16235548575214981842483751)
      ·
        refine ⟨24353322862822472763725627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235548575214981842483751 24353322862822472763725627)
        ·
          refine ⟨36529984294233709145588441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24353322862822472763725627 36529984294233709145588441)
          ·
            refine ⟨27397488220675281859191331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36529984294233709145588441 27397488220675281859191331)
            ·
              refine ⟨41096232331012922788786997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27397488220675281859191331 41096232331012922788786997)
              ·
                refine ⟨3852771781032461511448781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41096232331012922788786997 3852771781032461511448781)
                ·
                  refine ⟨1444789417887173066793293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3852771781032461511448781 1444789417887173066793293)
                  ·
                    refine ⟨541796031707689900047485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444789417887173066793293 541796031707689900047485)
                    ·
                      rfl

theorem cell22_1582716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1582716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582716 prefixEnd_1582716 := by exact prefixLift 1582716
  have htrace : WordTrace (prefixWord ++ tailWord_1582716) baseStart_1582716 baseEnd_1582716 := by
    simpa [prefixWord, tailWord_1582716, baseEnd_1582716] using wordTrace_append hprefix tailTrace_1582716
  have hstable : (prefixWord ++ tailWord_1582716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582716).length < 2 ^ (prefixWord ++ tailWord_1582716).sum := by decide
  have hdescent : baseEnd_1582716 < baseStart_1582716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582855 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1582855 : Nat := 118140960795 + 1582855 * 2 ^ 59
def prefixEnd_1582855 : Nat := 4983230072969 + 3 ^ 40 * 1582855 * 2
def baseEnd_1582855 : Nat := 541843614248339870822059

theorem tailTrace_1582855 : CollatzResearch.WordTrace tailWord_1582855 prefixEnd_1582855 541843614248339870822059 := by
  unfold tailWord_1582855
  simp only [CollatzResearch.WordTrace]
  refine ⟨57731464680594139957030019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38487643120396093304686679 57731464680594139957030019)
  ·
    refine ⟨86597197020891209935545029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57731464680594139957030019 86597197020891209935545029)
    ·
      refine ⟨16236974441417101862914693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86597197020891209935545029 16236974441417101862914693)
      ·
        refine ⟨3044432707765706599296505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16236974441417101862914693 3044432707765706599296505)
        ·
          refine ⟨2283324530824279949472379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044432707765706599296505 2283324530824279949472379)
          ·
            refine ⟨3424986796236419924208569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283324530824279949472379 3424986796236419924208569)
            ·
              refine ⟨2568740097177314943156427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424986796236419924208569 2568740097177314943156427)
              ·
                refine ⟨3853110145765972414734641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568740097177314943156427 3853110145765972414734641)
                ·
                  refine ⟨2889832609324479311050981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853110145765972414734641 2889832609324479311050981)
                  ·
                    refine ⟨541843614248339870822059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2889832609324479311050981 541843614248339870822059)
                    ·
                      rfl

theorem cell22_1582855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1582855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582855 prefixEnd_1582855 := by exact prefixLift 1582855
  have htrace : WordTrace (prefixWord ++ tailWord_1582855) baseStart_1582855 baseEnd_1582855 := by
    simpa [prefixWord, tailWord_1582855, baseEnd_1582855] using wordTrace_append hprefix tailTrace_1582855
  have hstable : (prefixWord ++ tailWord_1582855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582855).length < 2 ^ (prefixWord ++ tailWord_1582855).sum := by decide
  have hdescent : baseEnd_1582855 < baseStart_1582855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582898 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1582898 : Nat := 118140960795 + 1582898 * 2 ^ 59
def prefixEnd_1582898 : Nat := 4983230072969 + 3 ^ 40 * 1582898 * 2
def baseEnd_1582898 : Nat := 180619444675700697332309

theorem tailTrace_1582898 : CollatzResearch.WordTrace tailWord_1582898 prefixEnd_1582898 180619444675700697332309 := by
  unfold tailWord_1582898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433258254859589575211337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38488688679625572200563565 14433258254859589575211337)
  ·
    refine ⟨10824943691144692181408503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14433258254859589575211337 10824943691144692181408503)
    ·
      refine ⟨16237415536717038272112755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10824943691144692181408503 16237415536717038272112755)
      ·
        refine ⟨24356123305075557408169133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16237415536717038272112755 24356123305075557408169133)
        ·
          refine ⟨9133546239403334028063425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24356123305075557408169133 9133546239403334028063425)
          ·
            refine ⟨6850159679552500521047569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9133546239403334028063425 6850159679552500521047569)
            ·
              refine ⟨5137619759664375390785677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850159679552500521047569 5137619759664375390785677)
              ·
                refine ⟨1926607409874140771544629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5137619759664375390785677 1926607409874140771544629)
                ·
                  refine ⟨180619444675700697332309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1926607409874140771544629 180619444675700697332309)
                  ·
                    rfl

theorem cell22_1582898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1582898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582898 prefixEnd_1582898 := by exact prefixLift 1582898
  have htrace : WordTrace (prefixWord ++ tailWord_1582898) baseStart_1582898 baseEnd_1582898 := by
    simpa [prefixWord, tailWord_1582898, baseEnd_1582898] using wordTrace_append hprefix tailTrace_1582898
  have hstable : (prefixWord ++ tailWord_1582898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582898).length < 2 ^ (prefixWord ++ tailWord_1582898).sum := by decide
  have hdescent : baseEnd_1582898 < baseStart_1582898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582902 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1582902 : Nat := 118140960795 + 1582902 * 2 ^ 59
def prefixEnd_1582902 : Nat := 4983230072969 + 3 ^ 40 * 1582902 * 2
def baseEnd_1582902 : Nat := 541859703308847414896915

theorem tailTrace_1582902 : CollatzResearch.WordTrace tailWord_1582902 prefixEnd_1582902 541859703308847414896915 := by
  unfold tailWord_1582902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608323681963991686499435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38488785940949244655993973 3608323681963991686499435)
  ·
    refine ⟨5412485522945987529749153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608323681963991686499435 5412485522945987529749153)
    ·
      refine ⟨4059364142209490647311865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412485522945987529749153 4059364142209490647311865)
      ·
        refine ⟨3044523106657117985483899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059364142209490647311865 3044523106657117985483899)
        ·
          refine ⟨4566784659985676978225849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044523106657117985483899 4566784659985676978225849)
          ·
            refine ⟨3425088494989257733669387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566784659985676978225849 3425088494989257733669387)
            ·
              refine ⟨5137632742483886600504081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425088494989257733669387 5137632742483886600504081)
              ·
                refine ⟨3853224556862914950378061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5137632742483886600504081 3853224556862914950378061)
                ·
                  refine ⟨1444959208823593106391773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3853224556862914950378061 1444959208823593106391773)
                  ·
                    refine ⟨541859703308847414896915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444959208823593106391773 541859703308847414896915)
                    ·
                      rfl

theorem cell22_1582902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1582902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582902 prefixEnd_1582902 := by exact prefixLift 1582902
  have htrace : WordTrace (prefixWord ++ tailWord_1582902) baseStart_1582902 baseEnd_1582902 := by
    simpa [prefixWord, tailWord_1582902, baseEnd_1582902] using wordTrace_append hprefix tailTrace_1582902
  have hstable : (prefixWord ++ tailWord_1582902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582902).length < 2 ^ (prefixWord ++ tailWord_1582902).sum := by decide
  have hdescent : baseEnd_1582902 < baseStart_1582902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582943 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 6]
def baseStart_1582943 : Nat := 118140960795 + 1582943 * 2 ^ 59
def prefixEnd_1582943 : Nat := 4983230072969 + 3 ^ 40 * 1582943 * 2
def baseEnd_1582943 : Nat := 180624579482245658207263

theorem tailTrace_1582943 : CollatzResearch.WordTrace tailWord_1582943 prefixEnd_1582943 180624579482245658207263 := by
  unfold tailWord_1582943
  simp only [CollatzResearch.WordTrace]
  refine ⟨57734674304275330986233483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38489782869516887324155655 57734674304275330986233483)
  ·
    refine ⟨86602011456412996479350225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57734674304275330986233483 86602011456412996479350225)
    ·
      refine ⟨64951508592309747359512669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86602011456412996479350225 64951508592309747359512669)
      ·
        refine ⟨24356815722116155259817251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64951508592309747359512669 24356815722116155259817251)
        ·
          refine ⟨36535223583174232889725877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24356815722116155259817251 36535223583174232889725877)
          ·
            refine ⟨3425177210922584333411801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36535223583174232889725877 3425177210922584333411801)
            ·
              refine ⟨2568882908191938250058851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425177210922584333411801 2568882908191938250058851)
              ·
                refine ⟨3853324362287907375088277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568882908191938250058851 3853324362287907375088277)
                ·
                  refine ⟨180624579482245658207263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3853324362287907375088277 180624579482245658207263)
                  ·
                    rfl

theorem cell22_1582943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_1582943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582943 prefixEnd_1582943 := by exact prefixLift 1582943
  have htrace : WordTrace (prefixWord ++ tailWord_1582943) baseStart_1582943 baseEnd_1582943 := by
    simpa [prefixWord, tailWord_1582943, baseEnd_1582943] using wordTrace_append hprefix tailTrace_1582943
  have hstable : (prefixWord ++ tailWord_1582943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582943).length < 2 ^ (prefixWord ++ tailWord_1582943).sum := by decide
  have hdescent : baseEnd_1582943 < baseStart_1582943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582973 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1582973 : Nat := 118140960795 + 1582973 * 2 ^ 59
def prefixEnd_1582973 : Nat := 4983230072969 + 3 ^ 40 * 1582973 * 2
def baseEnd_1582973 : Nat := 541884008059826896371697

theorem tailTrace_1582973 : CollatzResearch.WordTrace tailWord_1582973 prefixEnd_1582973 541884008059826896371697 := by
  unfold tailWord_1582973
  simp only [CollatzResearch.WordTrace]
  refine ⟨57735768494166646109825573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38490512329444430739883715 57735768494166646109825573)
  ·
    refine ⟨10825456592656246145592295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57735768494166646109825573 10825456592656246145592295)
    ·
      refine ⟨16238184888984369218388443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825456592656246145592295 16238184888984369218388443)
      ·
        refine ⟨24357277333476553827582665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238184888984369218388443 24357277333476553827582665)
        ·
          refine ⟨18267958000107415370686999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24357277333476553827582665 18267958000107415370686999)
          ·
            refine ⟨27401937000161123056030499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18267958000107415370686999 27401937000161123056030499)
            ·
              refine ⟨41102905500241684584045749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27401937000161123056030499 41102905500241684584045749)
              ·
                refine ⟨3853397390647657929754289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41102905500241684584045749 3853397390647657929754289)
                ·
                  refine ⟨2890048042985743447315717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3853397390647657929754289 2890048042985743447315717)
                  ·
                    refine ⟨541884008059826896371697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890048042985743447315717 541884008059826896371697)
                    ·
                      rfl

theorem cell22_1582973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1582973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582973 prefixEnd_1582973 := by exact prefixLift 1582973
  have htrace : WordTrace (prefixWord ++ tailWord_1582973) baseStart_1582973 baseEnd_1582973 := by
    simpa [prefixWord, tailWord_1582973, baseEnd_1582973] using wordTrace_append hprefix tailTrace_1582973
  have hstable : (prefixWord ++ tailWord_1582973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582973).length < 2 ^ (prefixWord ++ tailWord_1582973).sum := by decide
  have hdescent : baseEnd_1582973 < baseStart_1582973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582994 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1582994 : Nat := 118140960795 + 1582994 * 2 ^ 59
def prefixEnd_1582994 : Nat := 4983230072969 + 3 ^ 40 * 1582994 * 2
def baseEnd_1582994 : Nat := 180630398929663280532211

theorem tailTrace_1582994 : CollatzResearch.WordTrace tailWord_1582994 prefixEnd_1582994 180630398929663280532211 := by
  unfold tailWord_1582994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434133606772641674085009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38491022951393711130893357 14434133606772641674085009)
  ·
    refine ⟨10825600205079481255563757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14434133606772641674085009 10825600205079481255563757)
    ·
      refine ⟨4059600076904805470836409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10825600205079481255563757 4059600076904805470836409)
      ·
        refine ⟨3044700057678604103127307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059600076904805470836409 3044700057678604103127307)
        ·
          refine ⟨4567050086517906154690961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044700057678604103127307 4567050086517906154690961)
          ·
            refine ⟨3425287564888429616018221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567050086517906154690961 3425287564888429616018221)
            ·
              refine ⟨1284482836833161106006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3425287564888429616018221 1284482836833161106006833)
              ·
                refine ⟨963362127624870829505125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284482836833161106006833 963362127624870829505125)
                ·
                  refine ⟨180630398929663280532211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963362127624870829505125 180630398929663280532211)
                  ·
                    rfl

theorem cell22_1582994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1582994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1582994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1582994 prefixEnd_1582994 := by exact prefixLift 1582994
  have htrace : WordTrace (prefixWord ++ tailWord_1582994) baseStart_1582994 baseEnd_1582994 := by
    simpa [prefixWord, tailWord_1582994, baseEnd_1582994] using wordTrace_append hprefix tailTrace_1582994
  have hstable : (prefixWord ++ tailWord_1582994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582994).length < 2 ^ (prefixWord ++ tailWord_1582994).sum := by decide
  have hdescent : baseEnd_1582994 < baseStart_1582994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583063 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1583063 : Nat := 118140960795 + 1583063 * 2 ^ 59
def prefixEnd_1583063 : Nat := 4983230072969 + 3 ^ 40 * 1583063 * 2
def baseEnd_1583063 : Nat := 541914816899096661621421

theorem tailTrace_1583063 : CollatzResearch.WordTrace tailWord_1583063 prefixEnd_1583063 541914816899096661621421 := by
  unfold tailWord_1583063
  simp only [CollatzResearch.WordTrace]
  refine ⟨57739051063840591480601843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492700709227060987067895 57739051063840591480601843)
  ·
    refine ⟨86608576595760887220902765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57739051063840591480601843 86608576595760887220902765)
    ·
      refine ⟨32478216223410332707838537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86608576595760887220902765 32478216223410332707838537)
      ·
        refine ⟨24358662167557749530878903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32478216223410332707838537 24358662167557749530878903)
        ·
          refine ⟨36537993251336624296318355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24358662167557749530878903 36537993251336624296318355)
          ·
            refine ⟨54806989877004936444477533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36537993251336624296318355 54806989877004936444477533)
            ·
              refine ⟨20552621203876851166679075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54806989877004936444477533 20552621203876851166679075)
              ·
                refine ⟨30828931805815276750018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20552621203876851166679075 30828931805815276750018613)
                ·
                  refine ⟨2890212356795182195314245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30828931805815276750018613 2890212356795182195314245)
                  ·
                    refine ⟨541914816899096661621421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890212356795182195314245 541914816899096661621421)
                    ·
                      rfl

theorem cell22_1583063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1583063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583063 prefixEnd_1583063 := by exact prefixLift 1583063
  have htrace : WordTrace (prefixWord ++ tailWord_1583063) baseStart_1583063 baseEnd_1583063 := by
    simpa [prefixWord, tailWord_1583063, baseEnd_1583063] using wordTrace_append hprefix tailTrace_1583063
  have hstable : (prefixWord ++ tailWord_1583063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583063).length < 2 ^ (prefixWord ++ tailWord_1583063).sum := by decide
  have hdescent : baseEnd_1583063 < baseStart_1583063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583065 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_1583065 : Nat := 118140960795 + 1583065 * 2 ^ 59
def prefixEnd_1583065 : Nat := 4983230072969 + 3 ^ 40 * 1583065 * 2
def baseEnd_1583065 : Nat := 541915501539969323071415

theorem tailTrace_1583065 : CollatzResearch.WordTrace tailWord_1583065 prefixEnd_1583065 541915501539969323071415 := by
  unfold tailWord_1583065
  simp only [CollatzResearch.WordTrace]
  refine ⟨57739124009833345822174649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38492749339888897214783099 57739124009833345822174649)
  ·
    refine ⟨43304343007375009366630987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57739124009833345822174649 43304343007375009366630987)
    ·
      refine ⟨64956514511062514049946481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43304343007375009366630987 64956514511062514049946481)
      ·
        refine ⟨48717385883296885537459861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64956514511062514049946481 48717385883296885537459861)
        ·
          refine ⟨2283627463279541509568431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48717385883296885537459861 2283627463279541509568431)
          ·
            refine ⟨3425441194919312264352647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283627463279541509568431 3425441194919312264352647)
            ·
              refine ⟨5138161792378968396528971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425441194919312264352647 5138161792378968396528971)
              ·
                refine ⟨7707242688568452594793457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5138161792378968396528971 7707242688568452594793457)
                ·
                  refine ⟨5780432016426339446095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7707242688568452594793457 5780432016426339446095093)
                  ·
                    refine ⟨541915501539969323071415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5780432016426339446095093 541915501539969323071415)
                    ·
                      rfl

theorem cell22_1583065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_1583065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583065 prefixEnd_1583065 := by exact prefixLift 1583065
  have htrace : WordTrace (prefixWord ++ tailWord_1583065) baseStart_1583065 baseEnd_1583065 := by
    simpa [prefixWord, tailWord_1583065, baseEnd_1583065] using wordTrace_append hprefix tailTrace_1583065
  have hstable : (prefixWord ++ tailWord_1583065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583065).length < 2 ^ (prefixWord ++ tailWord_1583065).sum := by decide
  have hdescent : baseEnd_1583065 < baseStart_1583065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583080 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1583080 : Nat := 118140960795 + 1583080 * 2 ^ 59
def prefixEnd_1583080 : Nat := 4983230072969 + 3 ^ 40 * 1583080 * 2
def baseEnd_1583080 : Nat := 541920636346514283946369

theorem tailTrace_1583080 : CollatzResearch.WordTrace tailWord_1583080 prefixEnd_1583080 541920636346514283946369 := by
  unfold tailWord_1583080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28869835552389501691985347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38493114069852668922647129 28869835552389501691985347)
  ·
    refine ⟨43304753328584252537978021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28869835552389501691985347 43304753328584252537978021)
    ·
      refine ⟨8119641249109547350870879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43304753328584252537978021 8119641249109547350870879)
      ·
        refine ⟨12179461873664321026306319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119641249109547350870879 12179461873664321026306319)
        ·
          refine ⟨18269192810496481539459479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12179461873664321026306319 18269192810496481539459479)
          ·
            refine ⟨27403789215744722309189219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18269192810496481539459479 27403789215744722309189219)
            ·
              refine ⟨41105683823617083463783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27403789215744722309189219 41105683823617083463783829)
              ·
                refine ⟨1926828929232050787364867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41105683823617083463783829 1926828929232050787364867)
                ·
                  refine ⟨2890243393848076181047301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926828929232050787364867 2890243393848076181047301)
                  ·
                    refine ⟨541920636346514283946369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890243393848076181047301 541920636346514283946369)
                    ·
                      rfl

theorem cell22_1583080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1583080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583080 prefixEnd_1583080 := by exact prefixLift 1583080
  have htrace : WordTrace (prefixWord ++ tailWord_1583080) baseStart_1583080 baseEnd_1583080 := by
    simpa [prefixWord, tailWord_1583080, baseEnd_1583080] using wordTrace_append hprefix tailTrace_1583080
  have hstable : (prefixWord ++ tailWord_1583080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583080).length < 2 ^ (prefixWord ++ tailWord_1583080).sum := by decide
  have hdescent : baseEnd_1583080 < baseStart_1583080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583097 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_1583097 : Nat := 118140960795 + 1583097 * 2 ^ 59
def prefixEnd_1583097 : Nat := 4983230072969 + 3 ^ 40 * 1583097 * 2
def baseEnd_1583097 : Nat := 541926455793931906271317

theorem tailTrace_1583097 : CollatzResearch.WordTrace tailWord_1583097 prefixEnd_1583097 541926455793931906271317 := by
  unfold tailWord_1583097
  simp only [CollatzResearch.WordTrace]
  refine ⟨57740291145717415287339545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38493527430478276858226363 57740291145717415287339545)
  ·
    refine ⟨43305218359288061465504659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57740291145717415287339545 43305218359288061465504659)
    ·
      refine ⟨64957827538932092198256989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43305218359288061465504659 64957827538932092198256989)
      ·
        refine ⟨24359185327099534574346371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64957827538932092198256989 24359185327099534574346371)
        ·
          refine ⟨36538777990649301861519557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24359185327099534574346371 36538777990649301861519557)
          ·
            refine ⟨6851020873246744099034917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36538777990649301861519557 6851020873246744099034917)
            ·
              refine ⟨1284566413733764518569047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6851020873246744099034917 1284566413733764518569047)
              ·
                refine ⟨1926849620600646777853571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284566413733764518569047 1926849620600646777853571)
                ·
                  refine ⟨2890274430900970166780357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926849620600646777853571 2890274430900970166780357)
                  ·
                    refine ⟨541926455793931906271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890274430900970166780357 541926455793931906271317)
                    ·
                      rfl

theorem cell22_1583097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_1583097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583097 prefixEnd_1583097 := by exact prefixLift 1583097
  have htrace : WordTrace (prefixWord ++ tailWord_1583097) baseStart_1583097 baseEnd_1583097 := by
    simpa [prefixWord, tailWord_1583097, baseEnd_1583097] using wordTrace_append hprefix tailTrace_1583097
  have hstable : (prefixWord ++ tailWord_1583097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583097).length < 2 ^ (prefixWord ++ tailWord_1583097).sum := by decide
  have hdescent : baseEnd_1583097 < baseStart_1583097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583155 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 5, 3]
def baseStart_1583155 : Nat := 118140960795 + 1583155 * 2 ^ 59
def prefixEnd_1583155 : Nat := 4983230072969 + 3 ^ 40 * 1583155 * 2
def baseEnd_1583155 : Nat := 541946310379239088321139

theorem tailTrace_1583155 : CollatzResearch.WordTrace tailWord_1583155 prefixEnd_1583155 541946310379239088321139 := by
  unfold tailWord_1583155
  simp only [CollatzResearch.WordTrace]
  refine ⟨57742406579507291192950919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38494937719671527461967279 57742406579507291192950919)
  ·
    refine ⟨86613609869260936789426379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57742406579507291192950919 86613609869260936789426379)
    ·
      refine ⟨129920414803891405184139569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86613609869260936789426379 129920414803891405184139569)
      ·
        refine ⟨97440311102918553888104677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129920414803891405184139569 97440311102918553888104677)
        ·
          refine ⟨18270058331797228854019627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97440311102918553888104677 18270058331797228854019627)
          ·
            refine ⟨27405087497695843281029441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18270058331797228854019627 27405087497695843281029441)
            ·
              refine ⟨20553815623271882460772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27405087497695843281029441 20553815623271882460772081)
              ·
                refine ⟨15415361717453911845579061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20553815623271882460772081 15415361717453911845579061)
                ·
                  refine ⟨1445190161011304235523037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15415361717453911845579061 1445190161011304235523037)
                  ·
                    refine ⟨541946310379239088321139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445190161011304235523037 541946310379239088321139)
                    ·
                      rfl

theorem cell22_1583155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 3].length) (baseStart_1583155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583155 prefixEnd_1583155 := by exact prefixLift 1583155
  have htrace : WordTrace (prefixWord ++ tailWord_1583155) baseStart_1583155 baseEnd_1583155 := by
    simpa [prefixWord, tailWord_1583155, baseEnd_1583155] using wordTrace_append hprefix tailTrace_1583155
  have hstable : (prefixWord ++ tailWord_1583155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583155).length < 2 ^ (prefixWord ++ tailWord_1583155).sum := by decide
  have hdescent : baseEnd_1583155 < baseStart_1583155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583264 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_1583264 : Nat := 118140960795 + 1583264 * 2 ^ 59
def prefixEnd_1583264 : Nat := 4983230072969 + 3 ^ 40 * 1583264 * 2
def baseEnd_1583264 : Nat := 180661207768933045781935

theorem tailTrace_1583264 : CollatzResearch.WordTrace tailWord_1583264 prefixEnd_1583264 180661207768933045781935 := by
  unfold tailWord_1583264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873191068056201404334423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38497588090741601872445897 28873191068056201404334423)
  ·
    refine ⟨43309786602084302106501635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28873191068056201404334423 43309786602084302106501635)
    ·
      refine ⟨64964679903126453159752453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43309786602084302106501635 64964679903126453159752453)
      ·
        refine ⟨12180877481836209967453585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64964679903126453159752453 12180877481836209967453585)
        ·
          refine ⟨9135658111377157475590189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12180877481836209967453585 9135658111377157475590189)
          ·
            refine ⟨3425871791766434053346321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9135658111377157475590189 3425871791766434053346321)
            ·
              refine ⟨2569403843824825540009741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425871791766434053346321 2569403843824825540009741)
              ·
                refine ⟨963526441434309577503653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569403843824825540009741 963526441434309577503653)
                ·
                  refine ⟨180661207768933045781935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963526441434309577503653 180661207768933045781935)
                  ·
                    rfl

theorem cell22_1583264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_1583264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583264 prefixEnd_1583264 := by exact prefixLift 1583264
  have htrace : WordTrace (prefixWord ++ tailWord_1583264) baseStart_1583264 baseEnd_1583264 := by
    simpa [prefixWord, tailWord_1583264, baseEnd_1583264] using wordTrace_append hprefix tailTrace_1583264
  have hstable : (prefixWord ++ tailWord_1583264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583264).length < 2 ^ (prefixWord ++ tailWord_1583264).sum := by decide
  have hdescent : baseEnd_1583264 < baseStart_1583264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583266 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1583266 : Nat := 118140960795 + 1583266 * 2 ^ 59
def prefixEnd_1583266 : Nat := 4983230072969 + 3 ^ 40 * 1583266 * 2
def baseEnd_1583266 : Nat := 541984307947671798795799

theorem tailTrace_1583266 : CollatzResearch.WordTrace tailWord_1583266 prefixEnd_1583266 541984307947671798795799 := by
  unfold tailWord_1583266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436613770526289287560413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38497636721403438100161101 14436613770526289287560413)
  ·
    refine ⟨5413730163947358482835155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14436613770526289287560413 5413730163947358482835155)
    ·
      refine ⟨8120595245921037724252733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5413730163947358482835155 8120595245921037724252733)
      ·
        refine ⟨3045223217220389146594775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8120595245921037724252733 3045223217220389146594775)
        ·
          refine ⟨4567834825830583719892163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045223217220389146594775 4567834825830583719892163)
          ·
            refine ⟨6851752238745875579838245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567834825830583719892163 6851752238745875579838245)
            ·
              refine ⟨1284703544764851671219671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6851752238745875579838245 1284703544764851671219671)
              ·
                refine ⟨1927055317147277506829507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284703544764851671219671 1927055317147277506829507)
                ·
                  refine ⟨2890582975720916260244261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927055317147277506829507 2890582975720916260244261)
                  ·
                    refine ⟨541984307947671798795799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2890582975720916260244261 541984307947671798795799)
                    ·
                      rfl

theorem cell22_1583266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1583266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583266 prefixEnd_1583266 := by exact prefixLift 1583266
  have htrace : WordTrace (prefixWord ++ tailWord_1583266) baseStart_1583266 baseEnd_1583266 := by
    simpa [prefixWord, tailWord_1583266, baseEnd_1583266] using wordTrace_append hprefix tailTrace_1583266
  have hstable : (prefixWord ++ tailWord_1583266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583266).length < 2 ^ (prefixWord ++ tailWord_1583266).sum := by decide
  have hdescent : baseEnd_1583266 < baseStart_1583266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583296 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_1583296 : Nat := 118140960795 + 1583296 * 2 ^ 59
def prefixEnd_1583296 : Nat := 4983230072969 + 3 ^ 40 * 1583296 * 2
def baseEnd_1583296 : Nat := 541994577560761720545707

theorem tailTrace_1583296 : CollatzResearch.WordTrace tailWord_1583296 prefixEnd_1583296 541994577560761720545707 := by
  unfold tailWord_1583296
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873774635998236136916871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38498366181330981515889161 28873774635998236136916871)
  ·
    refine ⟨43310661953997354205375307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28873774635998236136916871 43310661953997354205375307)
    ·
      refine ⟨64965992930996031308062961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43310661953997354205375307 64965992930996031308062961)
      ·
        refine ⟨48724494698247023481047221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64965992930996031308062961 48724494698247023481047221)
        ·
          refine ⟨4567921377960658451348177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48724494698247023481047221 4567921377960658451348177)
          ·
            refine ⟨3425941033470493838511133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567921377960658451348177 3425941033470493838511133)
            ·
              refine ⟨1284727887551435189441675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3425941033470493838511133 1284727887551435189441675)
              ·
                refine ⟨1927091831327152784162513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284727887551435189441675 1927091831327152784162513)
                ·
                  refine ⟨1445318873495364588121885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927091831327152784162513 1445318873495364588121885)
                  ·
                    refine ⟨541994577560761720545707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445318873495364588121885 541994577560761720545707)
                    ·
                      rfl

theorem cell22_1583296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_1583296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583296 prefixEnd_1583296 := by exact prefixLift 1583296
  have htrace : WordTrace (prefixWord ++ tailWord_1583296) baseStart_1583296 baseEnd_1583296 := by
    simpa [prefixWord, tailWord_1583296, baseEnd_1583296] using wordTrace_append hprefix tailTrace_1583296
  have hstable : (prefixWord ++ tailWord_1583296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583296).length < 2 ^ (prefixWord ++ tailWord_1583296).sum := by decide
  have hdescent : baseEnd_1583296 < baseStart_1583296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583307 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 3, 3]
def baseStart_1583307 : Nat := 118140960795 + 1583307 * 2 ^ 59
def prefixEnd_1583307 : Nat := 4983230072969 + 3 ^ 40 * 1583307 * 2
def baseEnd_1583307 : Nat := 541998343085561358520673

theorem tailTrace_1583307 : CollatzResearch.WordTrace tailWord_1583307 prefixEnd_1583307 541998343085561358520673 := by
  unfold tailWord_1583307
  simp only [CollatzResearch.WordTrace]
  refine ⟨57747950474956621152484175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38498633649971080768322783 57747950474956621152484175)
  ·
    refine ⟨86621925712434931728726263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57747950474956621152484175 86621925712434931728726263)
    ·
      refine ⟨129932888568652397593089395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86621925712434931728726263 129932888568652397593089395)
      ·
        refine ⟨194899332852978596389634093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129932888568652397593089395 194899332852978596389634093)
        ·
          refine ⟨73087249819866973646112785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194899332852978596389634093 73087249819866973646112785)
          ·
            refine ⟨54815437364900230234584589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73087249819866973646112785 54815437364900230234584589)
            ·
              refine ⟨20555789011837586337969221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54815437364900230234584589 20555789011837586337969221)
              ·
                refine ⟨3854210439719547438369229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20555789011837586337969221 3854210439719547438369229)
                ·
                  refine ⟨1445328914894830289388461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3854210439719547438369229 1445328914894830289388461)
                  ·
                    refine ⟨541998343085561358520673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445328914894830289388461 541998343085561358520673)
                    ·
                      rfl

theorem cell22_1583307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].length) (baseStart_1583307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583307 prefixEnd_1583307 := by exact prefixLift 1583307
  have htrace : WordTrace (prefixWord ++ tailWord_1583307) baseStart_1583307 baseEnd_1583307 := by
    simpa [prefixWord, tailWord_1583307, baseEnd_1583307] using wordTrace_append hprefix tailTrace_1583307
  have hstable : (prefixWord ++ tailWord_1583307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583307).length < 2 ^ (prefixWord ++ tailWord_1583307).sum := by decide
  have hdescent : baseEnd_1583307 < baseStart_1583307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583354 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_1583354 : Nat := 118140960795 + 1583354 * 2 ^ 59
def prefixEnd_1583354 : Nat := 4983230072969 + 3 ^ 40 * 1583354 * 2
def baseEnd_1583354 : Nat := 180671477382022967531843

theorem tailTrace_1583354 : CollatzResearch.WordTrace tailWord_1583354 prefixEnd_1583354 180671477382022967531843 := by
  unfold tailWord_1583354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437416176446587044861279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38499776470524232119630077 14437416176446587044861279)
  ·
    refine ⟨21656124264669880567291919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437416176446587044861279 21656124264669880567291919)
    ·
      refine ⟨32484186397004820850937879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21656124264669880567291919 32484186397004820850937879)
      ·
        refine ⟨48726279595507231276406819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32484186397004820850937879 48726279595507231276406819)
        ·
          refine ⟨73089419393260846914610229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48726279595507231276406819 73089419393260846914610229)
          ·
            refine ⟨6852133068118204398244709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73089419393260846914610229 6852133068118204398244709)
            ·
              refine ⟨1284774950272163324670883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6852133068118204398244709 1284774950272163324670883)
              ·
                refine ⟨1927162425408244987006325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284774950272163324670883 1927162425408244987006325)
                ·
                  refine ⟨180671477382022967531843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1927162425408244987006325 180671477382022967531843)
                  ·
                    rfl

theorem cell22_1583354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_1583354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583354 prefixEnd_1583354 := by exact prefixLift 1583354
  have htrace : WordTrace (prefixWord ++ tailWord_1583354) baseStart_1583354 baseEnd_1583354 := by
    simpa [prefixWord, tailWord_1583354, baseEnd_1583354] using wordTrace_append hprefix tailTrace_1583354
  have hstable : (prefixWord ++ tailWord_1583354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583354).length < 2 ^ (prefixWord ++ tailWord_1583354).sum := by decide
  have hdescent : baseEnd_1583354 < baseStart_1583354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583489 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 7]
def baseStart_1583489 : Nat := 118140960795 + 1583489 * 2 ^ 59
def prefixEnd_1583489 : Nat := 4983230072969 + 3 ^ 40 * 1583489 * 2
def baseEnd_1583489 : Nat := 180686881801657850156705

theorem tailTrace_1583489 : CollatzResearch.WordTrace tailWord_1583489 prefixEnd_1583489 180686881801657850156705 := by
  unfold tailWord_1583489
  simp only [CollatzResearch.WordTrace]
  refine ⟨57754588560297266235609521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38503059040198177490406347 57754588560297266235609521)
  ·
    refine ⟨43315941420222949676707141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57754588560297266235609521 43315941420222949676707141)
    ·
      refine ⟨8121739016291803064382589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43315941420222949676707141 8121739016291803064382589)
      ·
        refine ⟨3045652131109426149143471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8121739016291803064382589 3045652131109426149143471)
        ·
          refine ⟨4568478196664139223715207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045652131109426149143471 4568478196664139223715207)
          ·
            refine ⟨6852717294996208835572811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568478196664139223715207 6852717294996208835572811)
            ·
              refine ⟨10279075942494313253359217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852717294996208835572811 10279075942494313253359217)
              ·
                refine ⟨7709306956870734940019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10279075942494313253359217 7709306956870734940019413)
                ·
                  refine ⟨180686881801657850156705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7709306956870734940019413 180686881801657850156705)
                  ·
                    rfl

theorem cell22_1583489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_1583489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583489 prefixEnd_1583489 := by exact prefixLift 1583489
  have htrace : WordTrace (prefixWord ++ tailWord_1583489) baseStart_1583489 baseEnd_1583489 := by
    simpa [prefixWord, tailWord_1583489, baseEnd_1583489] using wordTrace_append hprefix tailTrace_1583489
  have hstable : (prefixWord ++ tailWord_1583489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583489).length < 2 ^ (prefixWord ++ tailWord_1583489).sum := by decide
  have hdescent : baseEnd_1583489 < baseStart_1583489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583519 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1583519 : Nat := 118140960795 + 1583519 * 2 ^ 59
def prefixEnd_1583519 : Nat := 4983230072969 + 3 ^ 40 * 1583519 * 2
def baseEnd_1583519 : Nat := 542070915018063472220023

theorem tailTrace_1583519 : CollatzResearch.WordTrace tailWord_1583519 prefixEnd_1583519 542070915018063472220023 := by
  unfold tailWord_1583519
  simp only [CollatzResearch.WordTrace]
  refine ⟨57755682750188581359201611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38503788500125720906134407 57755682750188581359201611)
  ·
    refine ⟨86633524125282872038802417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57755682750188581359201611 86633524125282872038802417)
    ·
      refine ⟨64975143093962154029101813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86633524125282872038802417 64975143093962154029101813)
      ·
        refine ⟨6091419665058951940228295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64975143093962154029101813 6091419665058951940228295)
        ·
          refine ⟨9137129497588427910342443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091419665058951940228295 9137129497588427910342443)
          ·
            refine ⟨13705694246382641865513665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137129497588427910342443 13705694246382641865513665)
            ·
              refine ⟨10279270684786981399135249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13705694246382641865513665 10279270684786981399135249)
              ·
                refine ⟨7709453013590236049351437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10279270684786981399135249 7709453013590236049351437)
                ·
                  refine ⟨2891044880096338518506789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7709453013590236049351437 2891044880096338518506789)
                  ·
                    refine ⟨542070915018063472220023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891044880096338518506789 542070915018063472220023)
                    ·
                      rfl

theorem cell22_1583519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1583519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583519 prefixEnd_1583519 := by exact prefixLift 1583519
  have htrace : WordTrace (prefixWord ++ tailWord_1583519) baseStart_1583519 baseEnd_1583519 := by
    simpa [prefixWord, tailWord_1583519, baseEnd_1583519] using wordTrace_append hprefix tailTrace_1583519
  have hstable : (prefixWord ++ tailWord_1583519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583519).length < 2 ^ (prefixWord ++ tailWord_1583519).sum := by decide
  have hdescent : baseEnd_1583519 < baseStart_1583519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583549 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1583549 : Nat := 118140960795 + 1583549 * 2 ^ 59
def prefixEnd_1583549 : Nat := 4983230072969 + 3 ^ 40 * 1583549 * 2
def baseEnd_1583549 : Nat := 542081184631153393969931

theorem tailTrace_1583549 : CollatzResearch.WordTrace tailWord_1583549 prefixEnd_1583549 542081184631153393969931 := by
  unfold tailWord_1583549
  simp only [CollatzResearch.WordTrace]
  refine ⟨57756776940079896482793701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38504517960053264321862467 57756776940079896482793701)
  ·
    refine ⟨10829395676264980590523819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57756776940079896482793701 10829395676264980590523819)
    ·
      refine ⟨16244093514397470885785729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10829395676264980590523819 16244093514397470885785729)
      ·
        refine ⟨12183070135798103164339297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16244093514397470885785729 12183070135798103164339297)
        ·
          refine ⟨9137302601848577373254473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183070135798103164339297 9137302601848577373254473)
          ·
            refine ⟨6852976951386433029940855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9137302601848577373254473 6852976951386433029940855)
            ·
              refine ⟨10279465427079649544911283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852976951386433029940855 10279465427079649544911283)
              ·
                refine ⟨15419198140619474317366925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10279465427079649544911283 15419198140619474317366925)
                ·
                  refine ⟨5782199302732302869012597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15419198140619474317366925 5782199302732302869012597)
                  ·
                    refine ⟨542081184631153393969931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5782199302732302869012597 542081184631153393969931)
                    ·
                      rfl

theorem cell22_1583549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1583549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583549 prefixEnd_1583549 := by exact prefixLift 1583549
  have htrace : WordTrace (prefixWord ++ tailWord_1583549) baseStart_1583549 baseEnd_1583549 := by
    simpa [prefixWord, tailWord_1583549, baseEnd_1583549] using wordTrace_append hprefix tailTrace_1583549
  have hstable : (prefixWord ++ tailWord_1583549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583549).length < 2 ^ (prefixWord ++ tailWord_1583549).sum := by decide
  have hdescent : baseEnd_1583549 < baseStart_1583549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583598 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1583598 : Nat := 118140960795 + 1583598 * 2 ^ 59
def prefixEnd_1583598 : Nat := 4983230072969 + 3 ^ 40 * 1583598 * 2
def baseEnd_1583598 : Nat := 542097958332533599494781

theorem tailTrace_1583598 : CollatzResearch.WordTrace tailWord_1583598 prefixEnd_1583598 542097958332533599494781 := by
  unfold tailWord_1583598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219820514612797231415931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38505709411268251900884965 7219820514612797231415931)
  ·
    refine ⟨10829730771919195847123897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219820514612797231415931 10829730771919195847123897)
    ·
      refine ⟨8122298078939396885342923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10829730771919195847123897 8122298078939396885342923)
      ·
        refine ⟨12183447118409095328014385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8122298078939396885342923 12183447118409095328014385)
        ·
          refine ⟨9137585338806821496010789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183447118409095328014385 9137585338806821496010789)
          ·
            refine ⟨1713297251026279030502023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9137585338806821496010789 1713297251026279030502023)
            ·
              refine ⟨2569945876539418545753035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713297251026279030502023 2569945876539418545753035)
              ·
                refine ⟨3854918814809127818629553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569945876539418545753035 3854918814809127818629553)
                ·
                  refine ⟨2891189111106845863972165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3854918814809127818629553 2891189111106845863972165)
                  ·
                    refine ⟨542097958332533599494781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891189111106845863972165 542097958332533599494781)
                    ·
                      rfl

theorem cell22_1583598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1583598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583598 prefixEnd_1583598 := by exact prefixLift 1583598
  have htrace : WordTrace (prefixWord ++ tailWord_1583598) baseStart_1583598 baseEnd_1583598 := by
    simpa [prefixWord, tailWord_1583598, baseEnd_1583598] using wordTrace_append hprefix tailTrace_1583598
  have hstable : (prefixWord ++ tailWord_1583598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583598).length < 2 ^ (prefixWord ++ tailWord_1583598).sum := by decide
  have hdescent : baseEnd_1583598 < baseStart_1583598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583628 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1583628 : Nat := 118140960795 + 1583628 * 2 ^ 59
def prefixEnd_1583628 : Nat := 4983230072969 + 3 ^ 40 * 1583628 * 2
def baseEnd_1583628 : Nat := 542108227945623521244689

theorem tailTrace_1583628 : CollatzResearch.WordTrace tailWord_1583628 prefixEnd_1583628 542108227945623521244689 := by
  unfold tailWord_1583628
  simp only [CollatzResearch.WordTrace]
  refine ⟨28879829153396846487459769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38506438871195795316613025 28879829153396846487459769)
  ·
    refine ⟨21659871865047634865594827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28879829153396846487459769 21659871865047634865594827)
    ·
      refine ⟨32489807797571452298392241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21659871865047634865594827 32489807797571452298392241)
      ·
        refine ⟨24367355848178589223794181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32489807797571452298392241 24367355848178589223794181)
        ·
          refine ⟨4568879221533485479461409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24367355848178589223794181 4568879221533485479461409)
          ·
            refine ⟨3426659416150114109596057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4568879221533485479461409 3426659416150114109596057)
            ·
              refine ⟨2569994562112585582197043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426659416150114109596057 2569994562112585582197043)
              ·
                refine ⟨3854991843168878373295565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2569994562112585582197043 3854991843168878373295565)
                ·
                  refine ⟨1445621941188329389985837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3854991843168878373295565 1445621941188329389985837)
                  ·
                    refine ⟨542108227945623521244689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445621941188329389985837 542108227945623521244689)
                    ·
                      rfl

theorem cell22_1583628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1583628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583628 prefixEnd_1583628 := by exact prefixLift 1583628
  have htrace : WordTrace (prefixWord ++ tailWord_1583628) baseStart_1583628 baseEnd_1583628 := by
    simpa [prefixWord, tailWord_1583628, baseEnd_1583628] using wordTrace_append hprefix tailTrace_1583628
  have hstable : (prefixWord ++ tailWord_1583628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583628).length < 2 ^ (prefixWord ++ tailWord_1583628).sum := by decide
  have hdescent : baseEnd_1583628 < baseStart_1583628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583671 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1583671 : Nat := 118140960795 + 1583671 * 2 ^ 59
def prefixEnd_1583671 : Nat := 4983230072969 + 3 ^ 40 * 1583671 * 2
def baseEnd_1583671 : Nat := 542122947724385742419557

theorem tailTrace_1583671 : CollatzResearch.WordTrace tailWord_1583671 prefixEnd_1583671 542122947724385742419557 := by
  unfold tailWord_1583671
  simp only [CollatzResearch.WordTrace]
  refine ⟨57761226645637911318734867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38507484430425274212489911 57761226645637911318734867)
  ·
    refine ⟨86641839968456866978102301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57761226645637911318734867 86641839968456866978102301)
    ·
      refine ⟨32490689988171325116788363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86641839968456866978102301 32490689988171325116788363)
      ·
        refine ⟨48736034982256987675182545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32490689988171325116788363 48736034982256987675182545)
        ·
          refine ⟨36552026236692740756386909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48736034982256987675182545 36552026236692740756386909)
          ·
            refine ⟨13707009838759777783645091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36552026236692740756386909 13707009838759777783645091)
            ·
              refine ⟨20560514758139666675467637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707009838759777783645091 20560514758139666675467637)
              ·
                refine ⟨1927548258575593750825091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20560514758139666675467637 1927548258575593750825091)
                ·
                  refine ⟨2891322387863390626237637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927548258575593750825091 2891322387863390626237637)
                  ·
                    refine ⟨542122947724385742419557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2891322387863390626237637 542122947724385742419557)
                    ·
                      rfl

theorem cell22_1583671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1583671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583671 prefixEnd_1583671 := by exact prefixLift 1583671
  have htrace : WordTrace (prefixWord ++ tailWord_1583671) baseStart_1583671 baseEnd_1583671 := by
    simpa [prefixWord, tailWord_1583671, baseEnd_1583671] using wordTrace_append hprefix tailTrace_1583671
  have hstable : (prefixWord ++ tailWord_1583671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583671).length < 2 ^ (prefixWord ++ tailWord_1583671).sum := by decide
  have hdescent : baseEnd_1583671 < baseStart_1583671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583748 : List Nat := [2, 3, 2, 1, 3, 3, 1, 7]
def baseStart_1583748 : Nat := 118140960795 + 1583748 * 2 ^ 59
def prefixEnd_1583748 : Nat := 4983230072969 + 3 ^ 40 * 1583748 * 2
def baseEnd_1583748 : Nat := 60238811821998134249369

theorem tailTrace_1583748 : CollatzResearch.WordTrace tailWord_1583748 prefixEnd_1583748 60238811821998134249369 := by
  unfold tailWord_1583748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882017533179476734643949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38509356710905968979525265 28882017533179476734643949)
  ·
    refine ⟨10830756574942303775491481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28882017533179476734643949 10830756574942303775491481)
    ·
      refine ⟨8123067431206727831618611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10830756574942303775491481 8123067431206727831618611)
      ·
        refine ⟨12184601146810091747427917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8123067431206727831618611 12184601146810091747427917)
        ·
          refine ⟨4569225430053784405285469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12184601146810091747427917 4569225430053784405285469)
          ·
            refine ⟨1713459536270169151982051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4569225430053784405285469 1713459536270169151982051)
            ·
              refine ⟨2570189304405253727973077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713459536270169151982051 2570189304405253727973077)
              ·
                refine ⟨60238811821998134249369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2570189304405253727973077 60238811821998134249369)
                ·
                  rfl

theorem cell22_1583748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_1583748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583748 prefixEnd_1583748 := by exact prefixLift 1583748
  have htrace : WordTrace (prefixWord ++ tailWord_1583748) baseStart_1583748 baseEnd_1583748 := by
    simpa [prefixWord, tailWord_1583748, baseEnd_1583748] using wordTrace_append hprefix tailTrace_1583748
  have hstable : (prefixWord ++ tailWord_1583748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583748).length < 2 ^ (prefixWord ++ tailWord_1583748).sum := by decide
  have hdescent : baseEnd_1583748 < baseStart_1583748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583786 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1583786 : Nat := 118140960795 + 1583786 * 2 ^ 59
def prefixEnd_1583786 : Nat := 4983230072969 + 3 ^ 40 * 1583786 * 2
def baseEnd_1583786 : Nat := 542162314574563775794205

theorem tailTrace_1583786 : CollatzResearch.WordTrace tailWord_1583786 prefixEnd_1583786 542162314574563775794205 := by
  unfold tailWord_1583786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441355260055321489792803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38510280693480857306114141 14441355260055321489792803)
  ·
    refine ⟨21662032890082982234689205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14441355260055321489792803 21662032890082982234689205)
    ·
      refine ⟨2030815583445279584502113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21662032890082982234689205 2030815583445279584502113)
      ·
        refine ⟨1523111687583959688376585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2030815583445279584502113 1523111687583959688376585)
        ·
          refine ⟨1142333765687969766282439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523111687583959688376585 1142333765687969766282439)
          ·
            refine ⟨1713500648531954649423659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142333765687969766282439 1713500648531954649423659)
            ·
              refine ⟨2570250972797931974135489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713500648531954649423659 2570250972797931974135489)
              ·
                refine ⟨1927688229598448980601617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570250972797931974135489 1927688229598448980601617)
                ·
                  refine ⟨1445766172198836735451213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927688229598448980601617 1445766172198836735451213)
                  ·
                    refine ⟨542162314574563775794205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445766172198836735451213 542162314574563775794205)
                    ·
                      rfl

theorem cell22_1583786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1583786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583786 prefixEnd_1583786 := by exact prefixLift 1583786
  have htrace : WordTrace (prefixWord ++ tailWord_1583786) baseStart_1583786 baseEnd_1583786 := by
    simpa [prefixWord, tailWord_1583786, baseEnd_1583786] using wordTrace_append hprefix tailTrace_1583786
  have hstable : (prefixWord ++ tailWord_1583786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583786).length < 2 ^ (prefixWord ++ tailWord_1583786).sum := by decide
  have hdescent : baseEnd_1583786 < baseStart_1583786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583791 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1583791 : Nat := 118140960795 + 1583791 * 2 ^ 59
def prefixEnd_1583791 : Nat := 4983230072969 + 3 ^ 40 * 1583791 * 2
def baseEnd_1583791 : Nat := 542164026176745429419189

theorem tailTrace_1583791 : CollatzResearch.WordTrace tailWord_1583791 prefixEnd_1583791 542164026176745429419189 := by
  unfold tailWord_1583791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57765603405203171813103227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38510402270135447875402151 57765603405203171813103227)
  ·
    refine ⟨86648405107804757719654841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57765603405203171813103227 86648405107804757719654841)
    ·
      refine ⟨64986303830853568289741131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86648405107804757719654841 64986303830853568289741131)
      ·
        refine ⟨97479455746280352434611697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64986303830853568289741131 97479455746280352434611697)
        ·
          refine ⟨73109591809710264325958773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97479455746280352434611697 73109591809710264325958773)
          ·
            refine ⟨6854024232160337280558635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73109591809710264325958773 6854024232160337280558635)
            ·
              refine ⟨10281036348240505920837953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854024232160337280558635 10281036348240505920837953)
              ·
                refine ⟨7710777261180379440628465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10281036348240505920837953 7710777261180379440628465)
                ·
                  refine ⟨5783082945885284580471349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7710777261180379440628465 5783082945885284580471349)
                  ·
                    refine ⟨542164026176745429419189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5783082945885284580471349 542164026176745429419189)
                    ·
                      rfl

theorem cell22_1583791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1583791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583791 prefixEnd_1583791 := by exact prefixLift 1583791
  have htrace : WordTrace (prefixWord ++ tailWord_1583791) baseStart_1583791 baseEnd_1583791 := by
    simpa [prefixWord, tailWord_1583791, baseEnd_1583791] using wordTrace_append hprefix tailTrace_1583791
  have hstable : (prefixWord ++ tailWord_1583791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583791).length < 2 ^ (prefixWord ++ tailWord_1583791).sum := by decide
  have hdescent : baseEnd_1583791 < baseStart_1583791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583797 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_1583797 : Nat := 118140960795 + 1583797 * 2 ^ 59
def prefixEnd_1583797 : Nat := 4983230072969 + 3 ^ 40 * 1583797 * 2
def baseEnd_1583797 : Nat := 542166080099363413769171

theorem tailTrace_1583797 : CollatzResearch.WordTrace tailWord_1583797 prefixEnd_1583797 542166080099363413769171 := by
  unfold tailWord_1583797
  simp only [CollatzResearch.WordTrace]
  refine ⟨57765822243181434837821645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38510548162120956558547763 57765822243181434837821645)
  ·
    refine ⟨21662183341193038064183117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57765822243181434837821645 21662183341193038064183117)
    ·
      refine ⟨8123318752947389274068669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21662183341193038064183117 8123318752947389274068669)
      ·
        refine ⟨3046244532355270977775751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8123318752947389274068669 3046244532355270977775751)
        ·
          refine ⟨4569366798532906466663627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046244532355270977775751 4569366798532906466663627)
          ·
            refine ⟨6854050197799359699995441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569366798532906466663627 6854050197799359699995441)
            ·
              refine ⟨5140537648349519774996581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854050197799359699995441 5140537648349519774996581)
              ·
                refine ⟨963850809065534957811859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5140537648349519774996581 963850809065534957811859)
                ·
                  refine ⟨1445776213598302436717789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963850809065534957811859 1445776213598302436717789)
                  ·
                    refine ⟨542166080099363413769171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445776213598302436717789 542166080099363413769171)
                    ·
                      rfl

theorem cell22_1583797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_1583797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583797 prefixEnd_1583797 := by exact prefixLift 1583797
  have htrace : WordTrace (prefixWord ++ tailWord_1583797) baseStart_1583797 baseEnd_1583797 := by
    simpa [prefixWord, tailWord_1583797, baseEnd_1583797] using wordTrace_append hprefix tailTrace_1583797
  have hstable : (prefixWord ++ tailWord_1583797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583797).length < 2 ^ (prefixWord ++ tailWord_1583797).sum := by decide
  have hdescent : baseEnd_1583797 < baseStart_1583797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583861 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 5]
def baseStart_1583861 : Nat := 118140960795 + 1583861 * 2 ^ 59
def prefixEnd_1583861 : Nat := 4983230072969 + 3 ^ 40 * 1583861 * 2
def baseEnd_1583861 : Nat := 180729329535762860056325

theorem tailTrace_1583861 : CollatzResearch.WordTrace tailWord_1583861 prefixEnd_1583861 180729329535762860056325 := by
  unfold tailWord_1583861
  simp only [CollatzResearch.WordTrace]
  refine ⟨57768156514949573768151437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38512104343299715845434291 57768156514949573768151437)
  ·
    refine ⟨21663058693106090163056789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57768156514949573768151437 21663058693106090163056789)
    ·
      refine ⟨1015455876239347976393287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21663058693106090163056789 1015455876239347976393287)
      ·
        refine ⟨1523183814359021964589931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015455876239347976393287 1523183814359021964589931)
        ·
          refine ⟨2284775721538532946884897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523183814359021964589931 2284775721538532946884897)
          ·
            refine ⟨1713581791153899710163673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2284775721538532946884897 1713581791153899710163673)
            ·
              refine ⟨1285186343365424782622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713581791153899710163673 1285186343365424782622755)
              ·
                refine ⟨1927779515048137173934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285186343365424782622755 1927779515048137173934133)
                ·
                  refine ⟨180729329535762860056325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1927779515048137173934133 180729329535762860056325)
                  ·
                    rfl

theorem cell22_1583861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_1583861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583861 prefixEnd_1583861 := by exact prefixLift 1583861
  have htrace : WordTrace (prefixWord ++ tailWord_1583861) baseStart_1583861 baseEnd_1583861 := by
    simpa [prefixWord, tailWord_1583861, baseEnd_1583861] using wordTrace_append hprefix tailTrace_1583861
  have hstable : (prefixWord ++ tailWord_1583861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583861).length < 2 ^ (prefixWord ++ tailWord_1583861).sum := by decide
  have hdescent : baseEnd_1583861 < baseStart_1583861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583866 : List Nat := [3, 1, 1, 1, 1, 3, 3, 9]
def baseStart_1583866 : Nat := 118140960795 + 1583866 * 2 ^ 59
def prefixEnd_1583866 : Nat := 4983230072969 + 3 ^ 40 * 1583866 * 2
def baseEnd_1583866 : Nat := 60243300023274470421551

theorem tailTrace_1583866 : CollatzResearch.WordTrace tailWord_1583866 prefixEnd_1583866 60243300023274470421551 := by
  unfold tailWord_1583866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14442084719982864905520863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38512225919954306414722301 14442084719982864905520863)
  ·
    refine ⟨21663127079974297358281295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14442084719982864905520863 21663127079974297358281295)
    ·
      refine ⟨32494690619961446037421943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21663127079974297358281295 32494690619961446037421943)
      ·
        refine ⟨48742035929942169056132915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32494690619961446037421943 48742035929942169056132915)
        ·
          refine ⟨73113053894913253584199373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48742035929942169056132915 73113053894913253584199373)
          ·
            refine ⟨27417395210592470094074765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73113053894913253584199373 27417395210592470094074765)
            ·
              refine ⟨10281523203972176285278037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27417395210592470094074765 10281523203972176285278037)
              ·
                refine ⟨60243300023274470421551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10281523203972176285278037 60243300023274470421551)
                ·
                  rfl

theorem cell22_1583866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_1583866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583866 prefixEnd_1583866 := by exact prefixLift 1583866
  have htrace : WordTrace (prefixWord ++ tailWord_1583866) baseStart_1583866 baseEnd_1583866 := by
    simpa [prefixWord, tailWord_1583866, baseEnd_1583866] using wordTrace_append hprefix tailTrace_1583866
  have hstable : (prefixWord ++ tailWord_1583866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583866).length < 2 ^ (prefixWord ++ tailWord_1583866).sum := by decide
  have hdescent : baseEnd_1583866 < baseStart_1583866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583881 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1583881 : Nat := 118140960795 + 1583881 * 2 ^ 59
def prefixEnd_1583881 : Nat := 4983230072969 + 3 ^ 40 * 1583881 * 2
def baseEnd_1583881 : Nat := 542194835016015194668913

theorem tailTrace_1583881 : CollatzResearch.WordTrace tailWord_1583881 prefixEnd_1583881 542194835016015194668913 := by
  unfold tailWord_1583881
  simp only [CollatzResearch.WordTrace]
  refine ⟨57768885974877117183879497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38512590649918078122586331 57768885974877117183879497)
  ·
    refine ⟨43326664481157837887909623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57768885974877117183879497 43326664481157837887909623)
    ·
      refine ⟨64989996721736756831864435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43326664481157837887909623 64989996721736756831864435)
      ·
        refine ⟨97484995082605135247796653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64989996721736756831864435 97484995082605135247796653)
        ·
          refine ⟨36556873155976925717923745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97484995082605135247796653 36556873155976925717923745)
          ·
            refine ⟨27417654866982694288442809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36556873155976925717923745 27417654866982694288442809)
            ·
              refine ⟨20563241150237020716332107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27417654866982694288442809 20563241150237020716332107)
              ·
                refine ⟨30844861725355531074498161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20563241150237020716332107 30844861725355531074498161)
                ·
                  refine ⟨23133646294016648305873621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30844861725355531074498161 23133646294016648305873621)
                  ·
                    refine ⟨542194835016015194668913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23133646294016648305873621 542194835016015194668913)
                    ·
                      rfl

theorem cell22_1583881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1583881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583881 prefixEnd_1583881 := by exact prefixLift 1583881
  have htrace : WordTrace (prefixWord ++ tailWord_1583881) baseStart_1583881 baseEnd_1583881 := by
    simpa [prefixWord, tailWord_1583881, baseEnd_1583881] using wordTrace_append hprefix tailTrace_1583881
  have hstable : (prefixWord ++ tailWord_1583881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583881).length < 2 ^ (prefixWord ++ tailWord_1583881).sum := by decide
  have hdescent : baseEnd_1583881 < baseStart_1583881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583928 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_1583928 : Nat := 118140960795 + 1583928 * 2 ^ 59
def prefixEnd_1583928 : Nat := 4983230072969 + 3 ^ 40 * 1583928 * 2
def baseEnd_1583928 : Nat := 180736974692174246247923

theorem tailTrace_1583928 : CollatzResearch.WordTrace tailWord_1583928 prefixEnd_1583928 180736974692174246247923 := by
  unfold tailWord_1583928
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885300102853422105420219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38513733470471229473893625 28885300102853422105420219)
  ·
    refine ⟨43327950154280133158130329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28885300102853422105420219 43327950154280133158130329)
    ·
      refine ⟨32495962615710099868597747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43327950154280133158130329 32495962615710099868597747)
      ·
        refine ⟨48743943923565149802896621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32495962615710099868597747 48743943923565149802896621)
        ·
          refine ⟨18278978971336931176086233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48743943923565149802896621 18278978971336931176086233)
          ·
            refine ⟨13709234228502698382064675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18278978971336931176086233 13709234228502698382064675)
            ·
              refine ⟨20563851342754047573097013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709234228502698382064675 20563851342754047573097013)
              ·
                refine ⟨1927861063383191959977845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20563851342754047573097013 1927861063383191959977845)
                ·
                  refine ⟨180736974692174246247923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1927861063383191959977845 180736974692174246247923)
                  ·
                    rfl

theorem cell22_1583928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_1583928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583928 prefixEnd_1583928 := by exact prefixLift 1583928
  have htrace : WordTrace (prefixWord ++ tailWord_1583928) baseStart_1583928 baseEnd_1583928 := by
    simpa [prefixWord, tailWord_1583928, baseEnd_1583928] using wordTrace_append hprefix tailTrace_1583928
  have hstable : (prefixWord ++ tailWord_1583928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583928).length < 2 ^ (prefixWord ++ tailWord_1583928).sum := by decide
  have hdescent : baseEnd_1583928 < baseStart_1583928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1583973 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 6]
def baseStart_1583973 : Nat := 118140960795 + 1583973 * 2 ^ 59
def prefixEnd_1583973 : Nat := 4983230072969 + 3 ^ 40 * 1583973 * 2
def baseEnd_1583973 : Nat := 180742109498719207122877

theorem tailTrace_1583973 : CollatzResearch.WordTrace tailWord_1583973 prefixEnd_1583973 180742109498719207122877 := by
  unfold tailWord_1583973
  simp only [CollatzResearch.WordTrace]
  refine ⟨57772241490543816896228573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38514827660362544597485715 57772241490543816896228573)
  ·
    refine ⟨21664590558953931336085715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57772241490543816896228573 21664590558953931336085715)
    ·
      refine ⟨32496885838430897004128573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21664590558953931336085715 32496885838430897004128573)
      ·
        refine ⟨12186332189411586376548215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32496885838430897004128573 12186332189411586376548215)
        ·
          refine ⟨18279498284117379564822323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186332189411586376548215 18279498284117379564822323)
          ·
            refine ⟨27419247426176069347233485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279498284117379564822323 27419247426176069347233485)
            ·
              refine ⟨10282217784816026005212557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27419247426176069347233485 10282217784816026005212557)
              ·
                refine ⟨3855831669306009751954709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10282217784816026005212557 3855831669306009751954709)
                ·
                  refine ⟨180742109498719207122877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3855831669306009751954709 180742109498719207122877)
                  ·
                    rfl

theorem cell22_1583973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_1583973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1583973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1583973 prefixEnd_1583973 := by exact prefixLift 1583973
  have htrace : WordTrace (prefixWord ++ tailWord_1583973) baseStart_1583973 baseEnd_1583973 := by
    simpa [prefixWord, tailWord_1583973, baseEnd_1583973] using wordTrace_append hprefix tailTrace_1583973
  have hstable : (prefixWord ++ tailWord_1583973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1583973).length < 2 ^ (prefixWord ++ tailWord_1583973).sum := by decide
  have hdescent : baseEnd_1583973 < baseStart_1583973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1583973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584003 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_1584003 : Nat := 118140960795 + 1584003 * 2 ^ 59
def prefixEnd_1584003 : Nat := 4983230072969 + 3 ^ 40 * 1584003 * 2
def baseEnd_1584003 : Nat := 542236598109247543118539

theorem tailTrace_1584003 : CollatzResearch.WordTrace tailWord_1584003 prefixEnd_1584003 542236598109247543118539 := by
  unfold tailWord_1584003
  simp only [CollatzResearch.WordTrace]
  refine ⟨57773335680435132019820663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38515557120290088013213775 57773335680435132019820663)
  ·
    refine ⟨86660003520652698029730995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57773335680435132019820663 86660003520652698029730995)
    ·
      refine ⟨129990005280979047044596493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86660003520652698029730995 129990005280979047044596493)
      ·
        refine ⟨48746251980367142641723685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129990005280979047044596493 48746251980367142641723685)
        ·
          refine ⟨9139922246318839245323191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48746251980367142641723685 9139922246318839245323191)
          ·
            refine ⟨13709883369478258867984787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9139922246318839245323191 13709883369478258867984787)
            ·
              refine ⟨20564825054217388301977181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13709883369478258867984787 20564825054217388301977181)
              ·
                refine ⟨7711809395331520613241443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20564825054217388301977181 7711809395331520613241443)
                ·
                  refine ⟨11567714092997280919862165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7711809395331520613241443 11567714092997280919862165)
                  ·
                    refine ⟨542236598109247543118539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11567714092997280919862165 542236598109247543118539)
                    ·
                      rfl

theorem cell22_1584003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_1584003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584003 prefixEnd_1584003 := by exact prefixLift 1584003
  have htrace : WordTrace (prefixWord ++ tailWord_1584003) baseStart_1584003 baseEnd_1584003 := by
    simpa [prefixWord, tailWord_1584003, baseEnd_1584003] using wordTrace_append hprefix tailTrace_1584003
  have hstable : (prefixWord ++ tailWord_1584003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584003).length < 2 ^ (prefixWord ++ tailWord_1584003).sum := by decide
  have hdescent : baseEnd_1584003 < baseStart_1584003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584005 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_1584005 : Nat := 118140960795 + 1584005 * 2 ^ 59
def prefixEnd_1584005 : Nat := 4983230072969 + 3 ^ 40 * 1584005 * 2
def baseEnd_1584005 : Nat := 542237282750120204568533

theorem tailTrace_1584005 : CollatzResearch.WordTrace tailWord_1584005 prefixEnd_1584005 542237282750120204568533 := by
  unfold tailWord_1584005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57773408626427886361393469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38515605750951924240928979 57773408626427886361393469)
  ·
    refine ⟨21665028234910457385522551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57773408626427886361393469 21665028234910457385522551)
    ·
      refine ⟨32497542352365686078283827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21665028234910457385522551 32497542352365686078283827)
      ·
        refine ⟨48746313528548529117425741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32497542352365686078283827 48746313528548529117425741)
        ·
          refine ⟨18279867573205698419034653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48746313528548529117425741 18279867573205698419034653)
          ·
            refine ⟨6854950339952136907137995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18279867573205698419034653 6854950339952136907137995)
            ·
              refine ⟨10282425509928205360706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6854950339952136907137995 10282425509928205360706993)
              ·
                refine ⟨7711819132446154020530245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10282425509928205360706993 7711819132446154020530245)
                ·
                  refine ⟨1445966087333653878849421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7711819132446154020530245 1445966087333653878849421)
                  ·
                    refine ⟨542237282750120204568533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445966087333653878849421 542237282750120204568533)
                    ·
                      rfl

theorem cell22_1584005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_1584005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584005 prefixEnd_1584005 := by exact prefixLift 1584005
  have htrace : WordTrace (prefixWord ++ tailWord_1584005) baseStart_1584005 baseEnd_1584005 := by
    simpa [prefixWord, tailWord_1584005, baseEnd_1584005] using wordTrace_append hprefix tailTrace_1584005
  have hstable : (prefixWord ++ tailWord_1584005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584005).length < 2 ^ (prefixWord ++ tailWord_1584005).sum := by decide
  have hdescent : baseEnd_1584005 < baseStart_1584005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584007 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 4]
def baseStart_1584007 : Nat := 118140960795 + 1584007 * 2 ^ 59
def prefixEnd_1584007 : Nat := 4983230072969 + 3 ^ 40 * 1584007 * 2
def baseEnd_1584007 : Nat := 180745989130330955339509

theorem tailTrace_1584007 : CollatzResearch.WordTrace tailWord_1584007 prefixEnd_1584007 180745989130330955339509 := by
  unfold tailWord_1584007
  simp only [CollatzResearch.WordTrace]
  refine ⟨57773481572420640702966275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38515654381613760468644183 57773481572420640702966275)
  ·
    refine ⟨86660222358630961054449413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57773481572420640702966275 86660222358630961054449413)
    ·
      refine ⟨16248791692243305197709265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86660222358630961054449413 16248791692243305197709265)
      ·
        refine ⟨12186593769182478898281949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16248791692243305197709265 12186593769182478898281949)
        ·
          refine ⟨4569972663443429586855731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12186593769182478898281949 4569972663443429586855731)
          ·
            refine ⟨6854958995165144380283597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569972663443429586855731 6854958995165144380283597)
            ·
              refine ⟨2570609623186929142606349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854958995165144380283597 2570609623186929142606349)
              ·
                refine ⟨963978608695098428477381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2570609623186929142606349 963978608695098428477381)
                ·
                  refine ⟨180745989130330955339509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963978608695098428477381 180745989130330955339509)
                  ·
                    rfl

theorem cell22_1584007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 4].length) (baseStart_1584007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584007 prefixEnd_1584007 := by exact prefixLift 1584007
  have htrace : WordTrace (prefixWord ++ tailWord_1584007) baseStart_1584007 baseEnd_1584007 := by
    simpa [prefixWord, tailWord_1584007, baseEnd_1584007] using wordTrace_append hprefix tailTrace_1584007
  have hstable : (prefixWord ++ tailWord_1584007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584007).length < 2 ^ (prefixWord ++ tailWord_1584007).sum := by decide
  have hdescent : baseEnd_1584007 < baseStart_1584007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584039 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1584039 : Nat := 118140960795 + 1584039 * 2 ^ 59
def prefixEnd_1584039 : Nat := 4983230072969 + 3 ^ 40 * 1584039 * 2
def baseEnd_1584039 : Nat := 542248921644955449218429

theorem tailTrace_1584039 : CollatzResearch.WordTrace tailWord_1584039 prefixEnd_1584039 542248921644955449218429 := by
  unfold tailWord_1584039
  simp only [CollatzResearch.WordTrace]
  refine ⟨57774648708304710168131171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38516432472203140112087447 57774648708304710168131171)
  ·
    refine ⟨86661973062457065252196757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57774648708304710168131171 86661973062457065252196757)
    ·
      refine ⟨4062279987302674933696723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86661973062457065252196757 4062279987302674933696723)
      ·
        refine ⟨6093419980954012400545085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062279987302674933696723 6093419980954012400545085)
        ·
          refine ⟨2285032492857754650204407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6093419980954012400545085 2285032492857754650204407)
          ·
            refine ⟨3427548739286631975306611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285032492857754650204407 3427548739286631975306611)
            ·
              refine ⟨5141323108929947962959917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427548739286631975306611 5141323108929947962959917)
              ·
                refine ⟨1927996165848730486109969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5141323108929947962959917 1927996165848730486109969)
                ·
                  refine ⟨1445997124386547864582477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927996165848730486109969 1445997124386547864582477)
                  ·
                    refine ⟨542248921644955449218429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445997124386547864582477 542248921644955449218429)
                    ·
                      rfl

theorem cell22_1584039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1584039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584039 prefixEnd_1584039 := by exact prefixLift 1584039
  have htrace : WordTrace (prefixWord ++ tailWord_1584039) baseStart_1584039 baseEnd_1584039 := by
    simpa [prefixWord, tailWord_1584039, baseEnd_1584039] using wordTrace_append hprefix tailTrace_1584039
  have hstable : (prefixWord ++ tailWord_1584039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584039).length < 2 ^ (prefixWord ++ tailWord_1584039).sum := by decide
  have hdescent : baseEnd_1584039 < baseStart_1584039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584052 : List Nat := [2, 5, 2, 1, 1, 1, 2, 8]
def baseStart_1584052 : Nat := 118140960795 + 1584052 * 2 ^ 59
def prefixEnd_1584052 : Nat := 4983230072969 + 3 ^ 40 * 1584052 * 2
def baseEnd_1584052 : Nat := 60250374645625305404821

theorem tailTrace_1584052 : CollatzResearch.WordTrace tailWord_1584052 prefixEnd_1584052 60250374645625305404821 := by
  unfold tailWord_1584052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887561428628806694177205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38516748571505075592236273 28887561428628806694177205)
  ·
    refine ⟨2708208883933950627579113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28887561428628806694177205 2708208883933950627579113)
    ·
      refine ⟨2031156662950462970684335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2708208883933950627579113 2031156662950462970684335)
      ·
        refine ⟨3046734994425694456026503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031156662950462970684335 3046734994425694456026503)
        ·
          refine ⟨4570102491638541684039755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046734994425694456026503 4570102491638541684039755)
          ·
            refine ⟨6855153737457812526059633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570102491638541684039755 6855153737457812526059633)
            ·
              refine ⟨5141365303093359394544725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6855153737457812526059633 5141365303093359394544725)
              ·
                refine ⟨60250374645625305404821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5141365303093359394544725 60250374645625305404821)
                ·
                  rfl

theorem cell22_1584052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_1584052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584052 prefixEnd_1584052 := by exact prefixLift 1584052
  have htrace : WordTrace (prefixWord ++ tailWord_1584052) baseStart_1584052 baseEnd_1584052 := by
    simpa [prefixWord, tailWord_1584052, baseEnd_1584052] using wordTrace_append hprefix tailTrace_1584052
  have hstable : (prefixWord ++ tailWord_1584052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584052).length < 2 ^ (prefixWord ++ tailWord_1584052).sum := by decide
  have hdescent : baseEnd_1584052 < baseStart_1584052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584063 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 7]
def baseStart_1584063 : Nat := 118140960795 + 1584063 * 2 ^ 59
def prefixEnd_1584063 : Nat := 4983230072969 + 3 ^ 40 * 1584063 * 2
def baseEnd_1584063 : Nat := 180752379111809128872785

theorem tailTrace_1584063 : CollatzResearch.WordTrace tailWord_1584063 prefixEnd_1584063 180752379111809128872785 := by
  unfold tailWord_1584063
  simp only [CollatzResearch.WordTrace]
  refine ⟨57775524060217762267004843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38517016040145174844669895 57775524060217762267004843)
  ·
    refine ⟨86663286090326643400507265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57775524060217762267004843 86663286090326643400507265)
    ·
      refine ⟨64997464567744982550380449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86663286090326643400507265 64997464567744982550380449)
      ·
        refine ⟨48748098425808736912785337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64997464567744982550380449 48748098425808736912785337)
        ·
          refine ⟨36561073819356552684589003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48748098425808736912785337 36561073819356552684589003)
          ·
            refine ⟨54841610729034829026883505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36561073819356552684589003 54841610729034829026883505)
            ·
              refine ⟨41131208046776121770162629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54841610729034829026883505 41131208046776121770162629)
              ·
                refine ⟨7712101508770522831905493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41131208046776121770162629 7712101508770522831905493)
                ·
                  refine ⟨180752379111809128872785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7712101508770522831905493 180752379111809128872785)
                  ·
                    rfl

theorem cell22_1584063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_1584063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584063 prefixEnd_1584063 := by exact prefixLift 1584063
  have htrace : WordTrace (prefixWord ++ tailWord_1584063) baseStart_1584063 baseEnd_1584063 := by
    simpa [prefixWord, tailWord_1584063, baseEnd_1584063] using wordTrace_append hprefix tailTrace_1584063
  have hstable : (prefixWord ++ tailWord_1584063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584063).length < 2 ^ (prefixWord ++ tailWord_1584063).sum := by decide
  have hdescent : baseEnd_1584063 < baseStart_1584063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584142 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1584142 : Nat := 118140960795 + 1584142 * 2 ^ 59
def prefixEnd_1584142 : Nat := 4983230072969 + 3 ^ 40 * 1584142 * 2
def baseEnd_1584142 : Nat := 180761393549965837964371

theorem tailTrace_1584142 : CollatzResearch.WordTrace tailWord_1584142 prefixEnd_1584142 180761393549965837964371 := by
  unfold tailWord_1584142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222300678366444844891335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38518936951287705839420453 7222300678366444844891335)
  ·
    refine ⟨10833451017549667267337003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7222300678366444844891335 10833451017549667267337003)
    ·
      refine ⟨16250176526324500901005505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10833451017549667267337003 16250176526324500901005505)
      ·
        refine ⟨12187632394743375675754129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16250176526324500901005505 12187632394743375675754129)
        ·
          refine ⟨9140724296057531756815597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12187632394743375675754129 9140724296057531756815597)
          ·
            refine ⟨3427771611021574408805849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9140724296057531756815597 3427771611021574408805849)
            ·
              refine ⟨2570828708266180806604387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427771611021574408805849 2570828708266180806604387)
              ·
                refine ⟨3856243062399271209906581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570828708266180806604387 3856243062399271209906581)
                ·
                  refine ⟨180761393549965837964371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3856243062399271209906581 180761393549965837964371)
                  ·
                    rfl

theorem cell22_1584142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1584142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584142 prefixEnd_1584142 := by exact prefixLift 1584142
  have htrace : WordTrace (prefixWord ++ tailWord_1584142) baseStart_1584142 baseEnd_1584142 := by
    simpa [prefixWord, tailWord_1584142, baseEnd_1584142] using wordTrace_append hprefix tailTrace_1584142
  have hstable : (prefixWord ++ tailWord_1584142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584142).length < 2 ^ (prefixWord ++ tailWord_1584142).sum := by decide
  have hdescent : baseEnd_1584142 < baseStart_1584142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584200 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1584200 : Nat := 118140960795 + 1584200 * 2 ^ 59
def prefixEnd_1584200 : Nat := 4983230072969 + 3 ^ 40 * 1584200 * 2
def baseEnd_1584200 : Nat := 542304035235204695942935

theorem tailTrace_1584200 : CollatzResearch.WordTrace tailWord_1584200 prefixEnd_1584200 542304035235204695942935 := by
  unfold tailWord_1584200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890260430360717332371027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38520347240480956443161369 28890260430360717332371027)
  ·
    refine ⟨43335390645541075998556541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28890260430360717332371027 43335390645541075998556541)
    ·
      refine ⟨16250771492077903499458703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43335390645541075998556541 16250771492077903499458703)
      ·
        refine ⟨24376157238116855249188055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16250771492077903499458703 24376157238116855249188055)
        ·
          refine ⟨36564235857175282873782083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24376157238116855249188055 36564235857175282873782083)
          ·
            refine ⟨54846353785762924310673125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36564235857175282873782083 54846353785762924310673125)
            ·
              refine ⟨10283691334830548308251211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54846353785762924310673125 10283691334830548308251211)
              ·
                refine ⟨15425537002245822462376817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10283691334830548308251211 15425537002245822462376817)
                ·
                  refine ⟨11569152751684366846782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15425537002245822462376817 11569152751684366846782613)
                  ·
                    refine ⟨542304035235204695942935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11569152751684366846782613 542304035235204695942935)
                    ·
                      rfl

theorem cell22_1584200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1584200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584200 prefixEnd_1584200 := by exact prefixLift 1584200
  have htrace : WordTrace (prefixWord ++ tailWord_1584200) baseStart_1584200 baseEnd_1584200 := by
    simpa [prefixWord, tailWord_1584200, baseEnd_1584200] using wordTrace_append hprefix tailTrace_1584200
  have hstable : (prefixWord ++ tailWord_1584200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584200).length < 2 ^ (prefixWord ++ tailWord_1584200).sum := by decide
  have hdescent : baseEnd_1584200 < baseStart_1584200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584249 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 5]
def baseStart_1584249 : Nat := 118140960795 + 1584249 * 2 ^ 59
def prefixEnd_1584249 : Nat := 4983230072969 + 3 ^ 40 * 1584249 * 2
def baseEnd_1584249 : Nat := 180773602978861633822595

theorem tailTrace_1584249 : CollatzResearch.WordTrace tailWord_1584249 prefixEnd_1584249 180773602978861633822595 := by
  unfold tailWord_1584249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57782308037543916033275801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38521538691695944022183867 57782308037543916033275801)
  ·
    refine ⟨43336731028157937024956851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57782308037543916033275801 43336731028157937024956851)
    ·
      refine ⟨65005096542236905537435277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43336731028157937024956851 65005096542236905537435277)
      ·
        refine ⟨24376911203338839576538229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65005096542236905537435277 24376911203338839576538229)
        ·
          refine ⟨2285335425313016210300459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24376911203338839576538229 2285335425313016210300459)
          ·
            refine ⟨3428003137969524315450689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285335425313016210300459 3428003137969524315450689)
            ·
              refine ⟨2571002353477143236588017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428003137969524315450689 2571002353477143236588017)
              ·
                refine ⟨1928251765107857427441013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571002353477143236588017 1928251765107857427441013)
                ·
                  refine ⟨180773602978861633822595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928251765107857427441013 180773602978861633822595)
                  ·
                    rfl

theorem cell22_1584249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_1584249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584249 prefixEnd_1584249 := by exact prefixLift 1584249
  have htrace : WordTrace (prefixWord ++ tailWord_1584249) baseStart_1584249 baseEnd_1584249 := by
    simpa [prefixWord, tailWord_1584249, baseEnd_1584249] using wordTrace_append hprefix tailTrace_1584249
  have hstable : (prefixWord ++ tailWord_1584249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584249).length < 2 ^ (prefixWord ++ tailWord_1584249).sum := by decide
  have hdescent : baseEnd_1584249 < baseStart_1584249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584264 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1584264 : Nat := 118140960795 + 1584264 * 2 ^ 59
def prefixEnd_1584264 : Nat := 4983230072969 + 3 ^ 40 * 1584264 * 2
def baseEnd_1584264 : Nat := 542325943743129862342739

theorem tailTrace_1584264 : CollatzResearch.WordTrace tailWord_1584264 prefixEnd_1584264 542325943743129862342739 := by
  unfold tailWord_1584264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28891427566244786797535923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38521903421659715730047897 28891427566244786797535923)
  ·
    refine ⟨43337141349367180196303885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28891427566244786797535923 43337141349367180196303885)
    ·
      refine ⟨16251428006012692573613957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43337141349367180196303885 16251428006012692573613957)
      ·
        refine ⟨3047142751127379857552617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16251428006012692573613957 3047142751127379857552617)
        ·
          refine ⟨2285357063345534893164463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047142751127379857552617 2285357063345534893164463)
          ·
            refine ⟨3428035595018302339746695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285357063345534893164463 3428035595018302339746695)
            ·
              refine ⟨5142053392527453509620043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428035595018302339746695 5142053392527453509620043)
              ·
                refine ⟨7713080088791180264430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142053392527453509620043 7713080088791180264430065)
                ·
                  refine ⟨5784810066593385198322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7713080088791180264430065 5784810066593385198322549)
                  ·
                    refine ⟨542325943743129862342739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5784810066593385198322549 542325943743129862342739)
                    ·
                      rfl

theorem cell22_1584264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1584264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584264 prefixEnd_1584264 := by exact prefixLift 1584264
  have htrace : WordTrace (prefixWord ++ tailWord_1584264) baseStart_1584264 baseEnd_1584264 := by
    simpa [prefixWord, tailWord_1584264, baseEnd_1584264] using wordTrace_append hprefix tailTrace_1584264
  have hstable : (prefixWord ++ tailWord_1584264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584264).length < 2 ^ (prefixWord ++ tailWord_1584264).sum := by decide
  have hdescent : baseEnd_1584264 < baseStart_1584264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584307 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_1584307 : Nat := 118140960795 + 1584307 * 2 ^ 59
def prefixEnd_1584307 : Nat := 4983230072969 + 3 ^ 40 * 1584307 * 2
def baseEnd_1584307 : Nat := 542340663521892083517607

theorem tailTrace_1584307 : CollatzResearch.WordTrace tailWord_1584307 prefixEnd_1584307 542340663521892083517607 := by
  unfold tailWord_1584307
  simp only [CollatzResearch.WordTrace]
  refine ⟨57784423471333791938887175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38522948980889194625924783 57784423471333791938887175)
  ·
    refine ⟨86676635207000687908330763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57784423471333791938887175 86676635207000687908330763)
    ·
      refine ⟨130014952810501031862496145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86676635207000687908330763 130014952810501031862496145)
      ·
        refine ⟨97511214607875773896872109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130014952810501031862496145 97511214607875773896872109)
        ·
          refine ⟨36566705477953415211327041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97511214607875773896872109 36566705477953415211327041)
          ·
            refine ⟨27425029108465061408495281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36566705477953415211327041 27425029108465061408495281)
            ·
              refine ⟨20568771831348796056371461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27425029108465061408495281 20568771831348796056371461)
              ·
                refine ⟨3856644718377899260569649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20568771831348796056371461 3856644718377899260569649)
                ·
                  refine ⟨2892483538783424445427237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856644718377899260569649 2892483538783424445427237)
                  ·
                    refine ⟨542340663521892083517607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892483538783424445427237 542340663521892083517607)
                    ·
                      rfl

theorem cell22_1584307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_1584307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584307 prefixEnd_1584307 := by exact prefixLift 1584307
  have htrace : WordTrace (prefixWord ++ tailWord_1584307) baseStart_1584307 baseEnd_1584307 := by
    simpa [prefixWord, tailWord_1584307, baseEnd_1584307] using wordTrace_append hprefix tailTrace_1584307
  have hstable : (prefixWord ++ tailWord_1584307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584307).length < 2 ^ (prefixWord ++ tailWord_1584307).sum := by decide
  have hdescent : baseEnd_1584307 < baseStart_1584307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584371 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 3, 3]
def baseStart_1584371 : Nat := 118140960795 + 1584371 * 2 ^ 59
def prefixEnd_1584371 : Nat := 4983230072969 + 3 ^ 40 * 1584371 * 2
def baseEnd_1584371 : Nat := 542362572029817249917411

theorem tailTrace_1584371 : CollatzResearch.WordTrace tailWord_1584371 prefixEnd_1584371 542362572029817249917411 := by
  unfold tailWord_1584371
  simp only [CollatzResearch.WordTrace]
  refine ⟨57786757743101930869216967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38524505162067953912811311 57786757743101930869216967)
  ·
    refine ⟨86680136614652896303825451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57786757743101930869216967 86680136614652896303825451)
    ·
      refine ⟨130020204921979344455738177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86680136614652896303825451 130020204921979344455738177)
      ·
        refine ⟨97515153691484508341803633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130020204921979344455738177 97515153691484508341803633)
        ·
          refine ⟨73136365268613381256352725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97515153691484508341803633 73136365268613381256352725)
          ·
            refine ⟨1714133560983126123195767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73136365268613381256352725 1714133560983126123195767)
            ·
              refine ⟨2571200341474689184793651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714133560983126123195767 2571200341474689184793651)
              ·
                refine ⟨3856800512212033777190477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571200341474689184793651 3856800512212033777190477)
                ·
                  refine ⟨1446300192079512666446429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3856800512212033777190477 1446300192079512666446429)
                  ·
                    refine ⟨542362572029817249917411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446300192079512666446429 542362572029817249917411)
                    ·
                      rfl

theorem cell22_1584371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 3].length) (baseStart_1584371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584371 prefixEnd_1584371 := by exact prefixLift 1584371
  have htrace : WordTrace (prefixWord ++ tailWord_1584371) baseStart_1584371 baseEnd_1584371 := by
    simpa [prefixWord, tailWord_1584371, baseEnd_1584371] using wordTrace_append hprefix tailTrace_1584371
  have hstable : (prefixWord ++ tailWord_1584371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584371).length < 2 ^ (prefixWord ++ tailWord_1584371).sum := by decide
  have hdescent : baseEnd_1584371 < baseStart_1584371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584444 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1584444 : Nat := 118140960795 + 1584444 * 2 ^ 59
def prefixEnd_1584444 : Nat := 4983230072969 + 3 ^ 40 * 1584444 * 2
def baseEnd_1584444 : Nat := 542387561421669392842187

theorem tailTrace_1584444 : CollatzResearch.WordTrace tailWord_1584444 prefixEnd_1584444 542387561421669392842187 := by
  unfold tailWord_1584444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28894710135918732168312193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38526280181224976224416257 28894710135918732168312193)
  ·
    refine ⟨21671032601939049126234145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28894710135918732168312193 21671032601939049126234145)
    ·
      refine ⟨16253274451454286844675609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21671032601939049126234145 16253274451454286844675609)
      ·
        refine ⟨12189955838590715133506707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16253274451454286844675609 12189955838590715133506707)
        ·
          refine ⟨18284933757886072700260061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189955838590715133506707 18284933757886072700260061)
          ·
            refine ⟨6856850159207277262597523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18284933757886072700260061 6856850159207277262597523)
            ·
              refine ⟨10285275238810915893896285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856850159207277262597523 10285275238810915893896285)
              ·
                refine ⟨3856978214554093460211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10285275238810915893896285 3856978214554093460211107)
                ·
                  refine ⟨5785467321831140190316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856978214554093460211107 5785467321831140190316661)
                  ·
                    refine ⟨542387561421669392842187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5785467321831140190316661 542387561421669392842187)
                    ·
                      rfl

theorem cell22_1584444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1584444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584444 prefixEnd_1584444 := by exact prefixLift 1584444
  have htrace : WordTrace (prefixWord ++ tailWord_1584444) baseStart_1584444 baseEnd_1584444 := by
    simpa [prefixWord, tailWord_1584444, baseEnd_1584444] using wordTrace_append hprefix tailTrace_1584444
  have hstable : (prefixWord ++ tailWord_1584444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584444).length < 2 ^ (prefixWord ++ tailWord_1584444).sum := by decide
  have hdescent : baseEnd_1584444 < baseStart_1584444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584457 : List Nat := [1, 2, 1, 1, 2, 3, 2, 10]
def baseStart_1584457 : Nat := 118140960795 + 1584457 * 2 ^ 59
def prefixEnd_1584457 : Nat := 4983230072969 + 3 ^ 40 * 1584457 * 2
def baseEnd_1584457 : Nat := 60265779065260188029683

theorem tailTrace_1584457 : CollatzResearch.WordTrace tailWord_1584457 prefixEnd_1584457 60265779065260188029683 := by
  unfold tailWord_1584457
  simp only [CollatzResearch.WordTrace]
  refine ⟨57789894420790367556847625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38526596280526911704565083 57789894420790367556847625)
  ·
    refine ⟨43342420815592775667635719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57789894420790367556847625 43342420815592775667635719)
    ·
      refine ⟨65013631223389163501453579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43342420815592775667635719 65013631223389163501453579)
      ·
        refine ⟨97520446835083745252180369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65013631223389163501453579 97520446835083745252180369)
        ·
          refine ⟨73140335126312808939135277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97520446835083745252180369 73140335126312808939135277)
          ·
            refine ⟨27427625672367303352175729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73140335126312808939135277 27427625672367303352175729)
            ·
              refine ⟨20570719254275477514131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27427625672367303352175729 20570719254275477514131797)
              ·
                refine ⟨60265779065260188029683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20570719254275477514131797 60265779065260188029683)
                ·
                  rfl

theorem cell22_1584457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 10].length) (baseStart_1584457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584457 prefixEnd_1584457 := by exact prefixLift 1584457
  have htrace : WordTrace (prefixWord ++ tailWord_1584457) baseStart_1584457 baseEnd_1584457 := by
    simpa [prefixWord, tailWord_1584457, baseEnd_1584457] using wordTrace_append hprefix tailTrace_1584457
  have hstable : (prefixWord ++ tailWord_1584457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584457).length < 2 ^ (prefixWord ++ tailWord_1584457).sum := by decide
  have hdescent : baseEnd_1584457 < baseStart_1584457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584519 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 7]
def baseStart_1584519 : Nat := 118140960795 + 1584519 * 2 ^ 59
def prefixEnd_1584519 : Nat := 4983230072969 + 3 ^ 40 * 1584519 * 2
def baseEnd_1584519 : Nat := 180804411818131399072319

theorem tailTrace_1584519 : CollatzResearch.WordTrace tailWord_1584519 prefixEnd_1584519 180804411818131399072319 := by
  unfold tailWord_1584519
  simp only [CollatzResearch.WordTrace]
  refine ⟨57792155746565752145604611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38528103831043834763736407 57792155746565752145604611)
  ·
    refine ⟨86688233619848628218406917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57792155746565752145604611 86688233619848628218406917)
    ·
      refine ⟨16254043803721617790951297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86688233619848628218406917 16254043803721617790951297)
      ·
        refine ⟨12190532852791213343213473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16254043803721617790951297 12190532852791213343213473)
        ·
          refine ⟨9142899639593410007410105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12190532852791213343213473 9142899639593410007410105)
          ·
            refine ⟨6857174729695057505557579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9142899639593410007410105 6857174729695057505557579)
            ·
              refine ⟨10285762094542586258336369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857174729695057505557579 10285762094542586258336369)
              ·
                refine ⟨7714321570906939693752277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10285762094542586258336369 7714321570906939693752277)
                ·
                  refine ⟨180804411818131399072319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7714321570906939693752277 180804411818131399072319)
                  ·
                    rfl

theorem cell22_1584519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_1584519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584519 prefixEnd_1584519 := by exact prefixLift 1584519
  have htrace : WordTrace (prefixWord ++ tailWord_1584519) baseStart_1584519 baseEnd_1584519 := by
    simpa [prefixWord, tailWord_1584519, baseEnd_1584519] using wordTrace_append hprefix tailTrace_1584519
  have hstable : (prefixWord ++ tailWord_1584519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584519).length < 2 ^ (prefixWord ++ tailWord_1584519).sum := by decide
  have hdescent : baseEnd_1584519 < baseStart_1584519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584579 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_1584579 : Nat := 118140960795 + 1584579 * 2 ^ 59
def prefixEnd_1584579 : Nat := 4983230072969 + 3 ^ 40 * 1584579 * 2
def baseEnd_1584579 : Nat := 542433774680574040716773

theorem tailTrace_1584579 : CollatzResearch.WordTrace tailWord_1584579 prefixEnd_1584579 542433774680574040716773 := by
  unfold tailWord_1584579
  simp only [CollatzResearch.WordTrace]
  refine ⟨57794344126348382392788791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38529562750898921595192527 57794344126348382392788791)
  ·
    refine ⟨86691516189522573589183187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57794344126348382392788791 86691516189522573589183187)
    ·
      refine ⟨130037274284283860383774781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86691516189522573589183187 130037274284283860383774781)
      ·
        refine ⟨48763977856606447643915543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130037274284283860383774781 48763977856606447643915543)
        ·
          refine ⟨73145966784909671465873315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48763977856606447643915543 73145966784909671465873315)
          ·
            refine ⟨109718950177364507198809973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73145966784909671465873315 109718950177364507198809973)
            ·
              refine ⟨10286151579127922549888435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109718950177364507198809973 10286151579127922549888435)
              ·
                refine ⟨15429227368691883824832653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286151579127922549888435 15429227368691883824832653)
                ·
                  refine ⟨5785960263259456434312245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429227368691883824832653 5785960263259456434312245)
                  ·
                    refine ⟨542433774680574040716773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5785960263259456434312245 542433774680574040716773)
                    ·
                      rfl

theorem cell22_1584579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_1584579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584579 prefixEnd_1584579 := by exact prefixLift 1584579
  have htrace : WordTrace (prefixWord ++ tailWord_1584579) baseStart_1584579 baseEnd_1584579 := by
    simpa [prefixWord, tailWord_1584579, baseEnd_1584579] using wordTrace_append hprefix tailTrace_1584579
  have hstable : (prefixWord ++ tailWord_1584579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584579).length < 2 ^ (prefixWord ++ tailWord_1584579).sum := by decide
  have hdescent : baseEnd_1584579 < baseStart_1584579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584583 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1584583 : Nat := 118140960795 + 1584583 * 2 ^ 59
def prefixEnd_1584583 : Nat := 4983230072969 + 3 ^ 40 * 1584583 * 2
def baseEnd_1584583 : Nat := 542435143962319363616761

theorem tailTrace_1584583 : CollatzResearch.WordTrace tailWord_1584583 prefixEnd_1584583 542435143962319363616761 := by
  unfold tailWord_1584583
  simp only [CollatzResearch.WordTrace]
  refine ⟨57794490018333891075934403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38529660012222594050622935 57794490018333891075934403)
  ·
    refine ⟨86691735027500836613901605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57794490018333891075934403 86691735027500836613901605)
    ·
      refine ⟨16254700317656406865106551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86691735027500836613901605 16254700317656406865106551)
      ·
        refine ⟨24382050476484610297659827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254700317656406865106551 24382050476484610297659827)
        ·
          refine ⟨36573075714726915446489741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24382050476484610297659827 36573075714726915446489741)
          ·
            refine ⟨13714903393022593292433653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36573075714726915446489741 13714903393022593292433653)
            ·
              refine ⟨1285772193095868121165655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13714903393022593292433653 1285772193095868121165655)
              ·
                refine ⟨1928658289643802181748483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285772193095868121165655 1928658289643802181748483)
                ·
                  refine ⟨2892987434465703272622725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928658289643802181748483 2892987434465703272622725)
                  ·
                    refine ⟨542435143962319363616761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892987434465703272622725 542435143962319363616761)
                    ·
                      rfl

theorem cell22_1584583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1584583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584583 prefixEnd_1584583 := by exact prefixLift 1584583
  have htrace : WordTrace (prefixWord ++ tailWord_1584583) baseStart_1584583 baseEnd_1584583 := by
    simpa [prefixWord, tailWord_1584583, baseEnd_1584583] using wordTrace_append hprefix tailTrace_1584583
  have hstable : (prefixWord ++ tailWord_1584583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584583).length < 2 ^ (prefixWord ++ tailWord_1584583).sum := by decide
  have hdescent : baseEnd_1584583 < baseStart_1584583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584613 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_1584613 : Nat := 118140960795 + 1584613 * 2 ^ 59
def prefixEnd_1584613 : Nat := 4983230072969 + 3 ^ 40 * 1584613 * 2
def baseEnd_1584613 : Nat := 542445413575409285366669

theorem tailTrace_1584613 : CollatzResearch.WordTrace tailWord_1584613 prefixEnd_1584613 542445413575409285366669 := by
  unfold tailWord_1584613
  simp only [CollatzResearch.WordTrace]
  refine ⟨57795584208225206199526493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38530389472150137466350995 57795584208225206199526493)
  ·
    refine ⟨21673344078084452324822435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57795584208225206199526493 21673344078084452324822435)
    ·
      refine ⟨32510016117126678487233653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673344078084452324822435 32510016117126678487233653)
      ·
        refine ⟨3047814010980626108178155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32510016117126678487233653 3047814010980626108178155)
        ·
          refine ⟨4571721016470939162267233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047814010980626108178155 4571721016470939162267233)
          ·
            refine ⟨3428790762353204371700425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4571721016470939162267233 3428790762353204371700425)
            ·
              refine ⟨2571593071764903278775319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428790762353204371700425 2571593071764903278775319)
              ·
                refine ⟨3857389607647354918162979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571593071764903278775319 3857389607647354918162979)
                ·
                  refine ⟨5786084411471032377244469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857389607647354918162979 5786084411471032377244469)
                  ·
                    refine ⟨542445413575409285366669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5786084411471032377244469 542445413575409285366669)
                    ·
                      rfl

theorem cell22_1584613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_1584613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584613 prefixEnd_1584613 := by exact prefixLift 1584613
  have htrace : WordTrace (prefixWord ++ tailWord_1584613) baseStart_1584613 baseEnd_1584613 := by
    simpa [prefixWord, tailWord_1584613, baseEnd_1584613] using wordTrace_append hprefix tailTrace_1584613
  have hstable : (prefixWord ++ tailWord_1584613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584613).length < 2 ^ (prefixWord ++ tailWord_1584613).sum := by decide
  have hdescent : baseEnd_1584613 < baseStart_1584613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584639 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1584639 : Nat := 118140960795 + 1584639 * 2 ^ 59
def prefixEnd_1584639 : Nat := 4983230072969 + 3 ^ 40 * 1584639 * 2
def baseEnd_1584639 : Nat := 542454313906753884216589

theorem tailTrace_1584639 : CollatzResearch.WordTrace tailWord_1584639 prefixEnd_1584639 542454313906753884216589 := by
  unfold tailWord_1584639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57796532506131012639972971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38531021670754008426648647 57796532506131012639972971)
  ·
    refine ⟨86694798759196518959959457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57796532506131012639972971 86694798759196518959959457)
    ·
      refine ⟨65021099069397389219969593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86694798759196518959959457 65021099069397389219969593)
      ·
        refine ⟨48765824302048041914977195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65021099069397389219969593 48765824302048041914977195)
        ·
          refine ⟨73148736453072062872465793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48765824302048041914977195 73148736453072062872465793)
          ·
            refine ⟨54861552339804047154349345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73148736453072062872465793 54861552339804047154349345)
            ·
              refine ⟨41146164254853035365762009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54861552339804047154349345 41146164254853035365762009)
              ·
                refine ⟨30859623191139776524321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41146164254853035365762009 30859623191139776524321507)
                ·
                  refine ⟨46289434786709664786482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30859623191139776524321507 46289434786709664786482261)
                  ·
                    refine ⟨542454313906753884216589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46289434786709664786482261 542454313906753884216589)
                    ·
                      rfl

theorem cell22_1584639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1584639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584639 prefixEnd_1584639 := by exact prefixLift 1584639
  have htrace : WordTrace (prefixWord ++ tailWord_1584639) baseStart_1584639 baseEnd_1584639 := by
    simpa [prefixWord, tailWord_1584639, baseEnd_1584639] using wordTrace_append hprefix tailTrace_1584639
  have hstable : (prefixWord ++ tailWord_1584639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584639).length < 2 ^ (prefixWord ++ tailWord_1584639).sum := by decide
  have hdescent : baseEnd_1584639 < baseStart_1584639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584671 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 5]
def baseStart_1584671 : Nat := 118140960795 + 1584671 * 2 ^ 59
def prefixEnd_1584671 : Nat := 4983230072969 + 3 ^ 40 * 1584671 * 2
def baseEnd_1584671 : Nat := 180821756053572155805497

theorem tailTrace_1584671 : CollatzResearch.WordTrace tailWord_1584671 prefixEnd_1584671 180821756053572155805497 := by
  unfold tailWord_1584671
  simp only [CollatzResearch.WordTrace]
  refine ⟨57797699642015082105137867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38531799761343388070091911 57797699642015082105137867)
  ·
    refine ⟨86696549463022623157706801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57797699642015082105137867 86696549463022623157706801)
    ·
      refine ⟨65022412097266967368280101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86696549463022623157706801 65022412097266967368280101)
      ·
        refine ⟨12191702268237556381552519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65022412097266967368280101 12191702268237556381552519)
        ·
          refine ⟨18287553402356334572328779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12191702268237556381552519 18287553402356334572328779)
          ·
            refine ⟨27431330103534501858493169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18287553402356334572328779 27431330103534501858493169)
            ·
              refine ⟨20573497577650876393869877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27431330103534501858493169 20573497577650876393869877)
              ·
                refine ⟨1928765397904769661925301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20573497577650876393869877 1928765397904769661925301)
                ·
                  refine ⟨180821756053572155805497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928765397904769661925301 180821756053572155805497)
                  ·
                    rfl

theorem cell22_1584671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 5].length) (baseStart_1584671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584671 prefixEnd_1584671 := by exact prefixLift 1584671
  have htrace : WordTrace (prefixWord ++ tailWord_1584671) baseStart_1584671 baseEnd_1584671 := by
    simpa [prefixWord, tailWord_1584671, baseEnd_1584671] using wordTrace_append hprefix tailTrace_1584671
  have hstable : (prefixWord ++ tailWord_1584671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584671).length < 2 ^ (prefixWord ++ tailWord_1584671).sum := by decide
  have hdescent : baseEnd_1584671 < baseStart_1584671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584765 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1584765 : Nat := 118140960795 + 1584765 * 2 ^ 59
def prefixEnd_1584765 : Nat := 4983230072969 + 3 ^ 40 * 1584765 * 2
def baseEnd_1584765 : Nat := 542497446281731555566203

theorem tailTrace_1584765 : CollatzResearch.WordTrace tailWord_1584765 prefixEnd_1584765 542497446281731555566203 := by
  unfold tailWord_1584765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57801128103674536159059749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38534085402449690772706499 57801128103674536159059749)
  ·
    refine ⟨10837711519438975529823703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57801128103674536159059749 10837711519438975529823703)
    ·
      refine ⟨16256567279158463294735555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10837711519438975529823703 16256567279158463294735555)
      ·
        refine ⟨24384850918737694942103333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16256567279158463294735555 24384850918737694942103333)
        ·
          refine ⟨4572159547263317801644375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24384850918737694942103333 4572159547263317801644375)
          ·
            refine ⟨6858239320894976702466563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572159547263317801644375 6858239320894976702466563)
            ·
              refine ⟨10287358981342465053699845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6858239320894976702466563 10287358981342465053699845)
              ·
                refine ⟨1928879809001712197568721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10287358981342465053699845 1928879809001712197568721)
                ·
                  refine ⟨1446659856751284148176541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1928879809001712197568721 1446659856751284148176541)
                  ·
                    refine ⟨542497446281731555566203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446659856751284148176541 542497446281731555566203)
                    ·
                      rfl

theorem cell22_1584765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1584765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584765 prefixEnd_1584765 := by exact prefixLift 1584765
  have htrace : WordTrace (prefixWord ++ tailWord_1584765) baseStart_1584765 baseEnd_1584765 := by
    simpa [prefixWord, tailWord_1584765, baseEnd_1584765] using wordTrace_append hprefix tailTrace_1584765
  have hstable : (prefixWord ++ tailWord_1584765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584765).length < 2 ^ (prefixWord ++ tailWord_1584765).sum := by decide
  have hdescent : baseEnd_1584765 < baseStart_1584765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584778 : List Nat := [3, 1, 2, 3, 2, 1, 3, 7]
def baseStart_1584778 : Nat := 118140960795 + 1584778 * 2 ^ 59
def prefixEnd_1584778 : Nat := 4983230072969 + 3 ^ 40 * 1584778 * 2
def baseEnd_1584778 : Nat := 60277988494155983887907

theorem tailTrace_1584778 : CollatzResearch.WordTrace tailWord_1584778 prefixEnd_1584778 60277988494155983887907 := by
  unfold tailWord_1584778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14450400563156859844820747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38534401501751626252855325 14450400563156859844820747)
  ·
    refine ⟨21675600844735289767231121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14450400563156859844820747 21675600844735289767231121)
    ·
      refine ⟨16256700633551467325423341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21675600844735289767231121 16256700633551467325423341)
      ·
        refine ⟨6096262737581800247033753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16256700633551467325423341 6096262737581800247033753)
        ·
          refine ⟨4572197053186350185275315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6096262737581800247033753 4572197053186350185275315)
          ·
            refine ⟨6858295579779525277912973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572197053186350185275315 6858295579779525277912973)
            ·
              refine ⟨2571860842417321979217365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6858295579779525277912973 2571860842417321979217365)
              ·
                refine ⟨60277988494155983887907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2571860842417321979217365 60277988494155983887907)
                ·
                  rfl

theorem cell22_1584778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_1584778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584778 prefixEnd_1584778 := by exact prefixLift 1584778
  have htrace : WordTrace (prefixWord ++ tailWord_1584778) baseStart_1584778 baseEnd_1584778 := by
    simpa [prefixWord, tailWord_1584778, baseEnd_1584778] using wordTrace_append hprefix tailTrace_1584778
  have hstable : (prefixWord ++ tailWord_1584778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584778).length < 2 ^ (prefixWord ++ tailWord_1584778).sum := by decide
  have hdescent : baseEnd_1584778 < baseStart_1584778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584823 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 7]
def baseStart_1584823 : Nat := 118140960795 + 1584823 * 2 ^ 59
def prefixEnd_1584823 : Nat := 4983230072969 + 3 ^ 40 * 1584823 * 2
def baseEnd_1584823 : Nat := 180839100289012912538675

theorem tailTrace_1584823 : CollatzResearch.WordTrace tailWord_1584823 prefixEnd_1584823 180839100289012912538675 := by
  unfold tailWord_1584823
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803243537464412064671123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38535495691642941376447415 57803243537464412064671123)
  ·
    refine ⟨86704865306196618097006685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57803243537464412064671123 86704865306196618097006685)
    ·
      refine ⟨32514324489823731786377507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86704865306196618097006685 32514324489823731786377507)
      ·
        refine ⟨48771486734735597679566261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32514324489823731786377507 48771486734735597679566261)
        ·
          refine ⟨4572326881381462282459337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48771486734735597679566261 4572326881381462282459337)
          ·
            refine ⟨3429245161036096711844503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4572326881381462282459337 3429245161036096711844503)
            ·
              refine ⟨5143867741554145067766755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429245161036096711844503 5143867741554145067766755)
              ·
                refine ⟨7715801612331217601650133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143867741554145067766755 7715801612331217601650133)
                ·
                  refine ⟨180839100289012912538675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7715801612331217601650133 180839100289012912538675)
                  ·
                    rfl

theorem cell22_1584823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_1584823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584823 prefixEnd_1584823 := by exact prefixLift 1584823
  have htrace : WordTrace (prefixWord ++ tailWord_1584823) baseStart_1584823 baseEnd_1584823 := by
    simpa [prefixWord, tailWord_1584823, baseEnd_1584823] using wordTrace_append hprefix tailTrace_1584823
  have hstable : (prefixWord ++ tailWord_1584823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584823).length < 2 ^ (prefixWord ++ tailWord_1584823).sum := by decide
  have hdescent : baseEnd_1584823 < baseStart_1584823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584840 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_1584840 : Nat := 118140960795 + 1584840 * 2 ^ 59
def prefixEnd_1584840 : Nat := 4983230072969 + 3 ^ 40 * 1584840 * 2
def baseEnd_1584840 : Nat := 180841040104818786646991

theorem tailTrace_1584840 : CollatzResearch.WordTrace tailWord_1584840 prefixEnd_1584840 180841040104818786646991 := by
  unfold tailWord_1584840
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901931789201411984019987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38535909052268549312026649 28901931789201411984019987)
  ·
    refine ⟨43352897683802117976029981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28901931789201411984019987 43352897683802117976029981)
    ·
      refine ⟨16257336631425794241011243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43352897683802117976029981 16257336631425794241011243)
      ·
        refine ⟨24386004947138691361516865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16257336631425794241011243 24386004947138691361516865)
        ·
          refine ⟨18289503710354018521137649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24386004947138691361516865 18289503710354018521137649)
          ·
            refine ⟨13717127782765513890853237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18289503710354018521137649 13717127782765513890853237)
            ·
              refine ⟨1285980729634266927267491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13717127782765513890853237 1285980729634266927267491)
              ·
                refine ⟨1928971094451400390901237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285980729634266927267491 1928971094451400390901237)
                ·
                  refine ⟨180841040104818786646991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928971094451400390901237 180841040104818786646991)
                  ·
                    rfl

theorem cell22_1584840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_1584840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584840 prefixEnd_1584840 := by exact prefixLift 1584840
  have htrace : WordTrace (prefixWord ++ tailWord_1584840) baseStart_1584840 baseEnd_1584840 := by
    simpa [prefixWord, tailWord_1584840, baseEnd_1584840] using wordTrace_append hprefix tailTrace_1584840
  have hstable : (prefixWord ++ tailWord_1584840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584840).length < 2 ^ (prefixWord ++ tailWord_1584840).sum := by decide
  have hdescent : baseEnd_1584840 < baseStart_1584840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584851 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 12]
def baseStart_1584851 : Nat := 118140960795 + 1584851 * 2 ^ 59
def prefixEnd_1584851 : Nat := 4983230072969 + 3 ^ 40 * 1584851 * 2
def baseEnd_1584851 : Nat := 180842295279751999305313

theorem tailTrace_1584851 : CollatzResearch.WordTrace tailWord_1584851 prefixEnd_1584851 180842295279751999305313 := by
  unfold tailWord_1584851
  simp only [CollatzResearch.WordTrace]
  refine ⟨57804264781362972846690407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38536176520908648564460271 57804264781362972846690407)
  ·
    refine ⟨86706397172044459270035611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57804264781362972846690407 86706397172044459270035611)
    ·
      refine ⟨130059595758066688905053417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86706397172044459270035611 130059595758066688905053417)
      ·
        refine ⟨97544696818550016678790063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130059595758066688905053417 97544696818550016678790063)
        ·
          refine ⟨146317045227825025018185095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97544696818550016678790063 146317045227825025018185095)
          ·
            refine ⟨219475567841737537527277643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146317045227825025018185095 219475567841737537527277643)
            ·
              refine ⟨329213351762606306290916465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219475567841737537527277643 329213351762606306290916465)
              ·
                refine ⟨246910013821954729718187349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329213351762606306290916465 246910013821954729718187349)
                ·
                  refine ⟨180842295279751999305313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 246910013821954729718187349 180842295279751999305313)
                  ·
                    rfl

theorem cell22_1584851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_1584851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584851 prefixEnd_1584851 := by exact prefixLift 1584851
  have htrace : WordTrace (prefixWord ++ tailWord_1584851) baseStart_1584851 baseEnd_1584851 := by
    simpa [prefixWord, tailWord_1584851, baseEnd_1584851] using wordTrace_append hprefix tailTrace_1584851
  have hstable : (prefixWord ++ tailWord_1584851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584851).length < 2 ^ (prefixWord ++ tailWord_1584851).sum := by decide
  have hdescent : baseEnd_1584851 < baseStart_1584851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584947 : List Nat := [1, 1, 1, 2, 8, 1, 1, 7]
def baseStart_1584947 : Nat := 118140960795 + 1584947 * 2 ^ 59
def prefixEnd_1584947 : Nat := 4983230072969 + 3 ^ 40 * 1584947 * 2
def baseEnd_1584947 : Nat := 60284416511238194168405

theorem tailTrace_1584947 : CollatzResearch.WordTrace tailWord_1584947 prefixEnd_1584947 60284416511238194168405 := by
  unfold tailWord_1584947
  simp only [CollatzResearch.WordTrace]
  refine ⟨57807766189015181242185095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38538510792676787494790063 57807766189015181242185095)
  ·
    refine ⟨86711649283522771863277643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57807766189015181242185095 86711649283522771863277643)
    ·
      refine ⟨130067473925284157794916465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86711649283522771863277643 130067473925284157794916465)
      ·
        refine ⟨97550605443963118346187349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130067473925284157794916465 97550605443963118346187349)
        ·
          refine ⟨1143171157546442793119383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 97550605443963118346187349 1143171157546442793119383)
          ·
            refine ⟨1714756736319664189679075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143171157546442793119383 1714756736319664189679075)
            ·
              refine ⟨2572135104479496284518613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714756736319664189679075 2572135104479496284518613)
              ·
                refine ⟨60284416511238194168405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2572135104479496284518613 60284416511238194168405)
                ·
                  rfl

theorem cell22_1584947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 7].length) (baseStart_1584947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584947 prefixEnd_1584947 := by exact prefixLift 1584947
  have htrace : WordTrace (prefixWord ++ tailWord_1584947) baseStart_1584947 baseEnd_1584947 := by
    simpa [prefixWord, tailWord_1584947, baseEnd_1584947] using wordTrace_append hprefix tailTrace_1584947
  have hstable : (prefixWord ++ tailWord_1584947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584947).length < 2 ^ (prefixWord ++ tailWord_1584947).sum := by decide
  have hdescent : baseEnd_1584947 < baseStart_1584947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584966 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1584966 : Nat := 118140960795 + 1584966 * 2 ^ 59
def prefixEnd_1584966 : Nat := 4983230072969 + 3 ^ 40 * 1584966 * 2
def baseEnd_1584966 : Nat := 542566252689434031290587

theorem tailTrace_1584966 : CollatzResearch.WordTrace tailWord_1584966 prefixEnd_1584966 542566252689434031290587 := by
  unfold tailWord_1584966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806514349248323358972711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38538972783964231658084501 1806514349248323358972711)
  ·
    refine ⟨2709771523872485038459067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806514349248323358972711 2709771523872485038459067)
    ·
      refine ⟨4064657285808727557688601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709771523872485038459067 4064657285808727557688601)
      ·
        refine ⟨3048492964356545668266451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4064657285808727557688601 3048492964356545668266451)
        ·
          refine ⟨4572739446534818502399677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048492964356545668266451 4572739446534818502399677)
          ·
            refine ⟨1714777292450556938399879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4572739446534818502399677 1714777292450556938399879)
            ·
              refine ⟨2572165938675835407599819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714777292450556938399879 2572165938675835407599819)
              ·
                refine ⟨3858248908013753111399729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572165938675835407599819 3858248908013753111399729)
                ·
                  refine ⟨2893686681010314833549797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858248908013753111399729 2893686681010314833549797)
                  ·
                    refine ⟨542566252689434031290587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893686681010314833549797 542566252689434031290587)
                    ·
                      rfl

theorem cell22_1584966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1584966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584966 prefixEnd_1584966 := by exact prefixLift 1584966
  have htrace : WordTrace (prefixWord ++ tailWord_1584966) baseStart_1584966 baseEnd_1584966 := by
    simpa [prefixWord, tailWord_1584966, baseEnd_1584966] using wordTrace_append hprefix tailTrace_1584966
  have hstable : (prefixWord ++ tailWord_1584966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584966).length < 2 ^ (prefixWord ++ tailWord_1584966).sum := by decide
  have hdescent : baseEnd_1584966 < baseStart_1584966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1584992 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_1584992 : Nat := 118140960795 + 1584992 * 2 ^ 59
def prefixEnd_1584992 : Nat := 4983230072969 + 3 ^ 40 * 1584992 * 2
def baseEnd_1584992 : Nat := 180858384340259543380169

theorem tailTrace_1584992 : CollatzResearch.WordTrace tailWord_1584992 prefixEnd_1584992 180858384340259543380169 := by
  unfold tailWord_1584992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904703736926076963786615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38539604982568102618382153 28904703736926076963786615)
  ·
    refine ⟨43357055605389115445679923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28904703736926076963786615 43357055605389115445679923)
    ·
      refine ⟨65035583408083673168519885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43357055605389115445679923 65035583408083673168519885)
      ·
        refine ⟨24388343778031377438194957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65035583408083673168519885 24388343778031377438194957)
        ·
          refine ⟨9145628916761766539323109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24388343778031377438194957 9145628916761766539323109)
          ·
            refine ⟨1714805421892831226123083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9145628916761766539323109 1714805421892831226123083)
            ·
              refine ⟨2572208132839246839184625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714805421892831226123083 2572208132839246839184625)
              ·
                refine ⟨1929156099629435129388469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572208132839246839184625 1929156099629435129388469)
                ·
                  refine ⟨180858384340259543380169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929156099629435129388469 180858384340259543380169)
                  ·
                    rfl

theorem cell22_1584992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_1584992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1584992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1584992 prefixEnd_1584992 := by exact prefixLift 1584992
  have htrace : WordTrace (prefixWord ++ tailWord_1584992) baseStart_1584992 baseEnd_1584992 := by
    simpa [prefixWord, tailWord_1584992, baseEnd_1584992] using wordTrace_append hprefix tailTrace_1584992
  have hstable : (prefixWord ++ tailWord_1584992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1584992).length < 2 ^ (prefixWord ++ tailWord_1584992).sum := by decide
  have hdescent : baseEnd_1584992 < baseStart_1584992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1584992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585005 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1585005 : Nat := 118140960795 + 1585005 * 2 ^ 59
def prefixEnd_1585005 : Nat := 4983230072969 + 3 ^ 40 * 1585005 * 2
def baseEnd_1585005 : Nat := 542579603186450929565467

theorem tailTrace_1585005 : CollatzResearch.WordTrace tailWord_1585005 prefixEnd_1585005 542579603186450929565467 := by
  unfold tailWord_1585005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57809881622805057147796469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38539921081870038098530979 57809881622805057147796469)
  ·
    refine ⟨5419676402137974107605919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57809881622805057147796469 5419676402137974107605919)
    ·
      refine ⟨8129514603206961161408879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5419676402137974107605919 8129514603206961161408879)
      ·
        refine ⟨12194271904810441742113319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129514603206961161408879 12194271904810441742113319)
        ·
          refine ⟨18291407857215662613169979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194271904810441742113319 18291407857215662613169979)
          ·
            refine ⟨27437111785823493919754969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291407857215662613169979 27437111785823493919754969)
            ·
              refine ⟨20577833839367620439816227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27437111785823493919754969 20577833839367620439816227)
              ·
                refine ⟨30866750759051430659724341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20577833839367620439816227 30866750759051430659724341)
                ·
                  refine ⟨2893757883661071624349157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30866750759051430659724341 2893757883661071624349157)
                  ·
                    refine ⟨542579603186450929565467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893757883661071624349157 542579603186450929565467)
                    ·
                      rfl

theorem cell22_1585005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1585005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585005 prefixEnd_1585005 := by exact prefixLift 1585005
  have htrace : WordTrace (prefixWord ++ tailWord_1585005) baseStart_1585005 baseEnd_1585005 := by
    simpa [prefixWord, tailWord_1585005, baseEnd_1585005] using wordTrace_append hprefix tailTrace_1585005
  have hstable : (prefixWord ++ tailWord_1585005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585005).length < 2 ^ (prefixWord ++ tailWord_1585005).sum := by decide
  have hdescent : baseEnd_1585005 < baseStart_1585005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585165 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1585165 : Nat := 118140960795 + 1585165 * 2 ^ 59
def prefixEnd_1585165 : Nat := 4983230072969 + 3 ^ 40 * 1585165 * 2
def baseEnd_1585165 : Nat := 542634374456263845564977

theorem tailTrace_1585165 : CollatzResearch.WordTrace tailWord_1585165 prefixEnd_1585165 542634374456263845564977 := by
  unfold tailWord_1585165
  simp only [CollatzResearch.WordTrace]
  refine ⟨57815717302225404473620949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38543811534816936315747299 57815717302225404473620949)
  ·
    refine ⟨1355055874270907917350491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57815717302225404473620949 1355055874270907917350491)
    ·
      refine ⟨2032583811406361876025737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355055874270907917350491 2032583811406361876025737)
      ·
        refine ⟨1524437858554771407019303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032583811406361876025737 1524437858554771407019303)
        ·
          refine ⟨2286656787832157110528955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524437858554771407019303 2286656787832157110528955)
          ·
            refine ⟨3429985181748235665793433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286656787832157110528955 3429985181748235665793433)
            ·
              refine ⟨2572488886311176749345075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429985181748235665793433 2572488886311176749345075)
              ·
                refine ⟨3858733329466765124017613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572488886311176749345075 3858733329466765124017613)
                ·
                  refine ⟨1447024998550036921506605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3858733329466765124017613 1447024998550036921506605)
                  ·
                    refine ⟨542634374456263845564977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447024998550036921506605 542634374456263845564977)
                    ·
                      rfl

theorem cell22_1585165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1585165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585165 prefixEnd_1585165 := by exact prefixLift 1585165
  have htrace : WordTrace (prefixWord ++ tailWord_1585165) baseStart_1585165 baseEnd_1585165 := by
    simpa [prefixWord, tailWord_1585165, baseEnd_1585165] using wordTrace_append hprefix tailTrace_1585165
  have hstable : (prefixWord ++ tailWord_1585165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585165).length < 2 ^ (prefixWord ++ tailWord_1585165).sum := by decide
  have hdescent : baseEnd_1585165 < baseStart_1585165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585202 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1585202 : Nat := 118140960795 + 1585202 * 2 ^ 59
def prefixEnd_1585202 : Nat := 4983230072969 + 3 ^ 40 * 1585202 * 2
def baseEnd_1585202 : Nat := 542647040312408082389863

theorem tailTrace_1585202 : CollatzResearch.WordTrace tailWord_1585202 prefixEnd_1585202 542647040312408082389863 := by
  unfold tailWord_1585202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454266700772839948179465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38544711202060906528478573 14454266700772839948179465)
  ·
    refine ⟨10840700025579629961134599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14454266700772839948179465 10840700025579629961134599)
    ·
      refine ⟨16261050038369444941701899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840700025579629961134599 16261050038369444941701899)
      ·
        refine ⟨24391575057554167412552849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16261050038369444941701899 24391575057554167412552849)
        ·
          refine ⟨18293681293165625559414637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24391575057554167412552849 18293681293165625559414637)
          ·
            refine ⟨6860130484937109584780489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18293681293165625559414637 6860130484937109584780489)
            ·
              refine ⟨5145097863702832188585367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860130484937109584780489 5145097863702832188585367)
              ·
                refine ⟨7717646795554248282878051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145097863702832188585367 7717646795554248282878051)
                ·
                  refine ⟨11576470193331372424317077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717646795554248282878051 11576470193331372424317077)
                  ·
                    refine ⟨542647040312408082389863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11576470193331372424317077 542647040312408082389863)
                    ·
                      rfl

theorem cell22_1585202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1585202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585202 prefixEnd_1585202 := by exact prefixLift 1585202
  have htrace : WordTrace (prefixWord ++ tailWord_1585202) baseStart_1585202 baseEnd_1585202 := by
    simpa [prefixWord, tailWord_1585202, baseEnd_1585202] using wordTrace_append hprefix tailTrace_1585202
  have hstable : (prefixWord ++ tailWord_1585202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585202).length < 2 ^ (prefixWord ++ tailWord_1585202).sum := by decide
  have hdescent : baseEnd_1585202 < baseStart_1585202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585217 : List Nat := [1, 2, 5, 1, 2, 1, 10]
def baseStart_1585217 : Nat := 118140960795 + 1585217 * 2 ^ 59
def prefixEnd_1585217 : Nat := 4983230072969 + 3 ^ 40 * 1585217 * 2
def baseEnd_1585217 : Nat := 20098228708109371972771

theorem tailTrace_1585217 : CollatzResearch.WordTrace tailWord_1585217 prefixEnd_1585217 20098228708109371972771 := by
  unfold tailWord_1585217
  simp only [CollatzResearch.WordTrace]
  refine ⟨57817613898037017354513905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38545075932024678236342603 57817613898037017354513905)
  ·
    refine ⟨43363210423527763015885429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57817613898037017354513905 43363210423527763015885429)
    ·
      refine ⟨4065300977205727782739259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43363210423527763015885429 4065300977205727782739259)
      ·
        refine ⟨6097951465808591674108889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065300977205727782739259 6097951465808591674108889)
        ·
          refine ⟨4573463599356443755581667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097951465808591674108889 4573463599356443755581667)
          ·
            refine ⟨6860195399034665633372501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573463599356443755581667 6860195399034665633372501)
            ·
              refine ⟨20098228708109371972771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6860195399034665633372501 20098228708109371972771)
              ·
                rfl

theorem cell22_1585217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 10].length) (baseStart_1585217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585217 prefixEnd_1585217 := by exact prefixLift 1585217
  have htrace : WordTrace (prefixWord ++ tailWord_1585217) baseStart_1585217 baseEnd_1585217 := by
    simpa [prefixWord, tailWord_1585217, baseEnd_1585217] using wordTrace_append hprefix tailTrace_1585217
  have hstable : (prefixWord ++ tailWord_1585217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585217).length < 2 ^ (prefixWord ++ tailWord_1585217).sum := by decide
  have hdescent : baseEnd_1585217 < baseStart_1585217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585234 : List Nat := [3, 2, 2, 1, 4, 1, 2, 7]
def baseStart_1585234 : Nat := 118140960795 + 1585234 * 2 ^ 59
def prefixEnd_1585234 : Nat := 4983230072969 + 3 ^ 40 * 1585234 * 2
def baseEnd_1585234 : Nat := 60295332729596740621085

theorem tailTrace_1585234 : CollatzResearch.WordTrace tailWord_1585234 prefixEnd_1585234 60295332729596740621085 := by
  unfold tailWord_1585234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454558484743857314470689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38545489292650286171921837 14454558484743857314470689)
  ·
    refine ⟨10840918863557892985853017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14454558484743857314470689 10840918863557892985853017)
    ·
      refine ⟨8130689147668419739389763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10840918863557892985853017 8130689147668419739389763)
      ·
        refine ⟨12196033721502629609084645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130689147668419739389763 12196033721502629609084645)
        ·
          refine ⟨2286756322781743051703371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12196033721502629609084645 2286756322781743051703371)
          ·
            refine ⟨3430134484172614577555057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286756322781743051703371 3430134484172614577555057)
            ·
              refine ⟨2572600863129460933166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430134484172614577555057 2572600863129460933166293)
              ·
                refine ⟨60295332729596740621085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2572600863129460933166293 60295332729596740621085)
                ·
                  rfl

theorem cell22_1585234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_1585234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585234 prefixEnd_1585234 := by exact prefixLift 1585234
  have htrace : WordTrace (prefixWord ++ tailWord_1585234) baseStart_1585234 baseEnd_1585234 := by
    simpa [prefixWord, tailWord_1585234, baseEnd_1585234] using wordTrace_append hprefix tailTrace_1585234
  have hstable : (prefixWord ++ tailWord_1585234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585234).length < 2 ^ (prefixWord ++ tailWord_1585234).sum := by decide
  have hdescent : baseEnd_1585234 < baseStart_1585234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585283 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 1, 3]
def baseStart_1585283 : Nat := 118140960795 + 1585283 * 2 ^ 59
def prefixEnd_1585283 : Nat := 4983230072969 + 3 ^ 40 * 1585283 * 2
def baseEnd_1585283 : Nat := 542674768267750871114615

theorem tailTrace_1585283 : CollatzResearch.WordTrace tailWord_1585283 prefixEnd_1585283 542674768267750871114615 := by
  unfold tailWord_1585283
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820021115797910626416503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38546680743865273750944335 57820021115797910626416503)
  ·
    refine ⟨86730031673696865939624755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57820021115797910626416503 86730031673696865939624755)
    ·
      refine ⟨130095047510545298909437133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86730031673696865939624755 130095047510545298909437133)
      ·
        refine ⟨48785642816454487091038925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130095047510545298909437133 48785642816454487091038925)
        ·
          refine ⟨18294616056170432659139597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48785642816454487091038925 18294616056170432659139597)
          ·
            refine ⟨6860481021063912247177349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18294616056170432659139597 6860481021063912247177349)
            ·
              refine ⟨1286340191449483546345753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6860481021063912247177349 1286340191449483546345753)
              ·
                refine ⟨964755143587112659759315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286340191449483546345753 964755143587112659759315)
                ·
                  refine ⟨1447132715380668989638973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964755143587112659759315 1447132715380668989638973)
                  ·
                    refine ⟨542674768267750871114615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447132715380668989638973 542674768267750871114615)
                    ·
                      rfl

theorem cell22_1585283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 3].length) (baseStart_1585283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585283 prefixEnd_1585283 := by exact prefixLift 1585283
  have htrace : WordTrace (prefixWord ++ tailWord_1585283) baseStart_1585283 baseEnd_1585283 := by
    simpa [prefixWord, tailWord_1585283, baseEnd_1585283] using wordTrace_append hprefix tailTrace_1585283
  have hstable : (prefixWord ++ tailWord_1585283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585283).length < 2 ^ (prefixWord ++ tailWord_1585283).sum := by decide
  have hdescent : baseEnd_1585283 < baseStart_1585283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585302 : List Nat := [5, 3, 2, 1, 1, 1, 3, 6]
def baseStart_1585302 : Nat := 118140960795 + 1585302 * 2 ^ 59
def prefixEnd_1585302 : Nat := 4983230072969 + 3 ^ 40 * 1585302 * 2
def baseEnd_1585302 : Nat := 60297919150671239432173

theorem tailTrace_1585302 : CollatzResearch.WordTrace tailWord_1585302 prefixEnd_1585302 60297919150671239432173 := by
  unfold tailWord_1585302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613794631420567304459885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38547142735152717914238773 3613794631420567304459885)
  ·
    refine ⟨1355172986782712739172457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3613794631420567304459885 1355172986782712739172457)
    ·
      refine ⟨1016379740087034554379343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355172986782712739172457 1016379740087034554379343)
      ·
        refine ⟨1524569610130551831569015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016379740087034554379343 1524569610130551831569015)
        ·
          refine ⟨2286854415195827747353523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524569610130551831569015 2286854415195827747353523)
          ·
            refine ⟨3430281622793741621030285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286854415195827747353523 3430281622793741621030285)
            ·
              refine ⟨1286355608547653107886357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3430281622793741621030285 1286355608547653107886357)
              ·
                refine ⟨60297919150671239432173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1286355608547653107886357 60297919150671239432173)
                ·
                  rfl

theorem cell22_1585302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_1585302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585302 prefixEnd_1585302 := by exact prefixLift 1585302
  have htrace : WordTrace (prefixWord ++ tailWord_1585302) baseStart_1585302 baseEnd_1585302 := by
    simpa [prefixWord, tailWord_1585302, baseEnd_1585302] using wordTrace_append hprefix tailTrace_1585302
  have hstable : (prefixWord ++ tailWord_1585302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585302).length < 2 ^ (prefixWord ++ tailWord_1585302).sum := by decide
  have hdescent : baseEnd_1585302 < baseStart_1585302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585309 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1585309 : Nat := 118140960795 + 1585309 * 2 ^ 59
def prefixEnd_1585309 : Nat := 4983230072969 + 3 ^ 40 * 1585309 * 2
def baseEnd_1585309 : Nat := 542683668599095469964535

theorem tailTrace_1585309 : CollatzResearch.WordTrace tailWord_1585309 prefixEnd_1585309 542683668599095469964535 := by
  unfold tailWord_1585309
  simp only [CollatzResearch.WordTrace]
  refine ⟨57820969413703717066862981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38547312942469144711241987 57820969413703717066862981)
  ·
    refine ⟨10841431765069446950036809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57820969413703717066862981 10841431765069446950036809)
    ·
      refine ⟨8131073823802085212527607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10841431765069446950036809 8131073823802085212527607)
      ·
        refine ⟨12196610735703127818791411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131073823802085212527607 12196610735703127818791411)
        ·
          refine ⟨18294916103554691728187117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196610735703127818791411 18294916103554691728187117)
          ·
            refine ⟨6860593538833009398070169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18294916103554691728187117 6860593538833009398070169)
            ·
              refine ⟨5145445154124757048552627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860593538833009398070169 5145445154124757048552627)
              ·
                refine ⟨7718167731187135572828941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145445154124757048552627 7718167731187135572828941)
                ·
                  refine ⟨2894312899195175839810853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7718167731187135572828941 2894312899195175839810853)
                  ·
                    refine ⟨542683668599095469964535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894312899195175839810853 542683668599095469964535)
                    ·
                      rfl

theorem cell22_1585309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1585309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585309 prefixEnd_1585309 := by exact prefixLift 1585309
  have htrace : WordTrace (prefixWord ++ tailWord_1585309) baseStart_1585309 baseEnd_1585309 := by
    simpa [prefixWord, tailWord_1585309, baseEnd_1585309] using wordTrace_append hprefix tailTrace_1585309
  have hstable : (prefixWord ++ tailWord_1585309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585309).length < 2 ^ (prefixWord ++ tailWord_1585309).sum := by decide
  have hdescent : baseEnd_1585309 < baseStart_1585309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585339 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 4, 3]
def baseStart_1585339 : Nat := 118140960795 + 1585339 * 2 ^ 59
def prefixEnd_1585339 : Nat := 4983230072969 + 3 ^ 40 * 1585339 * 2
def baseEnd_1585339 : Nat := 542693938212185391714443

theorem tailTrace_1585339 : CollatzResearch.WordTrace tailWord_1585339 prefixEnd_1585339 542693938212185391714443 := by
  unfold tailWord_1585339
  simp only [CollatzResearch.WordTrace]
  refine ⟨57822063603595032190455071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38548042402396688126970047 57822063603595032190455071)
  ·
    refine ⟨86733095405392548285682607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57822063603595032190455071 86733095405392548285682607)
    ·
      refine ⟨130099643108088822428523911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86733095405392548285682607 130099643108088822428523911)
      ·
        refine ⟨195149464662133233642785867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130099643108088822428523911 195149464662133233642785867)
        ·
          refine ⟨292724196993199850464178801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195149464662133233642785867 292724196993199850464178801)
          ·
            refine ⟨219543147744899887848134101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292724196993199850464178801 219543147744899887848134101)
            ·
              refine ⟨5145542525271091121440643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 219543147744899887848134101 5145542525271091121440643)
              ·
                refine ⟨7718313787906636682160965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145542525271091121440643 7718313787906636682160965)
                ·
                  refine ⟨1447183835232494377905181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7718313787906636682160965 1447183835232494377905181)
                  ·
                    refine ⟨542693938212185391714443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447183835232494377905181 542693938212185391714443)
                    ·
                      rfl

theorem cell22_1585339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 3].length) (baseStart_1585339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585339 prefixEnd_1585339 := by exact prefixLift 1585339
  have htrace : WordTrace (prefixWord ++ tailWord_1585339) baseStart_1585339 baseEnd_1585339 := by
    simpa [prefixWord, tailWord_1585339, baseEnd_1585339] using wordTrace_append hprefix tailTrace_1585339
  have hstable : (prefixWord ++ tailWord_1585339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585339).length < 2 ^ (prefixWord ++ tailWord_1585339).sum := by decide
  have hdescent : baseEnd_1585339 < baseStart_1585339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585352 : List Nat := [2, 1, 3, 1, 2, 1, 1, 11]
def baseStart_1585352 : Nat := 118140960795 + 1585352 * 2 ^ 59
def prefixEnd_1585352 : Nat := 4983230072969 + 3 ^ 40 * 1585352 * 2
def baseEnd_1585352 : Nat := 60299820930873076793267

theorem tailTrace_1585352 : CollatzResearch.WordTrace tailWord_1585352 prefixEnd_1585352 60299820930873076793267 := by
  unfold tailWord_1585352
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911268876273967705339155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38548358501698623607118873 28911268876273967705339155)
  ·
    refine ⟨43366903314410951558008733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28911268876273967705339155 43366903314410951558008733)
    ·
      refine ⟨16262588742904106834253275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43366903314410951558008733 16262588742904106834253275)
      ·
        refine ⟨24393883114356160251379913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16262588742904106834253275 24393883114356160251379913)
        ·
          refine ⟨18295412335767120188534935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24393883114356160251379913 18295412335767120188534935)
          ·
            refine ⟨27443118503650680282802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295412335767120188534935 27443118503650680282802403)
            ·
              refine ⟨41164677755476020424203605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27443118503650680282802403 41164677755476020424203605)
              ·
                refine ⟨60299820930873076793267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41164677755476020424203605 60299820930873076793267)
                ·
                  rfl

theorem cell22_1585352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_1585352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585352 prefixEnd_1585352 := by exact prefixLift 1585352
  have htrace : WordTrace (prefixWord ++ tailWord_1585352) baseStart_1585352 baseEnd_1585352 := by
    simpa [prefixWord, tailWord_1585352, baseEnd_1585352] using wordTrace_append hprefix tailTrace_1585352
  have hstable : (prefixWord ++ tailWord_1585352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585352).length < 2 ^ (prefixWord ++ tailWord_1585352).sum := by decide
  have hdescent : baseEnd_1585352 < baseStart_1585352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585367 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1585367 : Nat := 118140960795 + 1585367 * 2 ^ 59
def prefixEnd_1585367 : Nat := 4983230072969 + 3 ^ 40 * 1585367 * 2
def baseEnd_1585367 : Nat := 542703523184402652014357

theorem tailTrace_1585367 : CollatzResearch.WordTrace tailWord_1585367 prefixEnd_1585367 542703523184402652014357 := by
  unfold tailWord_1585367
  simp only [CollatzResearch.WordTrace]
  refine ⟨57823084847493592972474355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38548723231662395314982903 57823084847493592972474355)
  ·
    refine ⟨86734627271240389458711533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57823084847493592972474355 86734627271240389458711533)
    ·
      refine ⟨32525485226715146047016825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86734627271240389458711533 32525485226715146047016825)
      ·
        refine ⟨24394113920036359535262619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32525485226715146047016825 24394113920036359535262619)
        ·
          refine ⟨36591170880054539302893929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24394113920036359535262619 36591170880054539302893929)
          ·
            refine ⟨27443378160040904477170447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36591170880054539302893929 27443378160040904477170447)
            ·
              refine ⟨41165067240061356715755671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27443378160040904477170447 41165067240061356715755671)
              ·
                refine ⟨61747600860092035073633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41165067240061356715755671 61747600860092035073633507)
                ·
                  refine ⟨92621401290138052610450261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61747600860092035073633507 92621401290138052610450261)
                  ·
                    refine ⟨542703523184402652014357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92621401290138052610450261 542703523184402652014357)
                    ·
                      rfl

theorem cell22_1585367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1585367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585367 prefixEnd_1585367 := by exact prefixLift 1585367
  have htrace : WordTrace (prefixWord ++ tailWord_1585367) baseStart_1585367 baseEnd_1585367 := by
    simpa [prefixWord, tailWord_1585367, baseEnd_1585367] using wordTrace_append hprefix tailTrace_1585367
  have hstable : (prefixWord ++ tailWord_1585367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585367).length < 2 ^ (prefixWord ++ tailWord_1585367).sum := by decide
  have hdescent : baseEnd_1585367 < baseStart_1585367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585369 : List Nat := [1, 2, 1, 2, 3, 1, 6, 6]
def baseStart_1585369 : Nat := 118140960795 + 1585369 * 2 ^ 59
def prefixEnd_1585369 : Nat := 4983230072969 + 3 ^ 40 * 1585369 * 2
def baseEnd_1585369 : Nat := 60300467536141701496039

theorem tailTrace_1585369 : CollatzResearch.WordTrace tailWord_1585369 prefixEnd_1585369 60300467536141701496039 := by
  unfold tailWord_1585369
  simp only [CollatzResearch.WordTrace]
  refine ⟨57823157793486347314047161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38548771862324231542698107 57823157793486347314047161)
  ·
    refine ⟨43367368345114760485535371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57823157793486347314047161 43367368345114760485535371)
    ·
      refine ⟨65051052517672140728303057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43367368345114760485535371 65051052517672140728303057)
      ·
        refine ⟨48788289388254105546227293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65051052517672140728303057 48788289388254105546227293)
        ·
          refine ⟨18295608520595289579835235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48788289388254105546227293 18295608520595289579835235)
          ·
            refine ⟨27443412780892934369752853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295608520595289579835235 27443412780892934369752853)
            ·
              refine ⟨1286409974104356298582165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27443412780892934369752853 1286409974104356298582165)
              ·
                refine ⟨60300467536141701496039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1286409974104356298582165 60300467536141701496039)
                ·
                  rfl

theorem cell22_1585369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 6].length) (baseStart_1585369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585369 prefixEnd_1585369 := by exact prefixLift 1585369
  have htrace : WordTrace (prefixWord ++ tailWord_1585369) baseStart_1585369 baseEnd_1585369 := by
    simpa [prefixWord, tailWord_1585369, baseEnd_1585369] using wordTrace_append hprefix tailTrace_1585369
  have hstable : (prefixWord ++ tailWord_1585369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585369).length < 2 ^ (prefixWord ++ tailWord_1585369).sum := by decide
  have hdescent : baseEnd_1585369 < baseStart_1585369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585448 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_1585448 : Nat := 118140960795 + 1585448 * 2 ^ 59
def prefixEnd_1585448 : Nat := 4983230072969 + 3 ^ 40 * 1585448 * 2
def baseEnd_1585448 : Nat := 180910417046581813579703

theorem tailTrace_1585448 : CollatzResearch.WordTrace tailWord_1585448 prefixEnd_1585448 180910417046581813579703 := by
  unfold tailWord_1585448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28913019580100071903086499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38550692773466762537448665 28913019580100071903086499)
  ·
    refine ⟨43369529370150107854629749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28913019580100071903086499 43369529370150107854629749)
    ·
      refine ⟨4065893378451572611371539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43369529370150107854629749 4065893378451572611371539)
      ·
        refine ⟨6098840067677358917057309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065893378451572611371539 6098840067677358917057309)
        ·
          refine ⟨2287065025379009593896491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6098840067677358917057309 2287065025379009593896491)
          ·
            refine ⟨3430597538068514390844737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287065025379009593896491 3430597538068514390844737)
            ·
              refine ⟨2572948153551385793133553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430597538068514390844737 2572948153551385793133553)
              ·
                refine ⟨1929711115163539344850165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572948153551385793133553 1929711115163539344850165)
                ·
                  refine ⟨180910417046581813579703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929711115163539344850165 180910417046581813579703)
                  ·
                    rfl

theorem cell22_1585448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_1585448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585448 prefixEnd_1585448 := by exact prefixLift 1585448
  have htrace : WordTrace (prefixWord ++ tailWord_1585448) baseStart_1585448 baseEnd_1585448 := by
    simpa [prefixWord, tailWord_1585448, baseEnd_1585448] using wordTrace_append hprefix tailTrace_1585448
  have hstable : (prefixWord ++ tailWord_1585448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585448).length < 2 ^ (prefixWord ++ tailWord_1585448).sum := by decide
  have hdescent : baseEnd_1585448 < baseStart_1585448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585459 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 6]
def baseStart_1585459 : Nat := 118140960795 + 1585459 * 2 ^ 59
def prefixEnd_1585459 : Nat := 4983230072969 + 3 ^ 40 * 1585459 * 2
def baseEnd_1585459 : Nat := 180911672221515026238025

theorem tailTrace_1585459 : CollatzResearch.WordTrace tailWord_1585459 prefixEnd_1585459 180911672221515026238025 := by
  unfold tailWord_1585459
  simp only [CollatzResearch.WordTrace]
  refine ⟨57826440363160292684823431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550960242106861789882287 57826440363160292684823431)
  ·
    refine ⟨86739660544740439027235147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57826440363160292684823431 86739660544740439027235147)
    ·
      refine ⟨130109490817110658540852721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86739660544740439027235147 130109490817110658540852721)
      ·
        refine ⟨97582118112832993905639541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130109490817110658540852721 97582118112832993905639541)
        ·
          refine ⟨9148323573078093178653707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97582118112832993905639541 9148323573078093178653707)
          ·
            refine ⟨13722485359617139767980561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148323573078093178653707 13722485359617139767980561)
            ·
              refine ⟨10291864019712854825985421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13722485359617139767980561 10291864019712854825985421)
              ·
                refine ⟨3859449007392320559744533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10291864019712854825985421 3859449007392320559744533)
                ·
                  refine ⟨180911672221515026238025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3859449007392320559744533 180911672221515026238025)
                  ·
                    rfl

theorem cell22_1585459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_1585459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585459 prefixEnd_1585459 := by exact prefixLift 1585459
  have htrace : WordTrace (prefixWord ++ tailWord_1585459) baseStart_1585459 baseEnd_1585459 := by
    simpa [prefixWord, tailWord_1585459, baseEnd_1585459] using wordTrace_append hprefix tailTrace_1585459
  have hstable : (prefixWord ++ tailWord_1585459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585459).length < 2 ^ (prefixWord ++ tailWord_1585459).sum := by decide
  have hdescent : baseEnd_1585459 < baseStart_1585459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585626 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1585626 : Nat := 118140960795 + 1585626 * 2 ^ 59
def prefixEnd_1585626 : Nat := 4983230072969 + 3 ^ 40 * 1585626 * 2
def baseEnd_1585626 : Nat := 542792184177412309788563

theorem tailTrace_1585626 : CollatzResearch.WordTrace tailWord_1585626 prefixEnd_1585626 542792184177412309788563 := by
  unfold tailWord_1585626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458132838388820051538183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38555020902370186804101821 14458132838388820051538183)
  ·
    refine ⟨21687199257583230077307275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14458132838388820051538183 21687199257583230077307275)
    ·
      refine ⟨32530798886374845115960913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21687199257583230077307275 32530798886374845115960913)
      ·
        refine ⟨24398099164781133836970685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32530798886374845115960913 24398099164781133836970685)
        ·
          refine ⟨9149287186792925188864007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24398099164781133836970685 9149287186792925188864007)
          ·
            refine ⟨13723930780189387783296011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149287186792925188864007 13723930780189387783296011)
            ·
              refine ⟨20585896170284081674944017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13723930780189387783296011 20585896170284081674944017)
              ·
                refine ⟨15439422127713061256208013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20585896170284081674944017 15439422127713061256208013)
                ·
                  refine ⟨5789783297892397971078005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15439422127713061256208013 5789783297892397971078005)
                  ·
                    refine ⟨542792184177412309788563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5789783297892397971078005 542792184177412309788563)
                    ·
                      rfl

theorem cell22_1585626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1585626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585626 prefixEnd_1585626 := by exact prefixLift 1585626
  have htrace : WordTrace (prefixWord ++ tailWord_1585626) baseStart_1585626 baseEnd_1585626 := by
    simpa [prefixWord, tailWord_1585626, baseEnd_1585626] using wordTrace_append hprefix tailTrace_1585626
  have hstable : (prefixWord ++ tailWord_1585626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585626).length < 2 ^ (prefixWord ++ tailWord_1585626).sum := by decide
  have hdescent : baseEnd_1585626 < baseStart_1585626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585643 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 2, 3]
def baseStart_1585643 : Nat := 118140960795 + 1585643 * 2 ^ 59
def prefixEnd_1585643 : Nat := 4983230072969 + 3 ^ 40 * 1585643 * 2
def baseEnd_1585643 : Nat := 542798003624829932113511

theorem tailTrace_1585643 : CollatzResearch.WordTrace tailWord_1585643 prefixEnd_1585643 542798003624829932113511 := by
  unfold tailWord_1585643
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833151394493692109521583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38555434262995794739681055 57833151394493692109521583)
  ·
    refine ⟨86749727091740538164282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57833151394493692109521583 86749727091740538164282375)
    ·
      refine ⟨130124590637610807246423563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86749727091740538164282375 130124590637610807246423563)
      ·
        refine ⟨195186885956416210869635345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130124590637610807246423563 195186885956416210869635345)
        ·
          refine ⟨146390164467312158152226509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195186885956416210869635345 146390164467312158152226509)
          ·
            refine ⟨54896311675242059307084941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146390164467312158152226509 54896311675242059307084941)
            ·
              refine ⟨20586116878215772240156853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54896311675242059307084941 20586116878215772240156853)
              ·
                refine ⟨1929948457332728647514705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20586116878215772240156853 1929948457332728647514705)
                ·
                  refine ⟨1447461342999546485636029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929948457332728647514705 1447461342999546485636029)
                  ·
                    refine ⟨542798003624829932113511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447461342999546485636029 542798003624829932113511)
                    ·
                      rfl

theorem cell22_1585643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 3].length) (baseStart_1585643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585643 prefixEnd_1585643 := by exact prefixLift 1585643
  have htrace : WordTrace (prefixWord ++ tailWord_1585643) baseStart_1585643 baseEnd_1585643 := by
    simpa [prefixWord, tailWord_1585643, baseEnd_1585643] using wordTrace_append hprefix tailTrace_1585643
  have hstable : (prefixWord ++ tailWord_1585643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585643).length < 2 ^ (prefixWord ++ tailWord_1585643).sum := by decide
  have hdescent : baseEnd_1585643 < baseStart_1585643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585722 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_1585722 : Nat := 118140960795 + 1585722 * 2 ^ 59
def prefixEnd_1585722 : Nat := 4983230072969 + 3 ^ 40 * 1585722 * 2
def baseEnd_1585722 : Nat := 542825046939300059388269

theorem tailTrace_1585722 : CollatzResearch.WordTrace tailWord_1585722 prefixEnd_1585722 542825046939300059388269 := by
  unfold tailWord_1585722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459008190301872150411855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38557355174138325734431613 14459008190301872150411855)
  ·
    refine ⟨21688512285452808225617783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14459008190301872150411855 21688512285452808225617783)
    ·
      refine ⟨32532768428179212338426675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21688512285452808225617783 32532768428179212338426675)
      ·
        refine ⟨48799152642268818507640013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32532768428179212338426675 48799152642268818507640013)
        ·
          refine ⟨18299682240850806940365005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48799152642268818507640013 18299682240850806940365005)
          ·
            refine ⟨6862380840319052602636877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18299682240850806940365005 6862380840319052602636877)
            ·
              refine ⟨2573392815119644725988829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6862380840319052602636877 2573392815119644725988829)
              ·
                refine ⟨965022305669866772245811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573392815119644725988829 965022305669866772245811)
                ·
                  refine ⟨1447533458504800158368717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965022305669866772245811 1447533458504800158368717)
                  ·
                    refine ⟨542825046939300059388269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447533458504800158368717 542825046939300059388269)
                    ·
                      rfl

theorem cell22_1585722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_1585722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585722 prefixEnd_1585722 := by exact prefixLift 1585722
  have htrace : WordTrace (prefixWord ++ tailWord_1585722) baseStart_1585722 baseEnd_1585722 := by
    simpa [prefixWord, tailWord_1585722, baseEnd_1585722] using wordTrace_append hprefix tailTrace_1585722
  have hstable : (prefixWord ++ tailWord_1585722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585722).length < 2 ^ (prefixWord ++ tailWord_1585722).sum := by decide
  have hdescent : baseEnd_1585722 < baseStart_1585722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585765 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_1585765 : Nat := 118140960795 + 1585765 * 2 ^ 59
def prefixEnd_1585765 : Nat := 4983230072969 + 3 ^ 40 * 1585765 * 2
def baseEnd_1585765 : Nat := 542839766718062280563137

theorem tailTrace_1585765 : CollatzResearch.WordTrace tailWord_1585765 prefixEnd_1585765 542839766718062280563137 := by
  unfold tailWord_1585765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57837601100051706945462749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38558400733367804630308499 57837601100051706945462749)
  ·
    refine ⟨21689100412519390104548531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57837601100051706945462749 21689100412519390104548531)
    ·
      refine ⟨32533650618779085156822797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21689100412519390104548531 32533650618779085156822797)
      ·
        refine ⟨12200118982042156933808549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32533650618779085156822797 12200118982042156933808549)
        ·
          refine ⟨2287522309132904425089103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12200118982042156933808549 2287522309132904425089103)
          ·
            refine ⟨3431283463699356637633655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287522309132904425089103 3431283463699356637633655)
            ·
              refine ⟨5146925195549034956450483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431283463699356637633655 5146925195549034956450483)
              ·
                refine ⟨7720387793323552434675725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5146925195549034956450483 7720387793323552434675725)
                ·
                  refine ⟨2895145422496332163003397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720387793323552434675725 2895145422496332163003397)
                  ·
                    refine ⟨542839766718062280563137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895145422496332163003397 542839766718062280563137)
                    ·
                      rfl

theorem cell22_1585765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_1585765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585765 prefixEnd_1585765 := by exact prefixLift 1585765
  have htrace : WordTrace (prefixWord ++ tailWord_1585765) baseStart_1585765 baseEnd_1585765 := by
    simpa [prefixWord, tailWord_1585765, baseEnd_1585765] using wordTrace_append hprefix tailTrace_1585765
  have hstable : (prefixWord ++ tailWord_1585765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585765).length < 2 ^ (prefixWord ++ tailWord_1585765).sum := by decide
  have hdescent : baseEnd_1585765 < baseStart_1585765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585795 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 2, 3]
def baseStart_1585795 : Nat := 118140960795 + 1585795 * 2 ^ 59
def prefixEnd_1585795 : Nat := 4983230072969 + 3 ^ 40 * 1585795 * 2
def baseEnd_1585795 : Nat := 542850036331152202313045

theorem tailTrace_1585795 : CollatzResearch.WordTrace tailWord_1585795 prefixEnd_1585795 542850036331152202313045 := by
  unfold tailWord_1585795
  simp only [CollatzResearch.WordTrace]
  refine ⟨57838695289943022069054839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38559130193295348046036559 57838695289943022069054839)
  ·
    refine ⟨86758042934914533103582259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57838695289943022069054839 86758042934914533103582259)
    ·
      refine ⟨130137064402371799655373389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86758042934914533103582259 130137064402371799655373389)
      ·
        refine ⟨48801399150889424870765021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130137064402371799655373389 48801399150889424870765021)
        ·
          refine ⟨18300524681583534326536883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48801399150889424870765021 18300524681583534326536883)
          ·
            refine ⟨27450787022375301489805325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300524681583534326536883 27450787022375301489805325)
            ·
              refine ⟨10294045133390738058676997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27450787022375301489805325 10294045133390738058676997)
              ·
                refine ⟨1930133462510763386001937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10294045133390738058676997 1930133462510763386001937)
                ·
                  refine ⟨1447600096883072539501453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930133462510763386001937 1447600096883072539501453)
                  ·
                    refine ⟨542850036331152202313045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447600096883072539501453 542850036331152202313045)
                    ·
                      rfl

theorem cell22_1585795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].length) (baseStart_1585795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585795 prefixEnd_1585795 := by exact prefixLift 1585795
  have htrace : WordTrace (prefixWord ++ tailWord_1585795) baseStart_1585795 baseEnd_1585795 := by
    simpa [prefixWord, tailWord_1585795, baseEnd_1585795] using wordTrace_append hprefix tailTrace_1585795
  have hstable : (prefixWord ++ tailWord_1585795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585795).length < 2 ^ (prefixWord ++ tailWord_1585795).sum := by decide
  have hdescent : baseEnd_1585795 < baseStart_1585795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585797 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 4]
def baseStart_1585797 : Nat := 118140960795 + 1585797 * 2 ^ 59
def prefixEnd_1585797 : Nat := 4983230072969 + 3 ^ 40 * 1585797 * 2
def baseEnd_1585797 : Nat := 180950240324008287921013

theorem tailTrace_1585797 : CollatzResearch.WordTrace tailWord_1585797 prefixEnd_1585797 180950240324008287921013 := by
  unfold tailWord_1585797
  simp only [CollatzResearch.WordTrace]
  refine ⟨57838768235935776410627645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38559178823957184273751763 57838768235935776410627645)
  ·
    refine ⟨21689538088475916153985367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57838768235935776410627645 21689538088475916153985367)
    ·
      refine ⟨32534307132713874230978051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21689538088475916153985367 32534307132713874230978051)
      ·
        refine ⟨48801460699070811346467077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32534307132713874230978051 48801460699070811346467077)
        ·
          refine ⟨9150273881075777127462577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48801460699070811346467077 9150273881075777127462577)
          ·
            refine ⟨6862705410806832845596933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9150273881075777127462577 6862705410806832845596933)
            ·
              refine ⟨1286757264526281158549425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6862705410806832845596933 1286757264526281158549425)
              ·
                refine ⟨965067948394710868912069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286757264526281158549425 965067948394710868912069)
                ·
                  refine ⟨180950240324008287921013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965067948394710868912069 180950240324008287921013)
                  ·
                    rfl

theorem cell22_1585797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_1585797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585797 prefixEnd_1585797 := by exact prefixLift 1585797
  have htrace : WordTrace (prefixWord ++ tailWord_1585797) baseStart_1585797 baseEnd_1585797 := by
    simpa [prefixWord, tailWord_1585797, baseEnd_1585797] using wordTrace_append hprefix tailTrace_1585797
  have hstable : (prefixWord ++ tailWord_1585797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585797).length < 2 ^ (prefixWord ++ tailWord_1585797).sum := by decide
  have hdescent : baseEnd_1585797 < baseStart_1585797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585812 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1585812 : Nat := 118140960795 + 1585812 * 2 ^ 59
def prefixEnd_1585812 : Nat := 4983230072969 + 3 ^ 40 * 1585812 * 2
def baseEnd_1585812 : Nat := 542855855778569824637993

theorem tailTrace_1585812 : CollatzResearch.WordTrace tailWord_1585812 prefixEnd_1585812 542855855778569824637993 := by
  unfold tailWord_1585812
  simp only [CollatzResearch.WordTrace]
  refine ⟨28919657665440716986211845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38559543553920955981615793 28919657665440716986211845)
  ·
    refine ⟨5422435812270134434914721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28919657665440716986211845 5422435812270134434914721)
    ·
      refine ⟨4066826859202600826186041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422435812270134434914721 4066826859202600826186041)
      ·
        refine ⟨3050120144401950619639531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4066826859202600826186041 3050120144401950619639531)
        ·
          refine ⟨4575180216602925929459297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050120144401950619639531 4575180216602925929459297)
          ·
            refine ⟨3431385162452194447094473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575180216602925929459297 3431385162452194447094473)
            ·
              refine ⟨2573538871839145835320855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431385162452194447094473 2573538871839145835320855)
              ·
                refine ⟨3860308307758718752981283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573538871839145835320855 3860308307758718752981283)
                ·
                  refine ⟨5790462461638078129471925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860308307758718752981283 5790462461638078129471925)
                  ·
                    refine ⟨542855855778569824637993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5790462461638078129471925 542855855778569824637993)
                    ·
                      rfl

theorem cell22_1585812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1585812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585812 prefixEnd_1585812 := by exact prefixLift 1585812
  have htrace : WordTrace (prefixWord ++ tailWord_1585812) baseStart_1585812 baseEnd_1585812 := by
    simpa [prefixWord, tailWord_1585812, baseEnd_1585812] using wordTrace_append hprefix tailTrace_1585812
  have hstable : (prefixWord ++ tailWord_1585812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585812).length < 2 ^ (prefixWord ++ tailWord_1585812).sum := by decide
  have hdescent : baseEnd_1585812 < baseStart_1585812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585891 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 1, 3]
def baseStart_1585891 : Nat := 118140960795 + 1585891 * 2 ^ 59
def prefixEnd_1585891 : Nat := 4983230072969 + 3 ^ 40 * 1585891 * 2
def baseEnd_1585891 : Nat := 542882899093039951912751

theorem tailTrace_1585891 : CollatzResearch.WordTrace tailWord_1585891 prefixEnd_1585891 542882899093039951912751 := by
  unfold tailWord_1585891
  simp only [CollatzResearch.WordTrace]
  refine ⟨57842196697595230464549527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38561464465063486976366351 57842196697595230464549527)
  ·
    refine ⟨86763295046392845696824291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57842196697595230464549527 86763295046392845696824291)
    ·
      refine ⟨130144942569589268545236437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86763295046392845696824291 130144942569589268545236437)
      ·
        refine ⟨3050272091474748481528979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 130144942569589268545236437 3050272091474748481528979)
        ·
          refine ⟨4575408137212122722293469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050272091474748481528979 4575408137212122722293469)
          ·
            refine ⟨1715778051454546020860051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4575408137212122722293469 1715778051454546020860051)
            ·
              refine ⟨2573667077181819031290077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715778051454546020860051 2573667077181819031290077)
              ·
                refine ⟨965125153943182136733779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573667077181819031290077 965125153943182136733779)
                ·
                  refine ⟨1447687730914773205100669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965125153943182136733779 1447687730914773205100669)
                  ·
                    refine ⟨542882899093039951912751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447687730914773205100669 542882899093039951912751)
                    ·
                      rfl

theorem cell22_1585891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 3].length) (baseStart_1585891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585891 prefixEnd_1585891 := by exact prefixLift 1585891
  have htrace : WordTrace (prefixWord ++ tailWord_1585891) baseStart_1585891 baseEnd_1585891 := by
    simpa [prefixWord, tailWord_1585891, baseEnd_1585891] using wordTrace_append hprefix tailTrace_1585891
  have hstable : (prefixWord ++ tailWord_1585891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585891).length < 2 ^ (prefixWord ++ tailWord_1585891).sum := by decide
  have hdescent : baseEnd_1585891 < baseStart_1585891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585908 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1585908 : Nat := 118140960795 + 1585908 * 2 ^ 59
def prefixEnd_1585908 : Nat := 4983230072969 + 3 ^ 40 * 1585908 * 2
def baseEnd_1585908 : Nat := 542888718540457574237699

theorem tailTrace_1585908 : CollatzResearch.WordTrace tailWord_1585908 prefixEnd_1585908 542888718540457574237699 := by
  unfold tailWord_1585908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28921408369266821183959189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38561877825689094911945585 28921408369266821183959189)
  ·
    refine ⟨1355691017309382242998087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28921408369266821183959189 1355691017309382242998087)
    ·
      refine ⟨2033536525964073364497131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355691017309382242998087 2033536525964073364497131)
      ·
        refine ⟨3050304788946110046745697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033536525964073364497131 3050304788946110046745697)
        ·
          refine ⟨2287728591709582535059273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3050304788946110046745697 2287728591709582535059273)
          ·
            refine ⟨1715796443782186901294455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287728591709582535059273 1715796443782186901294455)
            ·
              refine ⟨2573694665673280351941683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715796443782186901294455 2573694665673280351941683)
              ·
                refine ⟨3860541998509920527912525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573694665673280351941683 3860541998509920527912525)
                ·
                  refine ⟨1447703249441220197967197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3860541998509920527912525 1447703249441220197967197)
                  ·
                    refine ⟨542888718540457574237699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447703249441220197967197 542888718540457574237699)
                    ·
                      rfl

theorem cell22_1585908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1585908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585908 prefixEnd_1585908 := by exact prefixLift 1585908
  have htrace : WordTrace (prefixWord ++ tailWord_1585908) baseStart_1585908 baseEnd_1585908 := by
    simpa [prefixWord, tailWord_1585908, baseEnd_1585908] using wordTrace_append hprefix tailTrace_1585908
  have hstable : (prefixWord ++ tailWord_1585908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585908).length < 2 ^ (prefixWord ++ tailWord_1585908).sum := by decide
  have hdescent : baseEnd_1585908 < baseStart_1585908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585930 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1585930 : Nat := 118140960795 + 1585930 * 2 ^ 59
def prefixEnd_1585930 : Nat := 4983230072969 + 3 ^ 40 * 1585930 * 2
def baseEnd_1585930 : Nat := 542896249590056850187631

theorem tailTrace_1585930 : CollatzResearch.WordTrace tailWord_1585930 prefixEnd_1585930 542896249590056850187631 := by
  unfold tailWord_1585930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460904786113485031304811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38562412762969293416812829 14460904786113485031304811)
  ·
    refine ⟨21691357179170227546957217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14460904786113485031304811 21691357179170227546957217)
    ·
      refine ⟨16268517884377670660217913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21691357179170227546957217 16268517884377670660217913)
      ·
        refine ⟨12201388413283252995163435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16268517884377670660217913 12201388413283252995163435)
        ·
          refine ⟨18302082619924879492745153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12201388413283252995163435 18302082619924879492745153)
          ·
            refine ⟨13726561964943659619558865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18302082619924879492745153 13726561964943659619558865)
            ·
              refine ⟨10294921473707744714669149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13726561964943659619558865 10294921473707744714669149)
              ·
                refine ⟨3860595552640404268000931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10294921473707744714669149 3860595552640404268000931)
                ·
                  refine ⟨5790893328960606402001397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860595552640404268000931 5790893328960606402001397)
                  ·
                    refine ⟨542896249590056850187631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5790893328960606402001397 542896249590056850187631)
                    ·
                      rfl

theorem cell22_1585930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1585930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585930 prefixEnd_1585930 := by exact prefixLift 1585930
  have htrace : WordTrace (prefixWord ++ tailWord_1585930) baseStart_1585930 baseEnd_1585930 := by
    simpa [prefixWord, tailWord_1585930, baseEnd_1585930] using wordTrace_append hprefix tailTrace_1585930
  have hstable : (prefixWord ++ tailWord_1585930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585930).length < 2 ^ (prefixWord ++ tailWord_1585930).sum := by decide
  have hdescent : baseEnd_1585930 < baseStart_1585930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585966 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_1585966 : Nat := 118140960795 + 1585966 * 2 ^ 59
def prefixEnd_1585966 : Nat := 4983230072969 + 3 ^ 40 * 1585966 * 2
def baseEnd_1585966 : Nat := 180969524375254918762507

theorem tailTrace_1585966 : CollatzResearch.WordTrace tailWord_1585966 prefixEnd_1585966 180969524375254918762507 := by
  unfold tailWord_1585966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230616521540439784191219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38563288114882345515686501 7230616521540439784191219)
  ·
    refine ⟨10845924782310659676286829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7230616521540439784191219 10845924782310659676286829)
    ·
      refine ⟨4067221793366497378607561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10845924782310659676286829 4067221793366497378607561)
      ·
        refine ⟨3050416345024873033955671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067221793366497378607561 3050416345024873033955671)
        ·
          refine ⟨4575624517537309550933507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050416345024873033955671 4575624517537309550933507)
          ·
            refine ⟨6863436776305964326400261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575624517537309550933507 6863436776305964326400261)
            ·
              refine ⟨1286894395557368311200049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6863436776305964326400261 1286894395557368311200049)
              ·
                refine ⟨965170796668026233400037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286894395557368311200049 965170796668026233400037)
                ·
                  refine ⟨180969524375254918762507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965170796668026233400037 180969524375254918762507)
                  ·
                    rfl

theorem cell22_1585966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_1585966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585966 prefixEnd_1585966 := by exact prefixLift 1585966
  have htrace : WordTrace (prefixWord ++ tailWord_1585966) baseStart_1585966 baseEnd_1585966 := by
    simpa [prefixWord, tailWord_1585966, baseEnd_1585966] using wordTrace_append hprefix tailTrace_1585966
  have hstable : (prefixWord ++ tailWord_1585966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585966).length < 2 ^ (prefixWord ++ tailWord_1585966).sum := by decide
  have hdescent : baseEnd_1585966 < baseStart_1585966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585992 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1585992 : Nat := 118140960795 + 1585992 * 2 ^ 59
def prefixEnd_1585992 : Nat := 4983230072969 + 3 ^ 40 * 1585992 * 2
def baseEnd_1585992 : Nat := 542917473457109355137441

theorem tailTrace_1585992 : CollatzResearch.WordTrace tailWord_1585992 prefixEnd_1585992 542917473457109355137441 := by
  unfold tailWord_1585992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28922940235114662356988115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38563920313486216475984153 28922940235114662356988115)
  ·
    refine ⟨43384410352671993535482173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28922940235114662356988115 43384410352671993535482173)
    ·
      refine ⟨16269153882251997575805815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43384410352671993535482173 16269153882251997575805815)
      ·
        refine ⟨24403730823377996363708723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16269153882251997575805815 24403730823377996363708723)
        ·
          refine ⟨36605596235066994545563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24403730823377996363708723 36605596235066994545563085)
          ·
            refine ⟨13727098588150122954586157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36605596235066994545563085 13727098588150122954586157)
            ·
              refine ⟨5147661970556296107969809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13727098588150122954586157 5147661970556296107969809)
              ·
                refine ⟨3860746477917222080977357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147661970556296107969809 3860746477917222080977357)
                ·
                  refine ⟨1447779929218958280366509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3860746477917222080977357 1447779929218958280366509)
                  ·
                    refine ⟨542917473457109355137441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447779929218958280366509 542917473457109355137441)
                    ·
                      rfl

theorem cell22_1585992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1585992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1585992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1585992 prefixEnd_1585992 := by exact prefixLift 1585992
  have htrace : WordTrace (prefixWord ++ tailWord_1585992) baseStart_1585992 baseEnd_1585992 := by
    simpa [prefixWord, tailWord_1585992, baseEnd_1585992] using wordTrace_append hprefix tailTrace_1585992
  have hstable : (prefixWord ++ tailWord_1585992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585992).length < 2 ^ (prefixWord ++ tailWord_1585992).sum := by decide
  have hdescent : baseEnd_1585992 < baseStart_1585992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586005 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1586005 : Nat := 118140960795 + 1586005 * 2 ^ 59
def prefixEnd_1586005 : Nat := 4983230072969 + 3 ^ 40 * 1586005 * 2
def baseEnd_1586005 : Nat := 180973974540927218187467

theorem tailTrace_1586005 : CollatzResearch.WordTrace tailWord_1586005 prefixEnd_1586005 180973974540927218187467 := by
  unfold tailWord_1586005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57846354619182227934199469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38564236412788151956132979 57846354619182227934199469)
  ·
    refine ⟨21692382982193335475324801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57846354619182227934199469 21692382982193335475324801)
    ·
      refine ⟨16269287236645001606493601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21692382982193335475324801 16269287236645001606493601)
      ·
        refine ⟨12201965427483751204870201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16269287236645001606493601 12201965427483751204870201)
        ·
          refine ⟨9151474070612813403652651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12201965427483751204870201 9151474070612813403652651)
          ·
            refine ⟨13727211105919220105478977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151474070612813403652651 13727211105919220105478977)
            ·
              refine ⟨10295408329439415079109233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727211105919220105478977 10295408329439415079109233)
              ·
                refine ⟨7721556247079561309331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10295408329439415079109233 7721556247079561309331925)
                ·
                  refine ⟨180973974540927218187467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7721556247079561309331925 180973974540927218187467)
                  ·
                    rfl

theorem cell22_1586005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1586005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586005 prefixEnd_1586005 := by exact prefixLift 1586005
  have htrace : WordTrace (prefixWord ++ tailWord_1586005) baseStart_1586005 baseEnd_1586005 := by
    simpa [prefixWord, tailWord_1586005, baseEnd_1586005] using wordTrace_append hprefix tailTrace_1586005
  have hstable : (prefixWord ++ tailWord_1586005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586005).length < 2 ^ (prefixWord ++ tailWord_1586005).sum := by decide
  have hdescent : baseEnd_1586005 < baseStart_1586005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586009 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 1, 3]
def baseStart_1586009 : Nat := 118140960795 + 1586009 * 2 ^ 59
def prefixEnd_1586009 : Nat := 4983230072969 + 3 ^ 40 * 1586009 * 2
def baseEnd_1586009 : Nat := 542923292904526977462389

theorem tailTrace_1586009 : CollatzResearch.WordTrace tailWord_1586009 prefixEnd_1586009 542923292904526977462389 := by
  unfold tailWord_1586009
  simp only [CollatzResearch.WordTrace]
  refine ⟨57846500511167736617345081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38564333674111824411563387 57846500511167736617345081)
  ·
    refine ⟨43384875383375802463008811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57846500511167736617345081 43384875383375802463008811)
    ·
      refine ⟨65077313075063703694513217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43384875383375802463008811 65077313075063703694513217)
      ·
        refine ⟨48807984806297777770884913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65077313075063703694513217 48807984806297777770884913)
        ·
          refine ⟨36605988604723333328163685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48807984806297777770884913 36605988604723333328163685)
          ·
            refine ⟨6863622863385624999030691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36605988604723333328163685 6863622863385624999030691)
            ·
              refine ⟨10295434295078437498546037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863622863385624999030691 10295434295078437498546037)
              ·
                refine ⟨965196965163603515488691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10295434295078437498546037 965196965163603515488691)
                ·
                  refine ⟨1447795447745405273233037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965196965163603515488691 1447795447745405273233037)
                  ·
                    refine ⟨542923292904526977462389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447795447745405273233037 542923292904526977462389)
                    ·
                      rfl

theorem cell22_1586009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 3].length) (baseStart_1586009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586009 prefixEnd_1586009 := by exact prefixLift 1586009
  have htrace : WordTrace (prefixWord ++ tailWord_1586009) baseStart_1586009 baseEnd_1586009 := by
    simpa [prefixWord, tailWord_1586009, baseEnd_1586009] using wordTrace_append hprefix tailTrace_1586009
  have hstable : (prefixWord ++ tailWord_1586009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586009).length < 2 ^ (prefixWord ++ tailWord_1586009).sum := by decide
  have hdescent : baseEnd_1586009 < baseStart_1586009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586035 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_1586035 : Nat := 118140960795 + 1586035 * 2 ^ 59
def prefixEnd_1586035 : Nat := 4983230072969 + 3 ^ 40 * 1586035 * 2
def baseEnd_1586035 : Nat := 542932193235871576312309

theorem tailTrace_1586035 : CollatzResearch.WordTrace tailWord_1586035 prefixEnd_1586035 542932193235871576312309 := by
  unfold tailWord_1586035
  simp only [CollatzResearch.WordTrace]
  refine ⟨57847448809073543057791559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38564965872715695371861039 57847448809073543057791559)
  ·
    refine ⟨86771173213610314586687339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57847448809073543057791559 86771173213610314586687339)
    ·
      refine ⟨130156759820415471880031009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86771173213610314586687339 130156759820415471880031009)
      ·
        refine ⟨97617569865311603910023257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130156759820415471880031009 97617569865311603910023257)
        ·
          refine ⟨73213177398983702932517443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97617569865311603910023257 73213177398983702932517443)
          ·
            refine ⟨109819766098475554398776165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73213177398983702932517443 109819766098475554398776165)
            ·
              refine ⟨20591206143464166449770531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109819766098475554398776165 20591206143464166449770531)
              ·
                refine ⟨30886809215196249674655797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20591206143464166449770531 30886809215196249674655797)
                ·
                  refine ⟨2895638363924648406998981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30886809215196249674655797 2895638363924648406998981)
                  ·
                    refine ⟨542932193235871576312309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895638363924648406998981 542932193235871576312309)
                    ·
                      rfl

theorem cell22_1586035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_1586035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586035 prefixEnd_1586035 := by exact prefixLift 1586035
  have htrace : WordTrace (prefixWord ++ tailWord_1586035) baseStart_1586035 baseEnd_1586035 := by
    simpa [prefixWord, tailWord_1586035, baseEnd_1586035] using wordTrace_append hprefix tailTrace_1586035
  have hstable : (prefixWord ++ tailWord_1586035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586035).length < 2 ^ (prefixWord ++ tailWord_1586035).sum := by decide
  have hdescent : baseEnd_1586035 < baseStart_1586035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586037 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1586037 : Nat := 118140960795 + 1586037 * 2 ^ 59
def prefixEnd_1586037 : Nat := 4983230072969 + 3 ^ 40 * 1586037 * 2
def baseEnd_1586037 : Nat := 542932877876744237762303

theorem tailTrace_1586037 : CollatzResearch.WordTrace tailWord_1586037 prefixEnd_1586037 542932877876744237762303 := by
  unfold tailWord_1586037
  simp only [CollatzResearch.WordTrace]
  refine ⟨57847521755066297399364365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565014503377531599576243 57847521755066297399364365)
  ·
    refine ⟨21692820658149861524761637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57847521755066297399364365 21692820658149861524761637)
    ·
      refine ⟨4067403873403099035892807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21692820658149861524761637 4067403873403099035892807)
      ·
        refine ⟨6101105810104648553839211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067403873403099035892807 6101105810104648553839211)
        ·
          refine ⟨9151658715156972830758817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6101105810104648553839211 9151658715156972830758817)
          ·
            refine ⟨6863744036367729623069113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9151658715156972830758817 6863744036367729623069113)
            ·
              refine ⟨5147808027275797217301835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6863744036367729623069113 5147808027275797217301835)
              ·
                refine ⟨7721712040913695825952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147808027275797217301835 7721712040913695825952753)
                ·
                  refine ⟨5791284030685271869464565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721712040913695825952753 5791284030685271869464565)
                  ·
                    refine ⟨542932877876744237762303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791284030685271869464565 542932877876744237762303)
                    ·
                      rfl

theorem cell22_1586037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1586037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586037 prefixEnd_1586037 := by exact prefixLift 1586037
  have htrace : WordTrace (prefixWord ++ tailWord_1586037) baseStart_1586037 baseEnd_1586037 := by
    simpa [prefixWord, tailWord_1586037, baseEnd_1586037] using wordTrace_append hprefix tailTrace_1586037
  have hstable : (prefixWord ++ tailWord_1586037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586037).length < 2 ^ (prefixWord ++ tailWord_1586037).sum := by decide
  have hdescent : baseEnd_1586037 < baseStart_1586037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586065 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1586065 : Nat := 118140960795 + 1586065 * 2 ^ 59
def prefixEnd_1586065 : Nat := 4983230072969 + 3 ^ 40 * 1586065 * 2
def baseEnd_1586065 : Nat := 542942462848961498062217

theorem tailTrace_1586065 : CollatzResearch.WordTrace tailWord_1586065 prefixEnd_1586065 542942462848961498062217 := by
  unfold tailWord_1586065
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848542998964858181383649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565695332643238787589099 57848542998964858181383649)
  ·
    refine ⟨43386407249223643636037737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57848542998964858181383649 43386407249223643636037737)
    ·
      refine ⟨32539805436917732727028303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43386407249223643636037737 32539805436917732727028303)
      ·
        refine ⟨48809708155376599090542455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32539805436917732727028303 48809708155376599090542455)
        ·
          refine ⟨73214562233064898635813683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48809708155376599090542455 73214562233064898635813683)
          ·
            refine ⟨109821843349597347953720525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73214562233064898635813683 109821843349597347953720525)
            ·
              refine ⟨41183191256099005482645197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109821843349597347953720525 41183191256099005482645197)
              ·
                refine ⟨15443696721037127055991949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41183191256099005482645197 15443696721037127055991949)
                ·
                  refine ⟨5791386270388922645996981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15443696721037127055991949 5791386270388922645996981)
                  ·
                    refine ⟨542942462848961498062217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791386270388922645996981 542942462848961498062217)
                    ·
                      rfl

theorem cell22_1586065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1586065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586065 prefixEnd_1586065 := by exact prefixLift 1586065
  have htrace : WordTrace (prefixWord ++ tailWord_1586065) baseStart_1586065 baseEnd_1586065 := by
    simpa [prefixWord, tailWord_1586065, baseEnd_1586065] using wordTrace_append hprefix tailTrace_1586065
  have hstable : (prefixWord ++ tailWord_1586065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586065).length < 2 ^ (prefixWord ++ tailWord_1586065).sum := by decide
  have hdescent : baseEnd_1586065 < baseStart_1586065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586067 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 4]
def baseStart_1586067 : Nat := 118140960795 + 1586067 * 2 ^ 59
def prefixEnd_1586067 : Nat := 4983230072969 + 3 ^ 40 * 1586067 * 2
def baseEnd_1586067 : Nat := 180981049163278053170737

theorem tailTrace_1586067 : CollatzResearch.WordTrace tailWord_1586067 prefixEnd_1586067 180981049163278053170737 := by
  unfold tailWord_1586067
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848615944957612522956455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565743963305075015304303 57848615944957612522956455)
  ·
    refine ⟨86772923917436418784434683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848615944957612522956455 86772923917436418784434683)
    ·
      refine ⟨130159385876154628176652025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86772923917436418784434683 130159385876154628176652025)
      ·
        refine ⟨97619539407115971132489019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130159385876154628176652025 97619539407115971132489019)
        ·
          refine ⟨146429309110673956698733529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97619539407115971132489019 146429309110673956698733529)
          ·
            refine ⟨109821981833005467524050147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146429309110673956698733529 109821981833005467524050147)
            ·
              refine ⟨164732972749508201286075221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109821981833005467524050147 164732972749508201286075221)
              ·
                refine ⟨965232262204149616910597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 164732972749508201286075221 965232262204149616910597)
                ·
                  refine ⟨180981049163278053170737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965232262204149616910597 180981049163278053170737)
                  ·
                    rfl

theorem cell22_1586067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 4].length) (baseStart_1586067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586067 prefixEnd_1586067 := by exact prefixLift 1586067
  have htrace : WordTrace (prefixWord ++ tailWord_1586067) baseStart_1586067 baseEnd_1586067 := by
    simpa [prefixWord, tailWord_1586067, baseEnd_1586067] using wordTrace_append hprefix tailTrace_1586067
  have hstable : (prefixWord ++ tailWord_1586067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586067).length < 2 ^ (prefixWord ++ tailWord_1586067).sum := by decide
  have hdescent : baseEnd_1586067 < baseStart_1586067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586116 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1586116 : Nat := 118140960795 + 1586116 * 2 ^ 59
def prefixEnd_1586116 : Nat := 4983230072969 + 3 ^ 40 * 1586116 * 2
def baseEnd_1586116 : Nat := 542959921191214365037061

theorem tailTrace_1586116 : CollatzResearch.WordTrace tailWord_1586116 prefixEnd_1586116 542959921191214365037061 := by
  unfold tailWord_1586116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28925201560890046945745101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38566935414520062594326801 28925201560890046945745101)
  ·
    refine ⟨10846950585333767604654413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28925201560890046945745101 10846950585333767604654413)
    ·
      refine ⟨4067606469500162851745405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10846950585333767604654413 4067606469500162851745405)
      ·
        refine ⟨1525352426062561069404527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4067606469500162851745405 1525352426062561069404527)
        ·
          refine ⟨2288028639093841604106791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525352426062561069404527 2288028639093841604106791)
          ·
            refine ⟨3432042958640762406160187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288028639093841604106791 3432042958640762406160187)
            ·
              refine ⟨5148064437961143609240281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432042958640762406160187 5148064437961143609240281)
              ·
                refine ⟨3861048328470857706930211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5148064437961143609240281 3861048328470857706930211)
                ·
                  refine ⟨5791572492706286560395317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861048328470857706930211 5791572492706286560395317)
                  ·
                    refine ⟨542959921191214365037061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791572492706286560395317 542959921191214365037061)
                    ·
                      rfl

theorem cell22_1586116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1586116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586116 prefixEnd_1586116 := by exact prefixLift 1586116
  have htrace : WordTrace (prefixWord ++ tailWord_1586116) baseStart_1586116 baseEnd_1586116 := by
    simpa [prefixWord, tailWord_1586116, baseEnd_1586116] using wordTrace_append hprefix tailTrace_1586116
  have hstable : (prefixWord ++ tailWord_1586116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586116).length < 2 ^ (prefixWord ++ tailWord_1586116).sum := by decide
  have hdescent : baseEnd_1586116 < baseStart_1586116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586146 : List Nat := [3, 3, 3, 1, 1, 3, 1, 7]
def baseStart_1586146 : Nat := 118140960795 + 1586146 * 2 ^ 59
def prefixEnd_1586146 : Nat := 4983230072969 + 3 ^ 40 * 1586146 * 2
def baseEnd_1586146 : Nat := 60330021200478254087441

theorem tailTrace_1586146 : CollatzResearch.WordTrace tailWord_1586146 prefixEnd_1586146 60330021200478254087441 := by
  unfold tailWord_1586146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462874327917852253770573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38567664874447606010054861 14462874327917852253770573)
  ·
    refine ⟨5423577872969194595163965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14462874327917852253770573 5423577872969194595163965)
    ·
      refine ⟨2033841702363447973186487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5423577872969194595163965 2033841702363447973186487)
      ·
        refine ⟨3050762553545171959779731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033841702363447973186487 3050762553545171959779731)
        ·
          refine ⟨4576143830317757939669597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050762553545171959779731 4576143830317757939669597)
          ·
            refine ⟨1716053936369159227376099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4576143830317757939669597 1716053936369159227376099)
            ·
              refine ⟨2574080904553738841064149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716053936369159227376099 2574080904553738841064149)
              ·
                refine ⟨60330021200478254087441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2574080904553738841064149 60330021200478254087441)
                ·
                  rfl

theorem cell22_1586146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_1586146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586146 prefixEnd_1586146 := by exact prefixLift 1586146
  have htrace : WordTrace (prefixWord ++ tailWord_1586146) baseStart_1586146 baseEnd_1586146 := by
    simpa [prefixWord, tailWord_1586146, baseEnd_1586146] using wordTrace_append hprefix tailTrace_1586146
  have hstable : (prefixWord ++ tailWord_1586146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586146).length < 2 ^ (prefixWord ++ tailWord_1586146).sum := by decide
  have hdescent : baseEnd_1586146 < baseStart_1586146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586165 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1586165 : Nat := 118140960795 + 1586165 * 2 ^ 59
def prefixEnd_1586165 : Nat := 4983230072969 + 3 ^ 40 * 1586165 * 2
def baseEnd_1586165 : Nat := 542976694892594570561911

theorem tailTrace_1586165 : CollatzResearch.WordTrace tailWord_1586165 prefixEnd_1586165 542976694892594570561911 := by
  unfold tailWord_1586165
  simp only [CollatzResearch.WordTrace]
  refine ⟨57852190298602575260023949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38568126865735050173349299 57852190298602575260023949)
  ·
    refine ⟨21694571361975965722508981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57852190298602575260023949 21694571361975965722508981)
    ·
      refine ⟨2033866065185246786485217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21694571361975965722508981 2033866065185246786485217)
      ·
        refine ⟨1525399548888935089863913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033866065185246786485217 1525399548888935089863913)
        ·
          refine ⟨1144049661666701317397935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525399548888935089863913 1144049661666701317397935)
          ·
            refine ⟨1716074492500051976096903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144049661666701317397935 1716074492500051976096903)
            ·
              refine ⟨2574111738750077964145355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716074492500051976096903 2574111738750077964145355)
              ·
                refine ⟨3861167608125116946218033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574111738750077964145355 3861167608125116946218033)
                ·
                  refine ⟨2895875706093837709663525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861167608125116946218033 2895875706093837709663525)
                  ·
                    refine ⟨542976694892594570561911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895875706093837709663525 542976694892594570561911)
                    ·
                      rfl

theorem cell22_1586165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1586165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586165 prefixEnd_1586165 := by exact prefixLift 1586165
  have htrace : WordTrace (prefixWord ++ tailWord_1586165) baseStart_1586165 baseEnd_1586165 := by
    simpa [prefixWord, tailWord_1586165, baseEnd_1586165] using wordTrace_append hprefix tailTrace_1586165
  have hstable : (prefixWord ++ tailWord_1586165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586165).length < 2 ^ (prefixWord ++ tailWord_1586165).sum := by decide
  have hdescent : baseEnd_1586165 < baseStart_1586165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586208 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_1586208 : Nat := 118140960795 + 1586208 * 2 ^ 59
def prefixEnd_1586208 : Nat := 4983230072969 + 3 ^ 40 * 1586208 * 2
def baseEnd_1586208 : Nat := 180997138223785597245593

theorem tailTrace_1586208 : CollatzResearch.WordTrace tailWord_1586208 prefixEnd_1586208 180997138223785597245593 := by
  unfold tailWord_1586208
  simp only [CollatzResearch.WordTrace]
  refine ⟨28926879318723396801919639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38569172424964529069226185 28926879318723396801919639)
  ·
    refine ⟨43390318978085095202879459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28926879318723396801919639 43390318978085095202879459)
    ·
      refine ⟨65085478467127642804319189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43390318978085095202879459 65085478467127642804319189)
      ·
        refine ⟨1525440901573304128226231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65085478467127642804319189 1525440901573304128226231)
        ·
          refine ⟨2288161352359956192339347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525440901573304128226231 2288161352359956192339347)
          ·
            refine ⟨3432242028539934288509021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288161352359956192339347 3432242028539934288509021)
            ·
              refine ⟨1287090760702475358190883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3432242028539934288509021 1287090760702475358190883)
              ·
                refine ⟨1930636141053713037286325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287090760702475358190883 1930636141053713037286325)
                ·
                  refine ⟨180997138223785597245593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1930636141053713037286325 180997138223785597245593)
                  ·
                    rfl

theorem cell22_1586208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_1586208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586208 prefixEnd_1586208 := by exact prefixLift 1586208
  have htrace : WordTrace (prefixWord ++ tailWord_1586208) baseStart_1586208 baseEnd_1586208 := by
    simpa [prefixWord, tailWord_1586208, baseEnd_1586208] using wordTrace_append hprefix tailTrace_1586208
  have hstable : (prefixWord ++ tailWord_1586208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586208).length < 2 ^ (prefixWord ++ tailWord_1586208).sum := by decide
  have hdescent : baseEnd_1586208 < baseStart_1586208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586234 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_1586234 : Nat := 118140960795 + 1586234 * 2 ^ 59
def prefixEnd_1586234 : Nat := 4983230072969 + 3 ^ 40 * 1586234 * 2
def baseEnd_1586234 : Nat := 543000315002701390586699

theorem tailTrace_1586234 : CollatzResearch.WordTrace tailWord_1586234 prefixEnd_1586234 543000315002701390586699 := by
  unfold tailWord_1586234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463676733838150011071439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38569804623568400029523837 14463676733838150011071439)
  ·
    refine ⟨21695515100757225016607159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14463676733838150011071439 21695515100757225016607159)
    ·
      refine ⟨32543272651135837524910739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21695515100757225016607159 32543272651135837524910739)
      ·
        refine ⟨48814908976703756287366109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32543272651135837524910739 48814908976703756287366109)
        ·
          refine ⟨18305590866263908607762291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48814908976703756287366109 18305590866263908607762291)
          ·
            refine ⟨27458386299395862911643437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18305590866263908607762291 27458386299395862911643437)
            ·
              refine ⟨10296894862273448591866289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27458386299395862911643437 10296894862273448591866289)
              ·
                refine ⟨7722671146705086443899717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296894862273448591866289 7722671146705086443899717)
                ·
                  refine ⟨1448000840007203708231197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7722671146705086443899717 1448000840007203708231197)
                  ·
                    refine ⟨543000315002701390586699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448000840007203708231197 543000315002701390586699)
                    ·
                      rfl

theorem cell22_1586234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_1586234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586234 prefixEnd_1586234 := by exact prefixLift 1586234
  have htrace : WordTrace (prefixWord ++ tailWord_1586234) baseStart_1586234 baseEnd_1586234 := by
    simpa [prefixWord, tailWord_1586234, baseEnd_1586234] using wordTrace_append hprefix tailTrace_1586234
  have hstable : (prefixWord ++ tailWord_1586234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586234).length < 2 ^ (prefixWord ++ tailWord_1586234).sum := by decide
  have hdescent : baseEnd_1586234 < baseStart_1586234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586236 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_1586236 : Nat := 118140960795 + 1586236 * 2 ^ 59
def prefixEnd_1586236 : Nat := 4983230072969 + 3 ^ 40 * 1586236 * 2
def baseEnd_1586236 : Nat := 181000333214524684012231

theorem tailTrace_1586236 : CollatzResearch.WordTrace tailWord_1586236 prefixEnd_1586236 181000333214524684012231 := by
  unfold tailWord_1586236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28927389940672677192929281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38569853254230236257239041 28927389940672677192929281)
  ·
    refine ⟨21695542455504507894696961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28927389940672677192929281 21695542455504507894696961)
    ·
      refine ⟨16271656841628380921022721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21695542455504507894696961 16271656841628380921022721)
      ·
        refine ⟨12203742631221285690767041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16271656841628380921022721 12203742631221285690767041)
        ·
          refine ⟨9152806973415964268075281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12203742631221285690767041 9152806973415964268075281)
          ·
            refine ⟨6864605230061973201056461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152806973415964268075281 6864605230061973201056461)
            ·
              refine ⟨2574226961273239950396173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6864605230061973201056461 2574226961273239950396173)
              ·
                refine ⟨965335110477464981398565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2574226961273239950396173 965335110477464981398565)
                ·
                  refine ⟨181000333214524684012231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965335110477464981398565 181000333214524684012231)
                  ·
                    rfl

theorem cell22_1586236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_1586236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586236 prefixEnd_1586236 := by exact prefixLift 1586236
  have htrace : WordTrace (prefixWord ++ tailWord_1586236) baseStart_1586236 baseEnd_1586236 := by
    simpa [prefixWord, tailWord_1586236, baseEnd_1586236] using wordTrace_append hprefix tailTrace_1586236
  have hstable : (prefixWord ++ tailWord_1586236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586236).length < 2 ^ (prefixWord ++ tailWord_1586236).sum := by decide
  have hdescent : baseEnd_1586236 < baseStart_1586236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586247 : List Nat := [1, 1, 4, 1, 3, 2, 10]
def baseStart_1586247 : Nat := 118140960795 + 1586247 * 2 ^ 59
def prefixEnd_1586247 : Nat := 4983230072969 + 3 ^ 40 * 1586247 * 2
def baseEnd_1586247 : Nat := 20111287598828655185617

theorem tailTrace_1586247 : CollatzResearch.WordTrace tailWord_1586247 prefixEnd_1586247 20111287598828655185617 := by
  unfold tailWord_1586247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855181084305503264508995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38570120722870335509672663 57855181084305503264508995)
  ·
    refine ⟨86782771626458254896763493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57855181084305503264508995 86782771626458254896763493)
    ·
      refine ⟨16271769679960922793143155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86782771626458254896763493 16271769679960922793143155)
      ·
        refine ⟨24407654519941384189714733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16271769679960922793143155 24407654519941384189714733)
        ·
          refine ⟨9152870444978019071143025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24407654519941384189714733 9152870444978019071143025)
          ·
            refine ⟨6864652833733514303357269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152870444978019071143025 6864652833733514303357269)
            ·
              refine ⟨20111287598828655185617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6864652833733514303357269 20111287598828655185617)
              ·
                rfl

theorem cell22_1586247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 10].length) (baseStart_1586247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586247 prefixEnd_1586247 := by exact prefixLift 1586247
  have htrace : WordTrace (prefixWord ++ tailWord_1586247) baseStart_1586247 baseEnd_1586247 := by
    simpa [prefixWord, tailWord_1586247, baseEnd_1586247] using wordTrace_append hprefix tailTrace_1586247
  have hstable : (prefixWord ++ tailWord_1586247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586247).length < 2 ^ (prefixWord ++ tailWord_1586247).sum := by decide
  have hdescent : baseEnd_1586247 < baseStart_1586247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586313 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_1586313 : Nat := 118140960795 + 1586313 * 2 ^ 59
def prefixEnd_1586313 : Nat := 4983230072969 + 3 ^ 40 * 1586313 * 2
def baseEnd_1586313 : Nat := 543027358317171517861457

theorem tailTrace_1586313 : CollatzResearch.WordTrace tailWord_1586313 prefixEnd_1586313 543027358317171517861457 := by
  unfold tailWord_1586313
  simp only [CollatzResearch.WordTrace]
  refine ⟨57857588302066396536411593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38571725534710931024274395 57857588302066396536411593)
  ·
    refine ⟨43393191226549797402308695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57857588302066396536411593 43393191226549797402308695)
    ·
      refine ⟨65089786839824696103463043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43393191226549797402308695 65089786839824696103463043)
      ·
        refine ⟨97634680259737044155194565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65089786839824696103463043 97634680259737044155194565)
        ·
          refine ⟨18306502548700695779098981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97634680259737044155194565 18306502548700695779098981)
          ·
            refine ⟨3432469227881380458581059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18306502548700695779098981 3432469227881380458581059)
            ·
              refine ⟨5148703841822070687871589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432469227881380458581059 5148703841822070687871589)
              ·
                refine ⟨965381970341638253975923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5148703841822070687871589 965381970341638253975923)
                ·
                  refine ⟨1448072955512457380963885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965381970341638253975923 1448072955512457380963885)
                  ·
                    refine ⟨543027358317171517861457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448072955512457380963885 543027358317171517861457)
                    ·
                      rfl

theorem cell22_1586313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_1586313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586313 prefixEnd_1586313 := by exact prefixLift 1586313
  have htrace : WordTrace (prefixWord ++ tailWord_1586313) baseStart_1586313 baseEnd_1586313 := by
    simpa [prefixWord, tailWord_1586313, baseEnd_1586313] using wordTrace_append hprefix tailTrace_1586313
  have hstable : (prefixWord ++ tailWord_1586313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586313).length < 2 ^ (prefixWord ++ tailWord_1586313).sum := by decide
  have hdescent : baseEnd_1586313 < baseStart_1586313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586405 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 4]
def baseStart_1586405 : Nat := 118140960795 + 1586405 * 2 ^ 59
def prefixEnd_1586405 : Nat := 4983230072969 + 3 ^ 40 * 1586405 * 2
def baseEnd_1586405 : Nat := 181019617265771314853725

theorem tailTrace_1586405 : CollatzResearch.WordTrace tailWord_1586405 prefixEnd_1586405 181019617265771314853725 := by
  unfold tailWord_1586405
  simp only [CollatzResearch.WordTrace]
  refine ⟨57860943817733096248760669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38573962545155397499173779 57860943817733096248760669)
  ·
    refine ⟨21697853931649911093285251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57860943817733096248760669 21697853931649911093285251)
    ·
      refine ⟨32546780897474866639927877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21697853931649911093285251 32546780897474866639927877)
      ·
        refine ⟨6102521418276537494986477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32546780897474866639927877 6102521418276537494986477)
        ·
          refine ⟨2288445531853701560619929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6102521418276537494986477 2288445531853701560619929)
          ·
            refine ⟨1716334148890276170464947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288445531853701560619929 1716334148890276170464947)
            ·
              refine ⟨2574501223335414255697421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716334148890276170464947 2574501223335414255697421)
              ·
                refine ⟨965437958750780345886533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2574501223335414255697421 965437958750780345886533)
                ·
                  refine ⟨181019617265771314853725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965437958750780345886533 181019617265771314853725)
                  ·
                    rfl

theorem cell22_1586405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_1586405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586405 prefixEnd_1586405 := by exact prefixLift 1586405
  have htrace : WordTrace (prefixWord ++ tailWord_1586405) baseStart_1586405 baseEnd_1586405 := by
    simpa [prefixWord, tailWord_1586405, baseEnd_1586405] using wordTrace_append hprefix tailTrace_1586405
  have hstable : (prefixWord ++ tailWord_1586405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586405).length < 2 ^ (prefixWord ++ tailWord_1586405).sum := by decide
  have hdescent : baseEnd_1586405 < baseStart_1586405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586418 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1586418 : Nat := 118140960795 + 1586418 * 2 ^ 59
def prefixEnd_1586418 : Nat := 4983230072969 + 3 ^ 40 * 1586418 * 2
def baseEnd_1586418 : Nat := 543063301962986243986135

theorem tailTrace_1586418 : CollatzResearch.WordTrace tailWord_1586418 prefixEnd_1586418 543063301962986243986135 := by
  unfold tailWord_1586418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465354491671499867245977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38574278644457332979322605 14465354491671499867245977)
  ·
    refine ⟨10849015868753624900434483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14465354491671499867245977 10849015868753624900434483)
    ·
      refine ⟨16273523803130437350651725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849015868753624900434483 16273523803130437350651725)
      ·
        refine ⟨6102571426173914006494397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16273523803130437350651725 6102571426173914006494397)
        ·
          refine ⟨2288464284815217752435399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6102571426173914006494397 2288464284815217752435399)
          ·
            refine ⟨3432696427222826628653099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288464284815217752435399 3432696427222826628653099)
            ·
              refine ⟨5149044640834239942979649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432696427222826628653099 5149044640834239942979649)
              ·
                refine ⟨3861783480625679957234737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149044640834239942979649 3861783480625679957234737)
                ·
                  refine ⟨2896337610469259967926053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861783480625679957234737 2896337610469259967926053)
                  ·
                    refine ⟨543063301962986243986135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896337610469259967926053 543063301962986243986135)
                    ·
                      rfl

theorem cell22_1586418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1586418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586418 prefixEnd_1586418 := by exact prefixLift 1586418
  have htrace : WordTrace (prefixWord ++ tailWord_1586418) baseStart_1586418 baseEnd_1586418 := by
    simpa [prefixWord, tailWord_1586418, baseEnd_1586418] using wordTrace_append hprefix tailTrace_1586418
  have hstable : (prefixWord ++ tailWord_1586418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586418).length < 2 ^ (prefixWord ++ tailWord_1586418).sum := by decide
  have hdescent : baseEnd_1586418 < baseStart_1586418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586459 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_1586459 : Nat := 118140960795 + 1586459 * 2 ^ 59
def prefixEnd_1586459 : Nat := 4983230072969 + 3 ^ 40 * 1586459 * 2
def baseEnd_1586459 : Nat := 543077337100875803711009

theorem tailTrace_1586459 : CollatzResearch.WordTrace tailWord_1586459 prefixEnd_1586459 543077337100875803711009 := by
  unfold tailWord_1586459
  simp only [CollatzResearch.WordTrace]
  refine ⟨57862913359537463471226431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38575275573024975647484287 57862913359537463471226431)
  ·
    refine ⟨86794370039306195206839647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57862913359537463471226431 86794370039306195206839647)
    ·
      refine ⟨130191555058959292810259471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86794370039306195206839647 130191555058959292810259471)
      ·
        refine ⟨195287332588438939215389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130191555058959292810259471 195287332588438939215389207)
        ·
          refine ⟨292930998882658408823083811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195287332588438939215389207 292930998882658408823083811)
          ·
            refine ⟨439396498323987613234625717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292930998882658408823083811 439396498323987613234625717)
            ·
              refine ⟨41193421717873838740746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439396498323987613234625717 41193421717873838740746161)
              ·
                refine ⟨30895066288405379055559621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41193421717873838740746161 30895066288405379055559621)
                ·
                  refine ⟨5792824929076008572917429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30895066288405379055559621 5792824929076008572917429)
                  ·
                    refine ⟨543077337100875803711009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5792824929076008572917429 543077337100875803711009)
                    ·
                      rfl

theorem cell22_1586459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_1586459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586459 prefixEnd_1586459 := by exact prefixLift 1586459
  have htrace : WordTrace (prefixWord ++ tailWord_1586459) baseStart_1586459 baseEnd_1586459 := by
    simpa [prefixWord, tailWord_1586459, baseEnd_1586459] using wordTrace_append hprefix tailTrace_1586459
  have hstable : (prefixWord ++ tailWord_1586459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586459).length < 2 ^ (prefixWord ++ tailWord_1586459).sum := by decide
  have hdescent : baseEnd_1586459 < baseStart_1586459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586482 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_1586482 : Nat := 118140960795 + 1586482 * 2 ^ 59
def prefixEnd_1586482 : Nat := 4983230072969 + 3 ^ 40 * 1586482 * 2
def baseEnd_1586482 : Nat := 543085210470911410385939

theorem tailTrace_1586482 : CollatzResearch.WordTrace tailWord_1586482 prefixEnd_1586482 543085210470911410385939 := by
  unfold tailWord_1586482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465938059613534599828425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38575834825636092266209133 14465938059613534599828425)
  ·
    refine ⟨10849453544710150949871319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14465938059613534599828425 10849453544710150949871319)
    ·
      refine ⟨16274180317065226424806979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849453544710150949871319 16274180317065226424806979)
      ·
        refine ⟨24411270475597839637210469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16274180317065226424806979 24411270475597839637210469)
        ·
          refine ⟨4577113214174594931976963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24411270475597839637210469 4577113214174594931976963)
          ·
            refine ⟨6865669821261892397965445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577113214174594931976963 6865669821261892397965445)
            ·
              refine ⟨1287313091486604824618521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6865669821261892397965445 1287313091486604824618521)
              ·
                refine ⟨965484818614953618463891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287313091486604824618521 965484818614953618463891)
                ·
                  refine ⟨1448227227922430427695837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965484818614953618463891 1448227227922430427695837)
                  ·
                    refine ⟨543085210470911410385939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448227227922430427695837 543085210470911410385939)
                    ·
                      rfl

theorem cell22_1586482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_1586482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586482 prefixEnd_1586482 := by exact prefixLift 1586482
  have htrace : WordTrace (prefixWord ++ tailWord_1586482) baseStart_1586482 baseEnd_1586482 := by
    simpa [prefixWord, tailWord_1586482, baseEnd_1586482] using wordTrace_append hprefix tailTrace_1586482
  have hstable : (prefixWord ++ tailWord_1586482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586482).length < 2 ^ (prefixWord ++ tailWord_1586482).sum := by decide
  have hdescent : baseEnd_1586482 < baseStart_1586482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586521 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_1586521 : Nat := 118140960795 + 1586521 * 2 ^ 59
def prefixEnd_1586521 : Nat := 4983230072969 + 3 ^ 40 * 1586521 * 2
def baseEnd_1586521 : Nat := 543098560967928308660819

theorem tailTrace_1586521 : CollatzResearch.WordTrace tailWord_1586521 prefixEnd_1586521 543098560967928308660819 := by
  unfold tailWord_1586521
  simp only [CollatzResearch.WordTrace]
  refine ⟨57865174685312848059983417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38576783123541898706655611 57865174685312848059983417)
  ·
    refine ⟨43398881013984636044987563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57865174685312848059983417 43398881013984636044987563)
    ·
      refine ⟨65098321520976954067481345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43398881013984636044987563 65098321520976954067481345)
      ·
        refine ⟨48823741140732715550611009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65098321520976954067481345 48823741140732715550611009)
        ·
          refine ⟨36617805855549536662958257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48823741140732715550611009 36617805855549536662958257)
          ·
            refine ⟨27463354391662152497218693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36617805855549536662958257 27463354391662152497218693)
            ·
              refine ⟨5149378948436653593228505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27463354391662152497218693 5149378948436653593228505)
              ·
                refine ⟨3862034211327490194921379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149378948436653593228505 3862034211327490194921379)
                ·
                  refine ⟨5793051316991235292382069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862034211327490194921379 5793051316991235292382069)
                  ·
                    refine ⟨543098560967928308660819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5793051316991235292382069 543098560967928308660819)
                    ·
                      rfl

theorem cell22_1586521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_1586521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586521 prefixEnd_1586521 := by exact prefixLift 1586521
  have htrace : WordTrace (prefixWord ++ tailWord_1586521) baseStart_1586521 baseEnd_1586521 := by
    simpa [prefixWord, tailWord_1586521, baseEnd_1586521] using wordTrace_append hprefix tailTrace_1586521
  have hstable : (prefixWord ++ tailWord_1586521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586521).length < 2 ^ (prefixWord ++ tailWord_1586521).sum := by decide
  have hdescent : baseEnd_1586521 < baseStart_1586521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586555 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 2, 3]
def baseStart_1586555 : Nat := 118140960795 + 1586555 * 2 ^ 59
def prefixEnd_1586555 : Nat := 4983230072969 + 3 ^ 40 * 1586555 * 2
def baseEnd_1586555 : Nat := 543110199862763553310715

theorem tailTrace_1586555 : CollatzResearch.WordTrace tailWord_1586555 prefixEnd_1586555 543110199862763553310715 := by
  unfold tailWord_1586555
  simp only [CollatzResearch.WordTrace]
  refine ⟨57866414767189671866721119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38577609844793114577814079 57866414767189671866721119)
  ·
    refine ⟨86799622150784507800081679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57866414767189671866721119 86799622150784507800081679)
    ·
      refine ⟨130199433226176761700122519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86799622150784507800081679 130199433226176761700122519)
      ·
        refine ⟨195299149839265142550183779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130199433226176761700122519 195299149839265142550183779)
        ·
          refine ⟨292948724758897713825275669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195299149839265142550183779 292948724758897713825275669)
          ·
            refine ⟨13731971473073330335559797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292948724758897713825275669 13731971473073330335559797)
            ·
              refine ⟨1287372325600624718958731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13731971473073330335559797 1287372325600624718958731)
              ·
                refine ⟨1931058488400937078438097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287372325600624718958731 1931058488400937078438097)
                ·
                  refine ⟨1448293866300702808828573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931058488400937078438097 1448293866300702808828573)
                  ·
                    refine ⟨543110199862763553310715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448293866300702808828573 543110199862763553310715)
                    ·
                      rfl

theorem cell22_1586555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 2, 3].length) (baseStart_1586555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586555 prefixEnd_1586555 := by exact prefixLift 1586555
  have htrace : WordTrace (prefixWord ++ tailWord_1586555) baseStart_1586555 baseEnd_1586555 := by
    simpa [prefixWord, tailWord_1586555, baseEnd_1586555] using wordTrace_append hprefix tailTrace_1586555
  have hstable : (prefixWord ++ tailWord_1586555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586555).length < 2 ^ (prefixWord ++ tailWord_1586555).sum := by decide
  have hdescent : baseEnd_1586555 < baseStart_1586555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586568 : List Nat := [2, 1, 3, 3, 1, 2, 4, 6]
def baseStart_1586568 : Nat := 118140960795 + 1586568 * 2 ^ 59
def prefixEnd_1586568 : Nat := 4983230072969 + 3 ^ 40 * 1586568 * 2
def baseEnd_1586568 : Nat := 60346072225381761415075

theorem tailTrace_1586568 : CollatzResearch.WordTrace tailWord_1586568 prefixEnd_1586568 60346072225381761415075 := by
  unfold tailWord_1586568
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933444458071287543472179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38577925944095050057962905 28933444458071287543472179)
  ·
    refine ⟨43400166687106931315208269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28933444458071287543472179 43400166687106931315208269)
    ·
      refine ⟨16275062507665099243203101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43400166687106931315208269 16275062507665099243203101)
      ·
        refine ⟨6103148440374412216201163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16275062507665099243203101 6103148440374412216201163)
        ·
          refine ⟨9154722660561618324301745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103148440374412216201163 9154722660561618324301745)
          ·
            refine ⟨6866041995421213743226309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154722660561618324301745 6866041995421213743226309)
            ·
              refine ⟨1287382874141477576854933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6866041995421213743226309 1287382874141477576854933)
              ·
                refine ⟨60346072225381761415075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1287382874141477576854933 60346072225381761415075)
                ·
                  rfl

theorem cell22_1586568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_1586568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586568 prefixEnd_1586568 := by exact prefixLift 1586568
  have htrace : WordTrace (prefixWord ++ tailWord_1586568) baseStart_1586568 baseEnd_1586568 := by
    simpa [prefixWord, tailWord_1586568, baseEnd_1586568] using wordTrace_append hprefix tailTrace_1586568
  have hstable : (prefixWord ++ tailWord_1586568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586568).length < 2 ^ (prefixWord ++ tailWord_1586568).sum := by decide
  have hdescent : baseEnd_1586568 < baseStart_1586568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586574 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_1586574 : Nat := 118140960795 + 1586574 * 2 ^ 59
def prefixEnd_1586574 : Nat := 4983230072969 + 3 ^ 40 * 1586574 * 2
def baseEnd_1586574 : Nat := 181038901317017945695219

theorem tailTrace_1586574 : CollatzResearch.WordTrace tailWord_1586574 prefixEnd_1586574 181038901317017945695219 := by
  unfold tailWord_1586574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233388469265104763957847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38578071836080558741108517 7233388469265104763957847)
  ·
    refine ⟨10850082703897657145936771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233388469265104763957847 10850082703897657145936771)
    ·
      refine ⟨16275124055846485718905157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850082703897657145936771 16275124055846485718905157)
      ·
        refine ⟨3051585760471216072294717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16275124055846485718905157 3051585760471216072294717)
        ·
          refine ⟨1144344660176706027110519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3051585760471216072294717 1144344660176706027110519)
          ·
            refine ⟨1716516990265059040665779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144344660176706027110519 1716516990265059040665779)
            ·
              refine ⟨2574775485397588560998669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716516990265059040665779 2574775485397588560998669)
              ·
                refine ⟨965540807024095710374501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2574775485397588560998669 965540807024095710374501)
                ·
                  refine ⟨181038901317017945695219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965540807024095710374501 181038901317017945695219)
                  ·
                    rfl

theorem cell22_1586574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_1586574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586574 prefixEnd_1586574 := by exact prefixLift 1586574
  have htrace : WordTrace (prefixWord ++ tailWord_1586574) baseStart_1586574 baseEnd_1586574 := by
    simpa [prefixWord, tailWord_1586574, baseEnd_1586574] using wordTrace_append hprefix tailTrace_1586574
  have hstable : (prefixWord ++ tailWord_1586574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586574).length < 2 ^ (prefixWord ++ tailWord_1586574).sum := by decide
  have hdescent : baseEnd_1586574 < baseStart_1586574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586611 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_1586611 : Nat := 118140960795 + 1586611 * 2 ^ 59
def prefixEnd_1586611 : Nat := 4983230072969 + 3 ^ 40 * 1586611 * 2
def baseEnd_1586611 : Nat := 543129369807198073910543

theorem tailTrace_1586611 : CollatzResearch.WordTrace tailWord_1586611 prefixEnd_1586611 543129369807198073910543 := by
  unfold tailWord_1586611
  simp only [CollatzResearch.WordTrace]
  refine ⟨57868457254986793430759687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38578971503324528953839791 57868457254986793430759687)
  ·
    refine ⟨86802685882480190146139531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57868457254986793430759687 86802685882480190146139531)
    ·
      refine ⟨130204028823720285219209297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86802685882480190146139531 130204028823720285219209297)
      ·
        refine ⟨97653021617790213914406973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130204028823720285219209297 97653021617790213914406973)
        ·
          refine ⟨36619883106671330217902615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97653021617790213914406973 36619883106671330217902615)
          ·
            refine ⟨54929824660006995326853923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36619883106671330217902615 54929824660006995326853923)
            ·
              refine ⟨82394736990010492990280885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54929824660006995326853923 82394736990010492990280885)
              ·
                refine ⟨7724506592813483717838833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82394736990010492990280885 7724506592813483717838833)
                ·
                  refine ⟨5793379944610112788379125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7724506592813483717838833 5793379944610112788379125)
                  ·
                    refine ⟨543129369807198073910543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5793379944610112788379125 543129369807198073910543)
                    ·
                      rfl

theorem cell22_1586611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_1586611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586611 prefixEnd_1586611 := by exact prefixLift 1586611
  have htrace : WordTrace (prefixWord ++ tailWord_1586611) baseStart_1586611 baseEnd_1586611 := by
    simpa [prefixWord, tailWord_1586611, baseEnd_1586611] using wordTrace_append hprefix tailTrace_1586611
  have hstable : (prefixWord ++ tailWord_1586611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586611).length < 2 ^ (prefixWord ++ tailWord_1586611).sum := by decide
  have hdescent : baseEnd_1586611 < baseStart_1586611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586673 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1586673 : Nat := 118140960795 + 1586673 * 2 ^ 59
def prefixEnd_1586673 : Nat := 4983230072969 + 3 ^ 40 * 1586673 * 2
def baseEnd_1586673 : Nat := 543150593674250578860353

theorem tailTrace_1586673 : CollatzResearch.WordTrace tailWord_1586673 prefixEnd_1586673 543150593674250578860353 := by
  unfold tailWord_1586673
  simp only [CollatzResearch.WordTrace]
  refine ⟨57870718580762178019516673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38580479053841452013011115 57870718580762178019516673)
  ·
    refine ⟨43403038935571633514637505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57870718580762178019516673 43403038935571633514637505)
    ·
      refine ⟨32552279201678725135978129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43403038935571633514637505 32552279201678725135978129)
      ·
        refine ⟨24414209401259043851983597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32552279201678725135978129 24414209401259043851983597)
        ·
          refine ⟨9155328525472141444493849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24414209401259043851983597 9155328525472141444493849)
          ·
            refine ⟨6866496394104106083370387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155328525472141444493849 6866496394104106083370387)
            ·
              refine ⟨10299744591156159125055581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866496394104106083370387 10299744591156159125055581)
              ·
                refine ⟨3862404221683559671895843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10299744591156159125055581 3862404221683559671895843)
                ·
                  refine ⟨5793606332525339507843765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862404221683559671895843 5793606332525339507843765)
                  ·
                    refine ⟨543150593674250578860353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5793606332525339507843765 543150593674250578860353)
                    ·
                      rfl

theorem cell22_1586673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1586673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586673 prefixEnd_1586673 := by exact prefixLift 1586673
  have htrace : WordTrace (prefixWord ++ tailWord_1586673) baseStart_1586673 baseEnd_1586673 := by
    simpa [prefixWord, tailWord_1586673, baseEnd_1586673] using wordTrace_append hprefix tailTrace_1586673
  have hstable : (prefixWord ++ tailWord_1586673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586673).length < 2 ^ (prefixWord ++ tailWord_1586673).sum := by decide
  have hdescent : baseEnd_1586673 < baseStart_1586673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586707 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 2, 3]
def baseStart_1586707 : Nat := 118140960795 + 1586707 * 2 ^ 59
def prefixEnd_1586707 : Nat := 4983230072969 + 3 ^ 40 * 1586707 * 2
def baseEnd_1586707 : Nat := 543162232569085823510249

theorem tailTrace_1586707 : CollatzResearch.WordTrace tailWord_1586707 prefixEnd_1586707 543162232569085823510249 := by
  unfold tailWord_1586707
  simp only [CollatzResearch.WordTrace]
  refine ⟨57871958662639001826254375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38581305775092667884169583 57871958662639001826254375)
  ·
    refine ⟨86807937993958502739381563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57871958662639001826254375 86807937993958502739381563)
    ·
      refine ⟨130211906990937754109072345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86807937993958502739381563 130211906990937754109072345)
      ·
        refine ⟨97658930243203315581804259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130211906990937754109072345 97658930243203315581804259)
        ·
          refine ⟨146488395364804973372706389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97658930243203315581804259 146488395364804973372706389)
          ·
            refine ⟨1716660883181308281711403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 146488395364804973372706389 1716660883181308281711403)
            ·
              refine ⟨2574991324771962422567105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716660883181308281711403 2574991324771962422567105)
              ·
                refine ⟨1931243493578971816925329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574991324771962422567105 1931243493578971816925329)
                ·
                  refine ⟨1448432620184228862693997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931243493578971816925329 1448432620184228862693997)
                  ·
                    refine ⟨543162232569085823510249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448432620184228862693997 543162232569085823510249)
                    ·
                      rfl

theorem cell22_1586707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].length) (baseStart_1586707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586707 prefixEnd_1586707 := by exact prefixLift 1586707
  have htrace : WordTrace (prefixWord ++ tailWord_1586707) baseStart_1586707 baseEnd_1586707 := by
    simpa [prefixWord, tailWord_1586707, baseEnd_1586707] using wordTrace_append hprefix tailTrace_1586707
  have hstable : (prefixWord ++ tailWord_1586707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586707).length < 2 ^ (prefixWord ++ tailWord_1586707).sum := by decide
  have hdescent : baseEnd_1586707 < baseStart_1586707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586769 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_1586769 : Nat := 118140960795 + 1586769 * 2 ^ 59
def prefixEnd_1586769 : Nat := 4983230072969 + 3 ^ 40 * 1586769 * 2
def baseEnd_1586769 : Nat := 543183456436138328460059

theorem tailTrace_1586769 : CollatzResearch.WordTrace tailWord_1586769 prefixEnd_1586769 543183456436138328460059 := by
  unfold tailWord_1586769
  simp only [CollatzResearch.WordTrace]
  refine ⟨57874219988414386415011361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38582813325609590943340907 57874219988414386415011361)
  ·
    refine ⟨43405664991310789811258521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57874219988414386415011361 43405664991310789811258521)
    ·
      refine ⟨32554248743483092358443891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43405664991310789811258521 32554248743483092358443891)
      ·
        refine ⟨48831373115224638537665837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32554248743483092358443891 48831373115224638537665837)
        ·
          refine ⟨18311764918209239451624689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48831373115224638537665837 18311764918209239451624689)
          ·
            refine ⟨13733823688656929588718517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18311764918209239451624689 13733823688656929588718517)
            ·
              refine ⟨1287545970811587148942361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13733823688656929588718517 1287545970811587148942361)
              ·
                refine ⟨965659478108690361706771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287545970811587148942361 965659478108690361706771)
                ·
                  refine ⟨1448489217163035542560157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965659478108690361706771 1448489217163035542560157)
                  ·
                    refine ⟨543183456436138328460059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448489217163035542560157 543183456436138328460059)
                    ·
                      rfl

theorem cell22_1586769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_1586769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586769 prefixEnd_1586769 := by exact prefixLift 1586769
  have htrace : WordTrace (prefixWord ++ tailWord_1586769) baseStart_1586769 baseEnd_1586769 := by
    simpa [prefixWord, tailWord_1586769, baseEnd_1586769] using wordTrace_append hprefix tailTrace_1586769
  have hstable : (prefixWord ++ tailWord_1586769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586769).length < 2 ^ (prefixWord ++ tailWord_1586769).sum := by decide
  have hdescent : baseEnd_1586769 < baseStart_1586769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586793 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 6]
def baseStart_1586793 : Nat := 118140960795 + 1586793 * 2 ^ 59
def prefixEnd_1586793 : Nat := 4983230072969 + 3 ^ 40 * 1586793 * 2
def baseEnd_1586793 : Nat := 181063890708870088619995

theorem tailTrace_1586793 : CollatzResearch.WordTrace tailWord_1586793 prefixEnd_1586793 181063890708870088619995 := by
  unfold tailWord_1586793
  simp only [CollatzResearch.WordTrace]
  refine ⟨57875095340327438513885033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38583396893551625675923355 57875095340327438513885033)
  ·
    refine ⟨43406321505245578885413775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57875095340327438513885033 43406321505245578885413775)
    ·
      refine ⟨65109482257868368328120663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43406321505245578885413775 65109482257868368328120663)
      ·
        refine ⟨97664223386802552492180995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65109482257868368328120663 97664223386802552492180995)
        ·
          refine ⟨146496335080203828738271493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97664223386802552492180995 146496335080203828738271493)
          ·
            refine ⟨27468062827538217888425905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146496335080203828738271493 27468062827538217888425905)
            ·
              refine ⟨20601047120653663416319429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27468062827538217888425905 20601047120653663416319429)
              ·
                refine ⟨3862696335122561890559893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20601047120653663416319429 3862696335122561890559893)
                ·
                  refine ⟨181063890708870088619995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3862696335122561890559893 181063890708870088619995)
                  ·
                    rfl

theorem cell22_1586793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_1586793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586793 prefixEnd_1586793 := by exact prefixLift 1586793
  have htrace : WordTrace (prefixWord ++ tailWord_1586793) baseStart_1586793 baseEnd_1586793 := by
    simpa [prefixWord, tailWord_1586793, baseEnd_1586793] using wordTrace_append hprefix tailTrace_1586793
  have hstable : (prefixWord ++ tailWord_1586793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586793).length < 2 ^ (prefixWord ++ tailWord_1586793).sum := by decide
  have hdescent : baseEnd_1586793 < baseStart_1586793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586825 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_1586825 : Nat := 118140960795 + 1586825 * 2 ^ 59
def prefixEnd_1586825 : Nat := 4983230072969 + 3 ^ 40 * 1586825 * 2
def baseEnd_1586825 : Nat := 543202626380572849059887

theorem tailTrace_1586825 : CollatzResearch.WordTrace tailWord_1586825 prefixEnd_1586825 543202626380572849059887 := by
  unfold tailWord_1586825
  simp only [CollatzResearch.WordTrace]
  refine ⟨57876262476211507979049929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38584174984141005319366619 57876262476211507979049929)
  ·
    refine ⟨43407196857158630984287447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57876262476211507979049929 43407196857158630984287447)
    ·
      refine ⟨65110795285737946476431171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43407196857158630984287447 65110795285737946476431171)
      ·
        refine ⟨97666192928606919714646757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65110795285737946476431171 97666192928606919714646757)
        ·
          refine ⟨18312411174113797446496267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97666192928606919714646757 18312411174113797446496267)
          ·
            refine ⟨27468616761170696169744401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18312411174113797446496267 27468616761170696169744401)
            ·
              refine ⟨20601462570878022127308301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27468616761170696169744401 20601462570878022127308301)
              ·
                refine ⟨7725548464079258297740613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20601462570878022127308301 7725548464079258297740613)
                ·
                  refine ⟨1448540337014860930826365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7725548464079258297740613 1448540337014860930826365)
                  ·
                    refine ⟨543202626380572849059887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448540337014860930826365 543202626380572849059887)
                    ·
                      rfl

theorem cell22_1586825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_1586825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586825 prefixEnd_1586825 := by exact prefixLift 1586825
  have htrace : WordTrace (prefixWord ++ tailWord_1586825) baseStart_1586825 baseEnd_1586825 := by
    simpa [prefixWord, tailWord_1586825, baseEnd_1586825] using wordTrace_append hprefix tailTrace_1586825
  have hstable : (prefixWord ++ tailWord_1586825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586825).length < 2 ^ (prefixWord ++ tailWord_1586825).sum := by decide
  have hdescent : baseEnd_1586825 < baseStart_1586825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586887 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1586887 : Nat := 118140960795 + 1586887 * 2 ^ 59
def prefixEnd_1586887 : Nat := 4983230072969 + 3 ^ 40 * 1586887 * 2
def baseEnd_1586887 : Nat := 543223850247625354009697

theorem tailTrace_1586887 : CollatzResearch.WordTrace tailWord_1586887 prefixEnd_1586887 543223850247625354009697 := by
  unfold tailWord_1586887
  simp only [CollatzResearch.WordTrace]
  refine ⟨57878523801986892567806915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38585682534657928378537943 57878523801986892567806915)
  ·
    refine ⟨86817785702980338851710373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57878523801986892567806915 86817785702980338851710373)
    ·
      refine ⟨16278334819308813534695695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86817785702980338851710373 16278334819308813534695695)
      ·
        refine ⟨24417502228963220302043543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278334819308813534695695 24417502228963220302043543)
        ·
          refine ⟨36626253343444830453065315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24417502228963220302043543 36626253343444830453065315)
          ·
            refine ⟨54939380015167245679597973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36626253343444830453065315 54939380015167245679597973)
            ·
              refine ⟨2575283438210964641231155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54939380015167245679597973 2575283438210964641231155)
              ·
                refine ⟨3862925157316446961846733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575283438210964641231155 3862925157316446961846733)
                ·
                  refine ⟨1448596933993667610692525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3862925157316446961846733 1448596933993667610692525)
                  ·
                    refine ⟨543223850247625354009697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448596933993667610692525 543223850247625354009697)
                    ·
                      rfl

theorem cell22_1586887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1586887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586887 prefixEnd_1586887 := by exact prefixLift 1586887
  have htrace : WordTrace (prefixWord ++ tailWord_1586887) baseStart_1586887 baseEnd_1586887 := by
    simpa [prefixWord, tailWord_1586887, baseEnd_1586887] using wordTrace_append hprefix tailTrace_1586887
  have hstable : (prefixWord ++ tailWord_1586887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586887).length < 2 ^ (prefixWord ++ tailWord_1586887).sum := by decide
  have hdescent : baseEnd_1586887 < baseStart_1586887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586893 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1586893 : Nat := 118140960795 + 1586893 * 2 ^ 59
def prefixEnd_1586893 : Nat := 4983230072969 + 3 ^ 40 * 1586893 * 2
def baseEnd_1586893 : Nat := 543225904170243338359679

theorem tailTrace_1586893 : CollatzResearch.WordTrace tailWord_1586893 prefixEnd_1586893 543225904170243338359679 := by
  unfold tailWord_1586893
  simp only [CollatzResearch.WordTrace]
  refine ⟨57878742639965155592525333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38585828426643437061683555 57878742639965155592525333)
  ·
    refine ⟨2713066061248366668399625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57878742639965155592525333 2713066061248366668399625)
    ·
      refine ⟨2034799545936275001299719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2713066061248366668399625 2034799545936275001299719)
      ·
        refine ⟨3052199318904412501949579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034799545936275001299719 3052199318904412501949579)
        ·
          refine ⟨4578298978356618752924369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052199318904412501949579 4578298978356618752924369)
          ·
            refine ⟨3433724233767464064693277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578298978356618752924369 3433724233767464064693277)
            ·
              refine ⟨1287646587662799024259979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3433724233767464064693277 1287646587662799024259979)
              ·
                refine ⟨1931469881494198536389969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287646587662799024259979 1931469881494198536389969)
                ·
                  refine ⟨1448602411120648902292477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931469881494198536389969 1448602411120648902292477)
                  ·
                    refine ⟨543225904170243338359679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448602411120648902292477 543225904170243338359679)
                    ·
                      rfl

theorem cell22_1586893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1586893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586893 prefixEnd_1586893 := by exact prefixLift 1586893
  have htrace : WordTrace (prefixWord ++ tailWord_1586893) baseStart_1586893 baseEnd_1586893 := by
    simpa [prefixWord, tailWord_1586893, baseEnd_1586893] using wordTrace_append hprefix tailTrace_1586893
  have hstable : (prefixWord ++ tailWord_1586893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586893).length < 2 ^ (prefixWord ++ tailWord_1586893).sum := by decide
  have hdescent : baseEnd_1586893 < baseStart_1586893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586951 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 5]
def baseStart_1586951 : Nat := 118140960795 + 1586951 * 2 ^ 59
def prefixEnd_1586951 : Nat := 4983230072969 + 3 ^ 40 * 1586951 * 2
def baseEnd_1586951 : Nat := 181081919585183506803167

theorem tailTrace_1586951 : CollatzResearch.WordTrace tailWord_1586951 prefixEnd_1586951 181081919585183506803167 := by
  unfold tailWord_1586951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57880858073755031498136707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38587238715836687665424471 57880858073755031498136707)
  ·
    refine ⟨86821287110632547247205061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57880858073755031498136707 86821287110632547247205061)
    ·
      refine ⟨16278991333243602608850949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86821287110632547247205061 16278991333243602608850949)
      ·
        refine ⟨3052310874983175489159553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16278991333243602608850949 3052310874983175489159553)
        ·
          refine ⟨2289233156237381616869665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3052310874983175489159553 2289233156237381616869665)
          ·
            refine ⟨1716924867178036212652249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289233156237381616869665 1716924867178036212652249)
            ·
              refine ⟨1287693650383527159489187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716924867178036212652249 1287693650383527159489187)
              ·
                refine ⟨1931540475575290739233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287693650383527159489187 1931540475575290739233781)
                ·
                  refine ⟨181081919585183506803167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931540475575290739233781 181081919585183506803167)
                  ·
                    rfl

theorem cell22_1586951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 5].length) (baseStart_1586951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586951 prefixEnd_1586951 := by exact prefixLift 1586951
  have htrace : WordTrace (prefixWord ++ tailWord_1586951) baseStart_1586951 baseEnd_1586951 := by
    simpa [prefixWord, tailWord_1586951, baseEnd_1586951] using wordTrace_append hprefix tailTrace_1586951
  have hstable : (prefixWord ++ tailWord_1586951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586951).length < 2 ^ (prefixWord ++ tailWord_1586951).sum := by decide
  have hdescent : baseEnd_1586951 < baseStart_1586951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586977 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1586977 : Nat := 118140960795 + 1586977 * 2 ^ 59
def prefixEnd_1586977 : Nat := 4983230072969 + 3 ^ 40 * 1586977 * 2
def baseEnd_1586977 : Nat := 543254659086895119259421

theorem tailTrace_1586977 : CollatzResearch.WordTrace tailWord_1586977 prefixEnd_1586977 543254659086895119259421 := by
  unfold tailWord_1586977
  simp only [CollatzResearch.WordTrace]
  refine ⟨57881806371660837938583185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38587870914440558625722123 57881806371660837938583185)
  ·
    refine ⟨43411354778745628453937389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57881806371660837938583185 43411354778745628453937389)
    ·
      refine ⟨16279258042029610670226521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43411354778745628453937389 16279258042029610670226521)
      ·
        refine ⟨12209443531522208002669891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16279258042029610670226521 12209443531522208002669891)
        ·
          refine ⟨18314165297283312004004837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12209443531522208002669891 18314165297283312004004837)
          ·
            refine ⟨3433905993240621000750907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18314165297283312004004837 3433905993240621000750907)
            ·
              refine ⟨5150858989860931501126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433905993240621000750907 5150858989860931501126361)
              ·
                refine ⟨3863144242395698625844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150858989860931501126361 3863144242395698625844771)
                ·
                  refine ⟨5794716363593547938767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863144242395698625844771 5794716363593547938767157)
                  ·
                    refine ⟨543254659086895119259421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5794716363593547938767157 543254659086895119259421)
                    ·
                      rfl

theorem cell22_1586977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1586977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586977 prefixEnd_1586977 := by exact prefixLift 1586977
  have htrace : WordTrace (prefixWord ++ tailWord_1586977) baseStart_1586977 baseEnd_1586977 := by
    simpa [prefixWord, tailWord_1586977, baseEnd_1586977] using wordTrace_append hprefix tailTrace_1586977
  have hstable : (prefixWord ++ tailWord_1586977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586977).length < 2 ^ (prefixWord ++ tailWord_1586977).sum := by decide
  have hdescent : baseEnd_1586977 < baseStart_1586977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586994 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1586994 : Nat := 118140960795 + 1586994 * 2 ^ 59
def prefixEnd_1586994 : Nat := 4983230072969 + 3 ^ 40 * 1586994 * 2
def baseEnd_1586994 : Nat := 543260478534312741584369

theorem tailTrace_1586994 : CollatzResearch.WordTrace tailWord_1586994 prefixEnd_1586994 543260478534312741584369 := by
  unfold tailWord_1586994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470606603149812460488009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38588284275066166561301357 14470606603149812460488009)
  ·
    refine ⟨10852954952362359345366007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14470606603149812460488009 10852954952362359345366007)
    ·
      refine ⟨16279432428543539018049011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852954952362359345366007 16279432428543539018049011)
      ·
        refine ⟨24419148642815308527073517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16279432428543539018049011 24419148642815308527073517)
        ·
          refine ⟨9157180741055740697652569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24419148642815308527073517 9157180741055740697652569)
          ·
            refine ⟨6867885555791805523239427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9157180741055740697652569 6867885555791805523239427)
            ·
              refine ⟨10301828333687708284859141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867885555791805523239427 10301828333687708284859141)
              ·
                refine ⟨1931592812566445303411089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10301828333687708284859141 1931592812566445303411089)
                ·
                  refine ⟨1448694609424833977558317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931592812566445303411089 1448694609424833977558317)
                  ·
                    refine ⟨543260478534312741584369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448694609424833977558317 543260478534312741584369)
                    ·
                      rfl

theorem cell22_1586994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1586994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586994 prefixEnd_1586994 := by exact prefixLift 1586994
  have htrace : WordTrace (prefixWord ++ tailWord_1586994) baseStart_1586994 baseEnd_1586994 := by
    simpa [prefixWord, tailWord_1586994, baseEnd_1586994] using wordTrace_append hprefix tailTrace_1586994
  have hstable : (prefixWord ++ tailWord_1586994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586994).length < 2 ^ (prefixWord ++ tailWord_1586994).sum := by decide
  have hdescent : baseEnd_1586994 < baseStart_1586994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586996 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1586996 : Nat := 118140960795 + 1586996 * 2 ^ 59
def prefixEnd_1586996 : Nat := 4983230072969 + 3 ^ 40 * 1586996 * 2
def baseEnd_1586996 : Nat := 181087054391728467678121

theorem tailTrace_1586996 : CollatzResearch.WordTrace tailWord_1586996 prefixEnd_1586996 181087054391728467678121 := by
  unfold tailWord_1586996
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941249679296002091762421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38588332905728002789016561 28941249679296002091762421)
  ·
    refine ⟨2713242157434000196102727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28941249679296002091762421 2713242157434000196102727)
    ·
      refine ⟨4069863236151000294154091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713242157434000196102727 4069863236151000294154091)
      ·
        refine ⟨6104794854226500441231137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069863236151000294154091 6104794854226500441231137)
        ·
          refine ⟨4578596140669875330923353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104794854226500441231137 4578596140669875330923353)
          ·
            refine ⟨3433947105502406498192515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578596140669875330923353 3433947105502406498192515)
            ·
              refine ⟨5150920658253609747288773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433947105502406498192515 5150920658253609747288773)
              ·
                refine ⟨965797623422551827616645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5150920658253609747288773 965797623422551827616645)
                ·
                  refine ⟨181087054391728467678121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965797623422551827616645 181087054391728467678121)
                  ·
                    rfl

theorem cell22_1586996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1586996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1586996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1586996 prefixEnd_1586996 := by exact prefixLift 1586996
  have htrace : WordTrace (prefixWord ++ tailWord_1586996) baseStart_1586996 baseEnd_1586996 := by
    simpa [prefixWord, tailWord_1586996, baseEnd_1586996] using wordTrace_append hprefix tailTrace_1586996
  have hstable : (prefixWord ++ tailWord_1586996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586996).length < 2 ^ (prefixWord ++ tailWord_1586996).sum := by decide
  have hdescent : baseEnd_1586996 < baseStart_1586996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587052 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1587052 : Nat := 118140960795 + 1587052 * 2 ^ 59
def prefixEnd_1587052 : Nat := 4983230072969 + 3 ^ 40 * 1587052 * 2
def baseEnd_1587052 : Nat := 181093444373206641211397

theorem tailTrace_1587052 : CollatzResearch.WordTrace tailWord_1587052 prefixEnd_1587052 181093444373206641211397 := by
  unfold tailWord_1587052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942270923194562873781705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38589694564259417165042273 28942270923194562873781705)
  ·
    refine ⟨21706703192395922155336279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28942270923194562873781705 21706703192395922155336279)
    ·
      refine ⟨32560054788593883233004419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21706703192395922155336279 32560054788593883233004419)
      ·
        refine ⟨48840082182890824849506629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32560054788593883233004419 48840082182890824849506629)
        ·
          refine ⟨9157515409292029659282493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48840082182890824849506629 9157515409292029659282493)
          ·
            refine ⟨3434068278484511122230935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9157515409292029659282493 3434068278484511122230935)
            ·
              refine ⟨5151102417726766683346403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434068278484511122230935 5151102417726766683346403)
              ·
                refine ⟨7726653626590150025019605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151102417726766683346403 7726653626590150025019605)
                ·
                  refine ⟨181093444373206641211397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7726653626590150025019605 181093444373206641211397)
                  ·
                    rfl

theorem cell22_1587052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1587052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587052 prefixEnd_1587052 := by exact prefixLift 1587052
  have htrace : WordTrace (prefixWord ++ tailWord_1587052) baseStart_1587052 baseEnd_1587052 := by
    simpa [prefixWord, tailWord_1587052, baseEnd_1587052] using wordTrace_append hprefix tailTrace_1587052
  have hstable : (prefixWord ++ tailWord_1587052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587052).length < 2 ^ (prefixWord ++ tailWord_1587052).sum := by decide
  have hdescent : baseEnd_1587052 < baseStart_1587052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587090 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1587090 : Nat := 118140960795 + 1587090 * 2 ^ 59
def prefixEnd_1587090 : Nat := 4983230072969 + 3 ^ 40 * 1587090 * 2
def baseEnd_1587090 : Nat := 543293341296200491184075

theorem tailTrace_1587090 : CollatzResearch.WordTrace tailWord_1587090 prefixEnd_1587090 543293341296200491184075 := by
  unfold tailWord_1587090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14471481955062864559361681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38590618546834305491631149 14471481955062864559361681)
  ·
    refine ⟨10853611466297148419521261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14471481955062864559361681 10853611466297148419521261)
    ·
      refine ⟨4070104299861430657320473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10853611466297148419521261 4070104299861430657320473)
      ·
        refine ⟨3052578224896072992990355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070104299861430657320473 3052578224896072992990355)
        ·
          refine ⟨4578867337344109489485533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052578224896072992990355 4578867337344109489485533)
          ·
            refine ⟨1717075251504041058557075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4578867337344109489485533 1717075251504041058557075)
            ·
              refine ⟨2575612877256061587835613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717075251504041058557075 2575612877256061587835613)
              ·
                refine ⟨965854828971023095438355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2575612877256061587835613 965854828971023095438355)
                ·
                  refine ⟨1448782243456534643157533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965854828971023095438355 1448782243456534643157533)
                  ·
                    refine ⟨543293341296200491184075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448782243456534643157533 543293341296200491184075)
                    ·
                      rfl

theorem cell22_1587090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1587090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587090 prefixEnd_1587090 := by exact prefixLift 1587090
  have htrace : WordTrace (prefixWord ++ tailWord_1587090) baseStart_1587090 baseEnd_1587090 := by
    simpa [prefixWord, tailWord_1587090, baseEnd_1587090] using wordTrace_append hprefix tailTrace_1587090
  have hstable : (prefixWord ++ tailWord_1587090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587090).length < 2 ^ (prefixWord ++ tailWord_1587090).sum := by decide
  have hdescent : baseEnd_1587090 < baseStart_1587090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587127 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1587127 : Nat := 118140960795 + 1587127 * 2 ^ 59
def prefixEnd_1587127 : Nat := 4983230072969 + 3 ^ 40 * 1587127 * 2
def baseEnd_1587127 : Nat := 543306007152344728008961

theorem tailTrace_1587127 : CollatzResearch.WordTrace tailWord_1587127 prefixEnd_1587127 543306007152344728008961 := by
  unfold tailWord_1587127
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887277321117413556543635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38591518214078275704362423 57887277321117413556543635)
  ·
    refine ⟨86830915981676120334815453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57887277321117413556543635 86830915981676120334815453)
    ·
      refine ⟨32561593493128545125555795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86830915981676120334815453 32561593493128545125555795)
      ·
        refine ⟨48842390239692817688333693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32561593493128545125555795 48842390239692817688333693)
        ·
          refine ⟨18315896339884806633125135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48842390239692817688333693 18315896339884806633125135)
          ·
            refine ⟨27473844509827209949687703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18315896339884806633125135 27473844509827209949687703)
            ·
              refine ⟨41210766764740814924531555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27473844509827209949687703 41210766764740814924531555)
              ·
                refine ⟨61816150147111222386797333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41210766764740814924531555 61816150147111222386797333)
                ·
                  refine ⟨2897632038145838549381125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61816150147111222386797333 2897632038145838549381125)
                  ·
                    refine ⟨543306007152344728008961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897632038145838549381125 543306007152344728008961)
                    ·
                      rfl

theorem cell22_1587127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1587127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587127 prefixEnd_1587127 := by exact prefixLift 1587127
  have htrace : WordTrace (prefixWord ++ tailWord_1587127) baseStart_1587127 baseEnd_1587127 := by
    simpa [prefixWord, tailWord_1587127, baseEnd_1587127] using wordTrace_append hprefix tailTrace_1587127
  have hstable : (prefixWord ++ tailWord_1587127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587127).length < 2 ^ (prefixWord ++ tailWord_1587127).sum := by decide
  have hdescent : baseEnd_1587127 < baseStart_1587127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587144 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1587144 : Nat := 118140960795 + 1587144 * 2 ^ 59
def prefixEnd_1587144 : Nat := 4983230072969 + 3 ^ 40 * 1587144 * 2
def baseEnd_1587144 : Nat := 543311826599762350333909

theorem tailTrace_1587144 : CollatzResearch.WordTrace tailWord_1587144 prefixEnd_1587144 543311826599762350333909 := by
  unfold tailWord_1587144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28943948681027912729956243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38591931574703883639941657 28943948681027912729956243)
  ·
    refine ⟨43415923021541869094934365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28943948681027912729956243 43415923021541869094934365)
    ·
      refine ⟨16280971133078200910600387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43415923021541869094934365 16280971133078200910600387)
      ·
        refine ⟨24421456699617301365900581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16280971133078200910600387 24421456699617301365900581)
        ·
          refine ⟨4579023131178244006106359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24421456699617301365900581 4579023131178244006106359)
          ·
            refine ⟨6868534696767366009159539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579023131178244006106359 6868534696767366009159539)
            ·
              refine ⟨10302802045151049013739309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868534696767366009159539 10302802045151049013739309)
              ·
                refine ⟨3863550766931643380152241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10302802045151049013739309 3863550766931643380152241)
                ·
                  refine ⟨2897663075198732535114181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863550766931643380152241 2897663075198732535114181)
                  ·
                    refine ⟨543311826599762350333909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897663075198732535114181 543311826599762350333909)
                    ·
                      rfl

theorem cell22_1587144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1587144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587144 prefixEnd_1587144 := by exact prefixLift 1587144
  have htrace : WordTrace (prefixWord ++ tailWord_1587144) baseStart_1587144 baseEnd_1587144 := by
    simpa [prefixWord, tailWord_1587144, baseEnd_1587144] using wordTrace_append hprefix tailTrace_1587144
  have hstable : (prefixWord ++ tailWord_1587144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587144).length < 2 ^ (prefixWord ++ tailWord_1587144).sum := by decide
  have hdescent : baseEnd_1587144 < baseStart_1587144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587165 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1587165 : Nat := 118140960795 + 1587165 * 2 ^ 59
def prefixEnd_1587165 : Nat := 4983230072969 + 3 ^ 40 * 1587165 * 2
def baseEnd_1587165 : Nat := 181106338442975098519615

theorem tailTrace_1587165 : CollatzResearch.WordTrace tailWord_1587165 prefixEnd_1587165 181106338442975098519615 := by
  unfold tailWord_1587165
  simp only [CollatzResearch.WordTrace]
  refine ⟨57888663294979746046426949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38592442196653164030951299 57888663294979746046426949)
  ·
    refine ⟨10854124367808702383705053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57888663294979746046426949 10854124367808702383705053)
    ·
      refine ⟨4070296637928263393889395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10854124367808702383705053 4070296637928263393889395)
      ·
        refine ⟨6105444956892395090834093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070296637928263393889395 6105444956892395090834093)
        ·
          refine ⟨2289541858834648159062785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6105444956892395090834093 2289541858834648159062785)
          ·
            refine ⟨1717156394125986119297089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289541858834648159062785 1717156394125986119297089)
            ·
              refine ⟨1287867295594489589472817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717156394125986119297089 1287867295594489589472817)
              ·
                refine ⟨965900471695867192104613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287867295594489589472817 965900471695867192104613)
                ·
                  refine ⟨181106338442975098519615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965900471695867192104613 181106338442975098519615)
                  ·
                    rfl

theorem cell22_1587165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1587165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587165 prefixEnd_1587165 := by exact prefixLift 1587165
  have htrace : WordTrace (prefixWord ++ tailWord_1587165) baseStart_1587165 baseEnd_1587165 := by
    simpa [prefixWord, tailWord_1587165, baseEnd_1587165] using wordTrace_append hprefix tailTrace_1587165
  have hstable : (prefixWord ++ tailWord_1587165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587165).length < 2 ^ (prefixWord ++ tailWord_1587165).sum := by decide
  have hdescent : baseEnd_1587165 < baseStart_1587165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587172 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1587172 : Nat := 118140960795 + 1587172 * 2 ^ 59
def prefixEnd_1587172 : Nat := 4983230072969 + 3 ^ 40 * 1587172 * 2
def baseEnd_1587172 : Nat := 543321411571979610633823

theorem tailTrace_1587172 : CollatzResearch.WordTrace tailWord_1587172 prefixEnd_1587172 543321411571979610633823 := by
  unfold tailWord_1587172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28944459302977193120965885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38592612403969590827954513 28944459302977193120965885)
  ·
    refine ⟨10854172238616447420362207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28944459302977193120965885 10854172238616447420362207)
    ·
      refine ⟨16281258357924671130543311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10854172238616447420362207 16281258357924671130543311)
      ·
        refine ⟨24421887536887006695814967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16281258357924671130543311 24421887536887006695814967)
        ·
          refine ⟨36632831305330510043722451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24421887536887006695814967 36632831305330510043722451)
          ·
            refine ⟨54949246957995765065583677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36632831305330510043722451 54949246957995765065583677)
            ·
              refine ⟨20605967609248411899593879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54949246957995765065583677 20605967609248411899593879)
              ·
                refine ⟨30908951413872617849390819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20605967609248411899593879 30908951413872617849390819)
                ·
                  refine ⟨46363427120808926774086229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30908951413872617849390819 46363427120808926774086229)
                  ·
                    refine ⟨543321411571979610633823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46363427120808926774086229 543321411571979610633823)
                    ·
                      rfl

theorem cell22_1587172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1587172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587172 prefixEnd_1587172 := by exact prefixLift 1587172
  have htrace : WordTrace (prefixWord ++ tailWord_1587172) baseStart_1587172 baseEnd_1587172 := by
    simpa [prefixWord, tailWord_1587172, baseEnd_1587172] using wordTrace_append hprefix tailTrace_1587172
  have hstable : (prefixWord ++ tailWord_1587172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587172).length < 2 ^ (prefixWord ++ tailWord_1587172).sum := by decide
  have hdescent : baseEnd_1587172 < baseStart_1587172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587208 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_1587208 : Nat := 118140960795 + 1587208 * 2 ^ 59
def prefixEnd_1587208 : Nat := 4983230072969 + 3 ^ 40 * 1587208 * 2
def baseEnd_1587208 : Nat := 543333735107687516733713

theorem tailTrace_1587208 : CollatzResearch.WordTrace tailWord_1587208 prefixEnd_1587208 543333735107687516733713 := by
  unfold tailWord_1587208
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945115816911982195121139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38593487755882642926828185 28945115816911982195121139)
  ·
    refine ⟨43417673725367973292681709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28945115816911982195121139 43417673725367973292681709)
    ·
      refine ⟨16281627647012989984755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43417673725367973292681709 16281627647012989984755641)
      ·
        refine ⟨12211220735259742488566731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16281627647012989984755641 12211220735259742488566731)
        ·
          refine ⟨18316831102889613732850097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211220735259742488566731 18316831102889613732850097)
          ·
            refine ⟨13737623327167210299637573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18316831102889613732850097 13737623327167210299637573)
            ·
              refine ⟨2575804373843851931182045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13737623327167210299637573 2575804373843851931182045)
              ·
                refine ⟨965926640191444474193267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2575804373843851931182045 965926640191444474193267)
                ·
                  refine ⟨1448889960287166711289901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965926640191444474193267 1448889960287166711289901)
                  ·
                    refine ⟨543333735107687516733713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448889960287166711289901 543333735107687516733713)
                    ·
                      rfl

theorem cell22_1587208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_1587208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587208 prefixEnd_1587208 := by exact prefixLift 1587208
  have htrace : WordTrace (prefixWord ++ tailWord_1587208) baseStart_1587208 baseEnd_1587208 := by
    simpa [prefixWord, tailWord_1587208, baseEnd_1587208] using wordTrace_append hprefix tailTrace_1587208
  have hstable : (prefixWord ++ tailWord_1587208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587208).length < 2 ^ (prefixWord ++ tailWord_1587208).sum := by decide
  have hdescent : baseEnd_1587208 < baseStart_1587208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587249 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 6]
def baseStart_1587249 : Nat := 118140960795 + 1587249 * 2 ^ 59
def prefixEnd_1587249 : Nat := 4983230072969 + 3 ^ 40 * 1587249 * 2
def baseEnd_1587249 : Nat := 181115923415192358819529

theorem tailTrace_1587249 : CollatzResearch.WordTrace tailWord_1587249 prefixEnd_1587249 181115923415192358819529 := by
  unfold tailWord_1587249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57891727026675428392484801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38594484684450285594989867 57891727026675428392484801)
  ·
    refine ⟨43418795270006571294363601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57891727026675428392484801 43418795270006571294363601)
    ·
      refine ⟨32564096452504928470772701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43418795270006571294363601 32564096452504928470772701)
      ·
        refine ⟨12211536169689348176539763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32564096452504928470772701 12211536169689348176539763)
        ·
          refine ⟨18317304254534022264809645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211536169689348176539763 18317304254534022264809645)
          ·
            refine ⟨6868989095450258349303617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18317304254534022264809645 6868989095450258349303617)
            ·
              refine ⟨5151741821587693761977713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868989095450258349303617 5151741821587693761977713)
              ·
                refine ⟨3863806366190770321483285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151741821587693761977713 3863806366190770321483285)
                ·
                  refine ⟨181115923415192358819529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3863806366190770321483285 181115923415192358819529)
                  ·
                    rfl

theorem cell22_1587249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_1587249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587249 prefixEnd_1587249 := by exact prefixLift 1587249
  have htrace : WordTrace (prefixWord ++ tailWord_1587249) baseStart_1587249 baseEnd_1587249 := by
    simpa [prefixWord, tailWord_1587249, baseEnd_1587249] using wordTrace_append hprefix tailTrace_1587249
  have hstable : (prefixWord ++ tailWord_1587249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587249).length < 2 ^ (prefixWord ++ tailWord_1587249).sum := by decide
  have hdescent : baseEnd_1587249 < baseStart_1587249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587279 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_1587279 : Nat := 118140960795 + 1587279 * 2 ^ 59
def prefixEnd_1587279 : Nat := 4983230072969 + 3 ^ 40 * 1587279 * 2
def baseEnd_1587279 : Nat := 543358039858666998208495

theorem tailTrace_1587279 : CollatzResearch.WordTrace tailWord_1587279 prefixEnd_1587279 543358039858666998208495 := by
  unfold tailWord_1587279
  simp only [CollatzResearch.WordTrace]
  refine ⟨57892821216566743516076891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38595214144377829010717927 57892821216566743516076891)
  ·
    refine ⟨86839231824850115274115337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57892821216566743516076891 86839231824850115274115337)
    ·
      refine ⟨65129423868637586455586503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86839231824850115274115337 65129423868637586455586503)
      ·
        refine ⟨97694135802956379683379755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65129423868637586455586503 97694135802956379683379755)
        ·
          refine ⟨146541203704434569525069633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97694135802956379683379755 146541203704434569525069633)
          ·
            refine ⟨109905902778325927143802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146541203704434569525069633 109905902778325927143802225)
            ·
              refine ⟨82429427083744445357851669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109905902778325927143802225 82429427083744445357851669)
              ·
                refine ⟨3863879394550520876149297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82429427083744445357851669 3863879394550520876149297)
                ·
                  refine ⟨2897909545912890657111973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863879394550520876149297 2897909545912890657111973)
                  ·
                    refine ⟨543358039858666998208495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897909545912890657111973 543358039858666998208495)
                    ·
                      rfl

theorem cell22_1587279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_1587279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587279 prefixEnd_1587279 := by exact prefixLift 1587279
  have htrace : WordTrace (prefixWord ++ tailWord_1587279) baseStart_1587279 baseEnd_1587279 := by
    simpa [prefixWord, tailWord_1587279, baseEnd_1587279] using wordTrace_append hprefix tailTrace_1587279
  have hstable : (prefixWord ++ tailWord_1587279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587279).length < 2 ^ (prefixWord ++ tailWord_1587279).sum := by decide
  have hdescent : baseEnd_1587279 < baseStart_1587279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587281 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_1587281 : Nat := 118140960795 + 1587281 * 2 ^ 59
def prefixEnd_1587281 : Nat := 4983230072969 + 3 ^ 40 * 1587281 * 2
def baseEnd_1587281 : Nat := 543358724499539659658489

theorem tailTrace_1587281 : CollatzResearch.WordTrace tailWord_1587281 prefixEnd_1587281 543358724499539659658489 := by
  unfold tailWord_1587281
  simp only [CollatzResearch.WordTrace]
  refine ⟨57892894162559497857649697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38595262775039665238433131 57892894162559497857649697)
  ·
    refine ⟨43419670621919623393237273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57892894162559497857649697 43419670621919623393237273)
    ·
      refine ⟨32564752966439717544927955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43419670621919623393237273 32564752966439717544927955)
      ·
        refine ⟨48847129449659576317391933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32564752966439717544927955 48847129449659576317391933)
        ·
          refine ⟨18317673543622341119021975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48847129449659576317391933 18317673543622341119021975)
          ·
            refine ⟨27476510315433511678532963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317673543622341119021975 27476510315433511678532963)
            ·
              refine ⟨41214765473150267517799445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27476510315433511678532963 41214765473150267517799445)
              ·
                refine ⟨1931942131553918789896849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41214765473150267517799445 1931942131553918789896849)
                ·
                  refine ⟨1448956598665439092422637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931942131553918789896849 1448956598665439092422637)
                  ·
                    refine ⟨543358724499539659658489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448956598665439092422637 543358724499539659658489)
                    ·
                      rfl

theorem cell22_1587281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_1587281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587281 prefixEnd_1587281 := by exact prefixLift 1587281
  have htrace : WordTrace (prefixWord ++ tailWord_1587281) baseStart_1587281 baseEnd_1587281 := by
    simpa [prefixWord, tailWord_1587281, baseEnd_1587281] using wordTrace_append hprefix tailTrace_1587281
  have hstable : (prefixWord ++ tailWord_1587281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587281).length < 2 ^ (prefixWord ++ tailWord_1587281).sum := by decide
  have hdescent : baseEnd_1587281 < baseStart_1587281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587356 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1587356 : Nat := 118140960795 + 1587356 * 2 ^ 59
def prefixEnd_1587356 : Nat := 4983230072969 + 3 ^ 40 * 1587356 * 2
def baseEnd_1587356 : Nat := 181128132844088154677753

theorem tailTrace_1587356 : CollatzResearch.WordTrace tailWord_1587356 prefixEnd_1587356 181128132844088154677753 := by
  unfold tailWord_1587356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28947814818643892833314961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38597086424858523777753281 28947814818643892833314961)
  ·
    refine ⟨21710861113982919624986221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28947814818643892833314961 21710861113982919624986221)
    ·
      refine ⟨8141572917743594859369833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21710861113982919624986221 8141572917743594859369833)
      ·
        refine ⟨6106179688307696144527375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8141572917743594859369833 6106179688307696144527375)
        ·
          refine ⟨9159269532461544216791063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106179688307696144527375 9159269532461544216791063)
          ·
            refine ⟨13738904298692316325186595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159269532461544216791063 13738904298692316325186595)
            ·
              refine ⟨20608356448038474487779893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13738904298692316325186595 20608356448038474487779893)
              ·
                refine ⟨1932033417003606983229365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20608356448038474487779893 1932033417003606983229365)
                ·
                  refine ⟨181128132844088154677753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1932033417003606983229365 181128132844088154677753)
                  ·
                    rfl

theorem cell22_1587356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1587356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587356 prefixEnd_1587356 := by exact prefixLift 1587356
  have htrace : WordTrace (prefixWord ++ tailWord_1587356) baseStart_1587356 baseEnd_1587356 := by
    simpa [prefixWord, tailWord_1587356, baseEnd_1587356] using wordTrace_append hprefix tailTrace_1587356
  have hstable : (prefixWord ++ tailWord_1587356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587356).length < 2 ^ (prefixWord ++ tailWord_1587356).sum := by decide
  have hdescent : baseEnd_1587356 < baseStart_1587356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587377 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 1, 3]
def baseStart_1587377 : Nat := 118140960795 + 1587377 * 2 ^ 59
def prefixEnd_1587377 : Nat := 4983230072969 + 3 ^ 40 * 1587377 * 2
def baseEnd_1587377 : Nat := 543391587261427409258195

theorem tailTrace_1587377 : CollatzResearch.WordTrace tailWord_1587377 prefixEnd_1587377 543391587261427409258195 := by
  unfold tailWord_1587377
  simp only [CollatzResearch.WordTrace]
  refine ⟨57896395570211706253144385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38597597046807804168762923 57896395570211706253144385)
  ·
    refine ⟨43422296677658779689858289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57896395570211706253144385 43422296677658779689858289)
    ·
      refine ⟨32566722508244084767393717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43422296677658779689858289 32566722508244084767393717)
      ·
        refine ⟨3053130235147882946943161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32566722508244084767393717 3053130235147882946943161)
        ·
          refine ⟨2289847676360912210207371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053130235147882946943161 2289847676360912210207371)
          ·
            refine ⟨3434771514541368315311057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289847676360912210207371 3434771514541368315311057)
            ·
              refine ⟨2576078635906026236483293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3434771514541368315311057 2576078635906026236483293)
              ·
                refine ⟨966029488464759838681235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576078635906026236483293 966029488464759838681235)
                ·
                  refine ⟨1449044232697139758021853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966029488464759838681235 1449044232697139758021853)
                  ·
                    refine ⟨543391587261427409258195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449044232697139758021853 543391587261427409258195)
                    ·
                      rfl

theorem cell22_1587377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_1587377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587377 prefixEnd_1587377 := by exact prefixLift 1587377
  have htrace : WordTrace (prefixWord ++ tailWord_1587377) baseStart_1587377 baseEnd_1587377 := by
    simpa [prefixWord, tailWord_1587377, baseEnd_1587377] using wordTrace_append hprefix tailTrace_1587377
  have hstable : (prefixWord ++ tailWord_1587377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587377).length < 2 ^ (prefixWord ++ tailWord_1587377).sum := by decide
  have hdescent : baseEnd_1587377 < baseStart_1587377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587384 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_1587384 : Nat := 118140960795 + 1587384 * 2 ^ 59
def prefixEnd_1587384 : Nat := 4983230072969 + 3 ^ 40 * 1587384 * 2
def baseEnd_1587384 : Nat := 181131327834827241444391

theorem tailTrace_1587384 : CollatzResearch.WordTrace tailWord_1587384 prefixEnd_1587384 181131327834827241444391 := by
  unfold tailWord_1587384
  simp only [CollatzResearch.WordTrace]
  refine ⟨28948325440593173224324603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38597767254124230965766137 28948325440593173224324603)
  ·
    refine ⟨43422488160889759836486905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28948325440593173224324603 43422488160889759836486905)
    ·
      refine ⟨32566866120667319877365179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43422488160889759836486905 32566866120667319877365179)
      ·
        refine ⟨48850299181000979816047769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32566866120667319877365179 48850299181000979816047769)
        ·
          refine ⟨36637724385750734862035827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48850299181000979816047769 36637724385750734862035827)
          ·
            refine ⟨54956586578626102293053741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36637724385750734862035827 54956586578626102293053741)
            ·
              refine ⟨20608719966984788359895153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54956586578626102293053741 20608719966984788359895153)
              ·
                refine ⟨15456539975238591269921365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20608719966984788359895153 15456539975238591269921365)
                ·
                  refine ⟨181131327834827241444391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15456539975238591269921365 181131327834827241444391)
                  ·
                    rfl

theorem cell22_1587384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_1587384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587384 prefixEnd_1587384 := by exact prefixLift 1587384
  have htrace : WordTrace (prefixWord ++ tailWord_1587384) baseStart_1587384 baseEnd_1587384 := by
    simpa [prefixWord, tailWord_1587384, baseEnd_1587384] using wordTrace_append hprefix tailTrace_1587384
  have hstable : (prefixWord ++ tailWord_1587384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587384).length < 2 ^ (prefixWord ++ tailWord_1587384).sum := by decide
  have hdescent : baseEnd_1587384 < baseStart_1587384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587390 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1587390 : Nat := 118140960795 + 1587390 * 2 ^ 59
def prefixEnd_1587390 : Nat := 4983230072969 + 3 ^ 40 * 1587390 * 2
def baseEnd_1587390 : Nat := 181132012475699902894385

theorem tailTrace_1587390 : CollatzResearch.WordTrace tailWord_1587390 prefixEnd_1587390 181132012475699902894385 := by
  unfold tailWord_1587390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237108714895576184170953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38597913146109739648911749 7237108714895576184170953)
  ·
    refine ⟨5427831536171682138128215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7237108714895576184170953 5427831536171682138128215)
    ·
      refine ⟨8141747304257523207192323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427831536171682138128215 8141747304257523207192323)
      ·
        refine ⟨12212620956386284810788485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141747304257523207192323 12212620956386284810788485)
        ·
          refine ⟨2289866429322428402022841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12212620956386284810788485 2289866429322428402022841)
          ·
            refine ⟨1717399821991821301517131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289866429322428402022841 1717399821991821301517131)
            ·
              refine ⟨2576099732987731952275697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717399821991821301517131 2576099732987731952275697)
              ·
                refine ⟨1932074799740798964206773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576099732987731952275697 1932074799740798964206773)
                ·
                  refine ⟨181132012475699902894385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1932074799740798964206773 181132012475699902894385)
                  ·
                    rfl

theorem cell22_1587390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1587390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587390 prefixEnd_1587390 := by exact prefixLift 1587390
  have htrace : WordTrace (prefixWord ++ tailWord_1587390) baseStart_1587390 baseEnd_1587390 := by
    simpa [prefixWord, tailWord_1587390, baseEnd_1587390] using wordTrace_append hprefix tailTrace_1587390
  have hstable : (prefixWord ++ tailWord_1587390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587390).length < 2 ^ (prefixWord ++ tailWord_1587390).sum := by decide
  have hdescent : baseEnd_1587390 < baseStart_1587390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587394 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1587394 : Nat := 118140960795 + 1587394 * 2 ^ 59
def prefixEnd_1587394 : Nat := 4983230072969 + 3 ^ 40 * 1587394 * 2
def baseEnd_1587394 : Nat := 543397406708845031583143

theorem tailTrace_1587394 : CollatzResearch.WordTrace tailWord_1587394 prefixEnd_1587394 543397406708845031583143 := by
  unfold tailWord_1587394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474253902787529539128309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38598010407433412104342157 14474253902787529539128309)
  ·
    refine ⟨1356961303386330894293279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14474253902787529539128309 1356961303386330894293279)
    ·
      refine ⟨2035441955079496341439919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356961303386330894293279 2035441955079496341439919)
      ·
        refine ⟨3053162932619244512159879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035441955079496341439919 3053162932619244512159879)
        ·
          refine ⟨4579744398928866768239819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053162932619244512159879 4579744398928866768239819)
          ·
            refine ⟨6869616598393300152359729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579744398928866768239819 6869616598393300152359729)
            ·
              refine ⟨5152212448794975114269797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6869616598393300152359729 5152212448794975114269797)
              ·
                refine ⟨966039834149057833925587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5152212448794975114269797 966039834149057833925587)
                ·
                  refine ⟨1449059751223586750888381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966039834149057833925587 1449059751223586750888381)
                  ·
                    refine ⟨543397406708845031583143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449059751223586750888381 543397406708845031583143)
                    ·
                      rfl

theorem cell22_1587394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1587394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587394 prefixEnd_1587394 := by exact prefixLift 1587394
  have htrace : WordTrace (prefixWord ++ tailWord_1587394) baseStart_1587394 baseEnd_1587394 := by
    simpa [prefixWord, tailWord_1587394, baseEnd_1587394] using wordTrace_append hprefix tailTrace_1587394
  have hstable : (prefixWord ++ tailWord_1587394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587394).length < 2 ^ (prefixWord ++ tailWord_1587394).sum := by decide
  have hdescent : baseEnd_1587394 < baseStart_1587394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1587399 : Nat := 118140960795 + 1587399 * 2 ^ 59
def prefixEnd_1587399 : Nat := 4983230072969 + 3 ^ 40 * 1587399 * 2
def baseEnd_1587399 : Nat := 543399118311026685208127

theorem tailTrace_1587399 : CollatzResearch.WordTrace tailWord_1587399 prefixEnd_1587399 543399118311026685208127 := by
  unfold tailWord_1587399
  simp only [CollatzResearch.WordTrace]
  refine ⟨57897197976132004010445251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38598131984088002673630167 57897197976132004010445251)
  ·
    refine ⟨86845796964198006015667877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57897197976132004010445251 86845796964198006015667877)
    ·
      refine ⟨16283586930787126127937727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86845796964198006015667877 16283586930787126127937727)
      ·
        refine ⟨24425380396180689191906591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16283586930787126127937727 24425380396180689191906591)
        ·
          refine ⟨36638070594271033787859887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24425380396180689191906591 36638070594271033787859887)
          ·
            refine ⟨54957105891406550681789831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36638070594271033787859887 54957105891406550681789831)
            ·
              refine ⟨82435658837109826022684747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54957105891406550681789831 82435658837109826022684747)
              ·
                refine ⟨123653488255664739034027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82435658837109826022684747 123653488255664739034027121)
                ·
                  refine ⟨92740116191748554275520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123653488255664739034027121 92740116191748554275520341)
                  ·
                    refine ⟨543399118311026685208127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92740116191748554275520341 543399118311026685208127)
                    ·
                      rfl

theorem cell22_1587399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1587399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587399 prefixEnd_1587399 := by exact prefixLift 1587399
  have htrace : WordTrace (prefixWord ++ tailWord_1587399) baseStart_1587399 baseEnd_1587399 := by
    simpa [prefixWord, tailWord_1587399, baseEnd_1587399] using wordTrace_append hprefix tailTrace_1587399
  have hstable : (prefixWord ++ tailWord_1587399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587399).length < 2 ^ (prefixWord ++ tailWord_1587399).sum := by decide
  have hdescent : baseEnd_1587399 < baseStart_1587399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587446 : List Nat := [5, 1, 1, 1, 1, 1, 12]
def baseStart_1587446 : Nat := 118140960795 + 1587446 * 2 ^ 59
def prefixEnd_1587446 : Nat := 4983230072969 + 3 ^ 40 * 1587446 * 2
def baseEnd_1587446 : Nat := 20126489161908675158629

theorem tailTrace_1587446 : CollatzResearch.WordTrace tailWord_1587446 prefixEnd_1587446 20126489161908675158629 := by
  unfold tailWord_1587446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618682012935108189837887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38599274804641154024937461 3618682012935108189837887)
  ·
    refine ⟨5428023019402662284756831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3618682012935108189837887 5428023019402662284756831)
    ·
      refine ⟨8142034529103993427135247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428023019402662284756831 8142034529103993427135247)
      ·
        refine ⟨12213051793655990140702871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8142034529103993427135247 12213051793655990140702871)
        ·
          refine ⟨18319577690483985211054307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213051793655990140702871 18319577690483985211054307)
          ·
            refine ⟨27479366535725977816581461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18319577690483985211054307 27479366535725977816581461)
            ·
              refine ⟨20126489161908675158629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27479366535725977816581461 20126489161908675158629)
              ·
                rfl

theorem cell22_1587446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 12].length) (baseStart_1587446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587446 prefixEnd_1587446 := by exact prefixLift 1587446
  have htrace : WordTrace (prefixWord ++ tailWord_1587446) baseStart_1587446 baseEnd_1587446 := by
    simpa [prefixWord, tailWord_1587446, baseEnd_1587446] using wordTrace_append hprefix tailTrace_1587446
  have hstable : (prefixWord ++ tailWord_1587446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587446).length < 2 ^ (prefixWord ++ tailWord_1587446).sum := by decide
  have hdescent : baseEnd_1587446 < baseStart_1587446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587512 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_1587512 : Nat := 118140960795 + 1587512 * 2 ^ 59
def prefixEnd_1587512 : Nat := 4983230072969 + 3 ^ 40 * 1587512 * 2
def baseEnd_1587512 : Nat := 543437800520332057132781

theorem tailTrace_1587512 : CollatzResearch.WordTrace tailWord_1587512 prefixEnd_1587512 543437800520332057132781 := by
  unfold tailWord_1587512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950659712361312154654395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38600879616481749539539193 28950659712361312154654395)
  ·
    refine ⟨43425989568541968231981593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28950659712361312154654395 43425989568541968231981593)
    ·
      refine ⟨32569492176406476173986195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43425989568541968231981593 32569492176406476173986195)
      ·
        refine ⟨48854238264609714260979293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32569492176406476173986195 48854238264609714260979293)
        ·
          refine ⟨18320339349228642847867235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48854238264609714260979293 18320339349228642847867235)
          ·
            refine ⟨27480509023842964271800853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320339349228642847867235 27480509023842964271800853)
            ·
              refine ⟨1288148860492638950240665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27480509023842964271800853 1288148860492638950240665)
              ·
                refine ⟨966111645369479212680499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288148860492638950240665 966111645369479212680499)
                ·
                  refine ⟨1449167468054218819020749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966111645369479212680499 1449167468054218819020749)
                  ·
                    refine ⟨543437800520332057132781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449167468054218819020749 543437800520332057132781)
                    ·
                      rfl

theorem cell22_1587512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_1587512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587512 prefixEnd_1587512 := by exact prefixLift 1587512
  have htrace : WordTrace (prefixWord ++ tailWord_1587512) baseStart_1587512 baseEnd_1587512 := by
    simpa [prefixWord, tailWord_1587512, baseEnd_1587512] using wordTrace_append hprefix tailTrace_1587512
  have hstable : (prefixWord ++ tailWord_1587512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587512).length < 2 ^ (prefixWord ++ tailWord_1587512).sum := by decide
  have hdescent : baseEnd_1587512 < baseStart_1587512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587536 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_1587536 : Nat := 118140960795 + 1587536 * 2 ^ 59
def prefixEnd_1587536 : Nat := 4983230072969 + 3 ^ 40 * 1587536 * 2
def baseEnd_1587536 : Nat := 181148672070267998177569

theorem tailTrace_1587536 : CollatzResearch.WordTrace tailWord_1587536 prefixEnd_1587536 181148672070267998177569 := by
  unfold tailWord_1587536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28951097388317838204091231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38601463184423784272121641 28951097388317838204091231)
  ·
    refine ⟨43426646082476757306136847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28951097388317838204091231 43426646082476757306136847)
    ·
      refine ⟨65139969123715135959205271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43426646082476757306136847 65139969123715135959205271)
      ·
        refine ⟨97709953685572703938807907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65139969123715135959205271 97709953685572703938807907)
        ·
          refine ⟨146564930528359055908211861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97709953685572703938807907 146564930528359055908211861)
          ·
            refine ⟨6870231118516830745697431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146564930528359055908211861 6870231118516830745697431)
            ·
              refine ⟨10305346677775246118546147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870231118516830745697431 10305346677775246118546147)
              ·
                refine ⟨15458020016662869177819221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10305346677775246118546147 15458020016662869177819221)
                ·
                  refine ⟨181148672070267998177569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15458020016662869177819221 181148672070267998177569)
                  ·
                    rfl

theorem cell22_1587536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_1587536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587536 prefixEnd_1587536 := by exact prefixLift 1587536
  have htrace : WordTrace (prefixWord ++ tailWord_1587536) baseStart_1587536 baseEnd_1587536 := by
    simpa [prefixWord, tailWord_1587536, baseEnd_1587536] using wordTrace_append hprefix tailTrace_1587536
  have hstable : (prefixWord ++ tailWord_1587536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587536).length < 2 ^ (prefixWord ++ tailWord_1587536).sum := by decide
  have hdescent : baseEnd_1587536 < baseStart_1587536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587538 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1587538 : Nat := 118140960795 + 1587538 * 2 ^ 59
def prefixEnd_1587538 : Nat := 4983230072969 + 3 ^ 40 * 1587538 * 2
def baseEnd_1587538 : Nat := 543446700851676655982701

theorem tailTrace_1587538 : CollatzResearch.WordTrace tailWord_1587538 prefixEnd_1587538 543446700851676655982701 := by
  unfold tailWord_1587538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14475566930657107687438817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38601511815085620499836845 14475566930657107687438817)
  ·
    refine ⟨10856675197992830765579113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14475566930657107687438817 10856675197992830765579113)
    ·
      refine ⟨8142506398494623074184335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10856675197992830765579113 8142506398494623074184335)
      ·
        refine ⟨12213759597741934611276503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8142506398494623074184335 12213759597741934611276503)
        ·
          refine ⟨18320639396612901916914755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213759597741934611276503 18320639396612901916914755)
          ·
            refine ⟨27480959094919352875372133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18320639396612901916914755 27480959094919352875372133)
            ·
              refine ⟨5152679830297378664132275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27480959094919352875372133 5152679830297378664132275)
              ·
                refine ⟨7729019745446067996198413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152679830297378664132275 7729019745446067996198413)
                ·
                  refine ⟨2898382404542275498574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7729019745446067996198413 2898382404542275498574405)
                  ·
                    refine ⟨543446700851676655982701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898382404542275498574405 543446700851676655982701)
                    ·
                      rfl

theorem cell22_1587538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1587538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587538 prefixEnd_1587538 := by exact prefixLift 1587538
  have htrace : WordTrace (prefixWord ++ tailWord_1587538) baseStart_1587538 baseEnd_1587538 := by
    simpa [prefixWord, tailWord_1587538, baseEnd_1587538] using wordTrace_append hprefix tailTrace_1587538
  have hstable : (prefixWord ++ tailWord_1587538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587538).length < 2 ^ (prefixWord ++ tailWord_1587538).sum := by decide
  have hdescent : baseEnd_1587538 < baseStart_1587538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587570 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1587570 : Nat := 118140960795 + 1587570 * 2 ^ 59
def prefixEnd_1587570 : Nat := 4983230072969 + 3 ^ 40 * 1587570 * 2
def baseEnd_1587570 : Nat := 181152551701879746394201

theorem tailTrace_1587570 : CollatzResearch.WordTrace tailWord_1587570 prefixEnd_1587570 181152551701879746394201 := by
  unfold tailWord_1587570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14475858714628125053730041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38602289905675000143280109 14475858714628125053730041)
  ·
    refine ⟨10856894035971093790297531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14475858714628125053730041 10856894035971093790297531)
    ·
      refine ⟨16285341053956640685446297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856894035971093790297531 16285341053956640685446297)
      ·
        refine ⟨12214005790467480514084723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16285341053956640685446297 12214005790467480514084723)
        ·
          refine ⟨18321008685701220771127085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12214005790467480514084723 18321008685701220771127085)
          ·
            refine ⟨6870378257137957789172657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18321008685701220771127085 6870378257137957789172657)
            ·
              refine ⟨5152783692853468341879493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6870378257137957789172657 5152783692853468341879493)
              ·
                refine ⟨966146942410025314102405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5152783692853468341879493 966146942410025314102405)
                ·
                  refine ⟨181152551701879746394201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966146942410025314102405 181152551701879746394201)
                  ·
                    rfl

theorem cell22_1587570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1587570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587570 prefixEnd_1587570 := by exact prefixLift 1587570
  have htrace : WordTrace (prefixWord ++ tailWord_1587570) baseStart_1587570 baseEnd_1587570 := by
    simpa [prefixWord, tailWord_1587570, baseEnd_1587570] using wordTrace_append hprefix tailTrace_1587570
  have hstable : (prefixWord ++ tailWord_1587570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587570).length < 2 ^ (prefixWord ++ tailWord_1587570).sum := by decide
  have hdescent : baseEnd_1587570 < baseStart_1587570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587585 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1587585 : Nat := 118140960795 + 1587585 * 2 ^ 59
def prefixEnd_1587585 : Nat := 4983230072969 + 3 ^ 40 * 1587585 * 2
def baseEnd_1587585 : Nat := 543462789912184200057557

theorem tailTrace_1587585 : CollatzResearch.WordTrace tailWord_1587585 prefixEnd_1587585 543462789912184200057557 := by
  unfold tailWord_1587585
  simp only [CollatzResearch.WordTrace]
  refine ⟨57903981953458157776716209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38602654635638771851144139 57903981953458157776716209)
  ·
    refine ⟨43427986465093618332537157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57903981953458157776716209 43427986465093618332537157)
    ·
      refine ⟨8142747462205053437350717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43427986465093618332537157 8142747462205053437350717)
      ·
        refine ⟨3053530298326895039006519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8142747462205053437350717 3053530298326895039006519)
        ·
          refine ⟨4580295447490342558509779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053530298326895039006519 4580295447490342558509779)
          ·
            refine ⟨6870443171235513837764669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580295447490342558509779 6870443171235513837764669)
            ·
              refine ⟨2576416189213317689161751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6870443171235513837764669 2576416189213317689161751)
              ·
                refine ⟨3864624283819976533742627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576416189213317689161751 3864624283819976533742627)
                ·
                  refine ⟨5796936425729964800613941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864624283819976533742627 5796936425729964800613941)
                  ·
                    refine ⟨543462789912184200057557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5796936425729964800613941 543462789912184200057557)
                    ·
                      rfl

theorem cell22_1587585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1587585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587585 prefixEnd_1587585 := by exact prefixLift 1587585
  have htrace : WordTrace (prefixWord ++ tailWord_1587585) baseStart_1587585 baseEnd_1587585 := by
    simpa [prefixWord, tailWord_1587585, baseEnd_1587585] using wordTrace_append hprefix tailTrace_1587585
  have hstable : (prefixWord ++ tailWord_1587585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587585).length < 2 ^ (prefixWord ++ tailWord_1587585).sum := by decide
  have hdescent : baseEnd_1587585 < baseStart_1587585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587604 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1587604 : Nat := 118140960795 + 1587604 * 2 ^ 59
def prefixEnd_1587604 : Nat := 4983230072969 + 3 ^ 40 * 1587604 * 2
def baseEnd_1587604 : Nat := 181156431333491494610833

theorem tailTrace_1587604 : CollatzResearch.WordTrace tailWord_1587604 prefixEnd_1587604 181156431333491494610833 := by
  unfold tailWord_1587604
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952337470194662010828933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38603116626926216014438577 28952337470194662010828933)
  ·
    refine ⟨5428563275661499127030425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28952337470194662010828933 5428563275661499127030425)
    ·
      refine ⟨4071422456746124345272819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428563275661499127030425 4071422456746124345272819)
      ·
        refine ⟨6107133685119186517909229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071422456746124345272819 6107133685119186517909229)
        ·
          refine ⟨2290175131919694944215961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6107133685119186517909229 2290175131919694944215961)
          ·
            refine ⟨1717631348939771208161971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2290175131919694944215961 1717631348939771208161971)
            ·
              refine ⟨2576447023409656812242957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717631348939771208161971 2576447023409656812242957)
              ·
                refine ⟨966167633778621304591109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576447023409656812242957 966167633778621304591109)
                ·
                  refine ⟨181156431333491494610833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966167633778621304591109 181156431333491494610833)
                  ·
                    rfl

theorem cell22_1587604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1587604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587604 prefixEnd_1587604 := by exact prefixLift 1587604
  have htrace : WordTrace (prefixWord ++ tailWord_1587604) baseStart_1587604 baseEnd_1587604 := by
    simpa [prefixWord, tailWord_1587604, baseEnd_1587604] using wordTrace_append hprefix tailTrace_1587604
  have hstable : (prefixWord ++ tailWord_1587604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587604).length < 2 ^ (prefixWord ++ tailWord_1587604).sum := by decide
  have hdescent : baseEnd_1587604 < baseStart_1587604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587617 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1587617 : Nat := 118140960795 + 1587617 * 2 ^ 59
def prefixEnd_1587617 : Nat := 4983230072969 + 3 ^ 40 * 1587617 * 2
def baseEnd_1587617 : Nat := 543473744166146783257459

theorem tailTrace_1587617 : CollatzResearch.WordTrace tailWord_1587617 prefixEnd_1587617 543473744166146783257459 := by
  unfold tailWord_1587617
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905149089342227241881105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38603432726228151494587403 57905149089342227241881105)
  ·
    refine ⟨43428861817006670431410829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57905149089342227241881105 43428861817006670431410829)
    ·
      refine ⟨16285823181377501411779061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43428861817006670431410829 16285823181377501411779061)
      ·
        refine ⟨1526795923254140757354287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16285823181377501411779061 1526795923254140757354287)
        ·
          refine ⟨2290193884881211136031431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526795923254140757354287 2290193884881211136031431)
          ·
            refine ⟨3435290827321816704047147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290193884881211136031431 3435290827321816704047147)
            ·
              refine ⟨5152936240982725056070721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435290827321816704047147 5152936240982725056070721)
              ·
                refine ⟨3864702180737043792053041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5152936240982725056070721 3864702180737043792053041)
                ·
                  refine ⟨2898526635552782844039781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3864702180737043792053041 2898526635552782844039781)
                  ·
                    refine ⟨543473744166146783257459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898526635552782844039781 543473744166146783257459)
                    ·
                      rfl

theorem cell22_1587617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1587617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587617 prefixEnd_1587617 := by exact prefixLift 1587617
  have htrace : WordTrace (prefixWord ++ tailWord_1587617) baseStart_1587617 baseEnd_1587617 := by
    simpa [prefixWord, tailWord_1587617, baseEnd_1587617] using wordTrace_append hprefix tailTrace_1587617
  have hstable : (prefixWord ++ tailWord_1587617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587617).length < 2 ^ (prefixWord ++ tailWord_1587617).sum := by decide
  have hdescent : baseEnd_1587617 < baseStart_1587617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587636 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1587636 : Nat := 118140960795 + 1587636 * 2 ^ 59
def prefixEnd_1587636 : Nat := 4983230072969 + 3 ^ 40 * 1587636 * 2
def baseEnd_1587636 : Nat := 543480248254437067032401

theorem tailTrace_1587636 : CollatzResearch.WordTrace tailWord_1587636 prefixEnd_1587636 543480248254437067032401 := by
  unfold tailWord_1587636
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952921038136696743411381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38603894717515595657881841 28952921038136696743411381)
  ·
    refine ⟨2714336347325315319694817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28952921038136696743411381 2714336347325315319694817)
    ·
      refine ⟨2035752260493986489771113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2714336347325315319694817 2035752260493986489771113)
      ·
        refine ⟨1526814195370489867328335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035752260493986489771113 1526814195370489867328335)
        ·
          refine ⟨2290221293055734800992503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526814195370489867328335 2290221293055734800992503)
          ·
            refine ⟨3435331939583602201488755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290221293055734800992503 3435331939583602201488755)
            ·
              refine ⟨5152997909375403302233133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435331939583602201488755 5152997909375403302233133)
              ·
                refine ⟨1932374216015776238337425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5152997909375403302233133 1932374216015776238337425)
                ·
                  refine ⟨1449280662011832178753069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1932374216015776238337425 1449280662011832178753069)
                  ·
                    refine ⟨543480248254437067032401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449280662011832178753069 543480248254437067032401)
                    ·
                      rfl

theorem cell22_1587636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1587636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587636 prefixEnd_1587636 := by exact prefixLift 1587636
  have htrace : WordTrace (prefixWord ++ tailWord_1587636) baseStart_1587636 baseEnd_1587636 := by
    simpa [prefixWord, tailWord_1587636, baseEnd_1587636] using wordTrace_append hprefix tailTrace_1587636
  have hstable : (prefixWord ++ tailWord_1587636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587636).length < 2 ^ (prefixWord ++ tailWord_1587636).sum := by decide
  have hdescent : baseEnd_1587636 < baseStart_1587636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587690 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1587690 : Nat := 118140960795 + 1587690 * 2 ^ 59
def prefixEnd_1587690 : Nat := 4983230072969 + 3 ^ 40 * 1587690 * 2
def baseEnd_1587690 : Nat := 543498733557998926182235

theorem tailTrace_1587690 : CollatzResearch.WordTrace tailWord_1587690 prefixEnd_1587690 543498733557998926182235 := by
  unfold tailWord_1587690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476952904519440177322131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38605207745385173806192349 14476952904519440177322131)
  ·
    refine ⟨21715429356779160265983197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14476952904519440177322131 21715429356779160265983197)
    ·
      refine ⟨8143286008792185099743699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21715429356779160265983197 8143286008792185099743699)
      ·
        refine ⟨12214929013188277649615549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143286008792185099743699 12214929013188277649615549)
        ·
          refine ⟨4580598379945604118605831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12214929013188277649615549 4580598379945604118605831)
          ·
            refine ⟨6870897569918406177908747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580598379945604118605831 6870897569918406177908747)
            ·
              refine ⟨10306346354877609266863121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870897569918406177908747 10306346354877609266863121)
              ·
                refine ⟨7729759766158206950147341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306346354877609266863121 7729759766158206950147341)
                ·
                  refine ⟨2898659912309327606305253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7729759766158206950147341 2898659912309327606305253)
                  ·
                    refine ⟨543498733557998926182235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898659912309327606305253 543498733557998926182235)
                    ·
                      rfl

theorem cell22_1587690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1587690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587690 prefixEnd_1587690 := by exact prefixLift 1587690
  have htrace : WordTrace (prefixWord ++ tailWord_1587690) baseStart_1587690 baseEnd_1587690 := by
    simpa [prefixWord, tailWord_1587690, baseEnd_1587690] using wordTrace_append hprefix tailTrace_1587690
  have hstable : (prefixWord ++ tailWord_1587690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587690).length < 2 ^ (prefixWord ++ tailWord_1587690).sum := by decide
  have hdescent : baseEnd_1587690 < baseStart_1587690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587720 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1587720 : Nat := 118140960795 + 1587720 * 2 ^ 59
def prefixEnd_1587720 : Nat := 4983230072969 + 3 ^ 40 * 1587720 * 2
def baseEnd_1587720 : Nat := 543509003171088847932143

theorem tailTrace_1587720 : CollatzResearch.WordTrace tailWord_1587720 prefixEnd_1587720 543509003171088847932143 := by
  unfold tailWord_1587720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954452903984537916440307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38605937205312717221920409 28954452903984537916440307)
  ·
    refine ⟨43431679355976806874660461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954452903984537916440307 43431679355976806874660461)
    ·
      refine ⟨16286879758491302577997673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43431679355976806874660461 16286879758491302577997673)
      ·
        refine ⟨12215159818868476933498255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16286879758491302577997673 12215159818868476933498255)
        ·
          refine ⟨18322739728302715400247383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12215159818868476933498255 18322739728302715400247383)
          ·
            refine ⟨27484109592454073100371075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18322739728302715400247383 27484109592454073100371075)
            ·
              refine ⟨41226164388681109650556613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27484109592454073100371075 41226164388681109650556613)
              ·
                refine ⟨7729905822877708059479365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41226164388681109650556613 7729905822877708059479365)
                ·
                  refine ⟨1449357341789570261152381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7729905822877708059479365 1449357341789570261152381)
                  ·
                    refine ⟨543509003171088847932143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449357341789570261152381 543509003171088847932143)
                    ·
                      rfl

theorem cell22_1587720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1587720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587720 prefixEnd_1587720 := by exact prefixLift 1587720
  have htrace : WordTrace (prefixWord ++ tailWord_1587720) baseStart_1587720 baseEnd_1587720 := by
    simpa [prefixWord, tailWord_1587720, baseEnd_1587720] using wordTrace_append hprefix tailTrace_1587720
  have hstable : (prefixWord ++ tailWord_1587720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587720).length < 2 ^ (prefixWord ++ tailWord_1587720).sum := by decide
  have hdescent : baseEnd_1587720 < baseStart_1587720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587722 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_1587722 : Nat := 118140960795 + 1587722 * 2 ^ 59
def prefixEnd_1587722 : Nat := 4983230072969 + 3 ^ 40 * 1587722 * 2
def baseEnd_1587722 : Nat := 181169895937320503127379

theorem tailTrace_1587722 : CollatzResearch.WordTrace tailWord_1587722 prefixEnd_1587722 181169895937320503127379 := by
  unfold tailWord_1587722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14477244688490457543613355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38605985835974553449635613 14477244688490457543613355)
  ·
    refine ⟨21715867032735686315420033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14477244688490457543613355 21715867032735686315420033)
    ·
      refine ⟨16286900274551764736565025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21715867032735686315420033 16286900274551764736565025)
      ·
        refine ⟨12215175205913823552423769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16286900274551764736565025 12215175205913823552423769)
        ·
          refine ⟨9161381404435367664317827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12215175205913823552423769 9161381404435367664317827)
          ·
            refine ⟨13742072106653051496476741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161381404435367664317827 13742072106653051496476741)
            ·
              refine ⟨2576638519997447155589389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13742072106653051496476741 2576638519997447155589389)
              ·
                refine ⟨966239444999042683346021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576638519997447155589389 966239444999042683346021)
                ·
                  refine ⟨181169895937320503127379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966239444999042683346021 181169895937320503127379)
                  ·
                    rfl

theorem cell22_1587722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_1587722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587722 prefixEnd_1587722 := by exact prefixLift 1587722
  have htrace : WordTrace (prefixWord ++ tailWord_1587722) baseStart_1587722 baseEnd_1587722 := by
    simpa [prefixWord, tailWord_1587722, baseEnd_1587722] using wordTrace_append hprefix tailTrace_1587722
  have hstable : (prefixWord ++ tailWord_1587722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587722).length < 2 ^ (prefixWord ++ tailWord_1587722).sum := by decide
  have hdescent : baseEnd_1587722 < baseStart_1587722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587724 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_1587724 : Nat := 118140960795 + 1587724 * 2 ^ 59
def prefixEnd_1587724 : Nat := 4983230072969 + 3 ^ 40 * 1587724 * 2
def baseEnd_1587724 : Nat := 543510372452834170832131

theorem tailTrace_1587724 : CollatzResearch.WordTrace tailWord_1587724 prefixEnd_1587724 543510372452834170832131 := by
  unfold tailWord_1587724
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954525849977292258013113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38606034466636389677350817 28954525849977292258013113)
  ·
    refine ⟨21715894387482969193509835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28954525849977292258013113 21715894387482969193509835)
    ·
      refine ⟨32573841581224453790264753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21715894387482969193509835 32573841581224453790264753)
      ·
        refine ⟨24430381185918340342698565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32573841581224453790264753 24430381185918340342698565)
        ·
          refine ⟨4580696472359688814255981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24430381185918340342698565 4580696472359688814255981)
          ·
            refine ⟨1717761177134883305345993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4580696472359688814255981 1717761177134883305345993)
            ·
              refine ⟨1288320882851162479009495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717761177134883305345993 1288320882851162479009495)
              ·
                refine ⟨1932481324276743718514243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288320882851162479009495 1932481324276743718514243)
                ·
                  refine ⟨2898721986415115577771365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932481324276743718514243 2898721986415115577771365)
                  ·
                    refine ⟨543510372452834170832131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898721986415115577771365 543510372452834170832131)
                    ·
                      rfl

theorem cell22_1587724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_1587724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587724 prefixEnd_1587724 := by exact prefixLift 1587724
  have htrace : WordTrace (prefixWord ++ tailWord_1587724) baseStart_1587724 baseEnd_1587724 := by
    simpa [prefixWord, tailWord_1587724, baseEnd_1587724] using wordTrace_append hprefix tailTrace_1587724
  have hstable : (prefixWord ++ tailWord_1587724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587724).length < 2 ^ (prefixWord ++ tailWord_1587724).sum := by decide
  have hdescent : baseEnd_1587724 < baseStart_1587724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587733 : List Nat := [1, 3, 2, 1, 3, 1, 11]
def baseStart_1587733 : Nat := 118140960795 + 1587733 * 2 ^ 59
def prefixEnd_1587733 : Nat := 4983230072969 + 3 ^ 40 * 1587733 * 2
def baseEnd_1587733 : Nat := 20130127901361523976189

theorem tailTrace_1587733 : CollatzResearch.WordTrace tailWord_1587733 prefixEnd_1587733 20130127901361523976189 := by
  unfold tailWord_1587733
  simp only [CollatzResearch.WordTrace]
  refine ⟨57909379956921979053103853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38606253304614652702069235 57909379956921979053103853)
  ·
    refine ⟨21716017483845742144913945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57909379956921979053103853 21716017483845742144913945)
    ·
      refine ⟨16287013112884306608685459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21716017483845742144913945 16287013112884306608685459)
      ·
        refine ⟨24430519669326459913028189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16287013112884306608685459 24430519669326459913028189)
        ·
          refine ⟨9161444875997422467385571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24430519669326459913028189 9161444875997422467385571)
          ·
            refine ⟨13742167313996133701078357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9161444875997422467385571 13742167313996133701078357)
            ·
              refine ⟨20130127901361523976189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13742167313996133701078357 20130127901361523976189)
              ·
                rfl

theorem cell22_1587733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 11].length) (baseStart_1587733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587733 prefixEnd_1587733 := by exact prefixLift 1587733
  have htrace : WordTrace (prefixWord ++ tailWord_1587733) baseStart_1587733 baseEnd_1587733 := by
    simpa [prefixWord, tailWord_1587733, baseEnd_1587733] using wordTrace_append hprefix tailTrace_1587733
  have hstable : (prefixWord ++ tailWord_1587733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587733).length < 2 ^ (prefixWord ++ tailWord_1587733).sum := by decide
  have hdescent : baseEnd_1587733 < baseStart_1587733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587850 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1587850 : Nat := 118140960795 + 1587850 * 2 ^ 59
def prefixEnd_1587850 : Nat := 4983230072969 + 3 ^ 40 * 1587850 * 2
def baseEnd_1587850 : Nat := 543553504827811842181745

theorem tailTrace_1587850 : CollatzResearch.WordTrace tailWord_1587850 prefixEnd_1587850 543553504827811842181745 := by
  unfold tailWord_1587850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14478411824374527008778251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38609098198332072023408669 14478411824374527008778251)
  ·
    refine ⟨21717617736561790513167377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14478411824374527008778251 21717617736561790513167377)
    ·
      refine ⟨16288213302421342884875533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21717617736561790513167377 16288213302421342884875533)
      ·
        refine ⟨6108079988408003581828325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16288213302421342884875533 6108079988408003581828325)
        ·
          refine ⟨1145264997826500671592811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6108079988408003581828325 1145264997826500671592811)
          ·
            refine ⟨1717897496739751007389217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145264997826500671592811 1717897496739751007389217)
            ·
              refine ⟨1288423122554813255541913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717897496739751007389217 1288423122554813255541913)
              ·
                refine ⟨966317341916109941656435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288423122554813255541913 966317341916109941656435)
                ·
                  refine ⟨1449476012874164912484653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966317341916109941656435 1449476012874164912484653)
                  ·
                    refine ⟨543553504827811842181745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449476012874164912484653 543553504827811842181745)
                    ·
                      rfl

theorem cell22_1587850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1587850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587850 prefixEnd_1587850 := by exact prefixLift 1587850
  have htrace : WordTrace (prefixWord ++ tailWord_1587850) baseStart_1587850 baseEnd_1587850 := by
    simpa [prefixWord, tailWord_1587850, baseEnd_1587850] using wordTrace_append hprefix tailTrace_1587850
  have hstable : (prefixWord ++ tailWord_1587850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587850).length < 2 ^ (prefixWord ++ tailWord_1587850).sum := by decide
  have hdescent : baseEnd_1587850 < baseStart_1587850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587887 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_1587887 : Nat := 118140960795 + 1587887 * 2 ^ 59
def prefixEnd_1587887 : Nat := 4983230072969 + 3 ^ 40 * 1587887 * 2
def baseEnd_1587887 : Nat := 543566170683956079006631

theorem tailTrace_1587887 : CollatzResearch.WordTrace tailWord_1587887 prefixEnd_1587887 543566170683956079006631 := by
  unfold tailWord_1587887
  simp only [CollatzResearch.WordTrace]
  refine ⟨57914996798364063354209915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38609997865576042236139943 57914996798364063354209915)
  ·
    refine ⟨86872495197546095031314873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57914996798364063354209915 86872495197546095031314873)
    ·
      refine ⟨65154371398159571273486155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86872495197546095031314873 65154371398159571273486155)
      ·
        refine ⟨97731557097239356910229233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65154371398159571273486155 97731557097239356910229233)
        ·
          refine ⟨73298667822929517682671925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97731557097239356910229233 73298667822929517682671925)
          ·
            refine ⟨6871750108399642282750493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73298667822929517682671925 6871750108399642282750493)
            ·
              refine ⟨2576906290649865856031435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6871750108399642282750493 2576906290649865856031435)
              ·
                refine ⟨3865359435974798784047153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576906290649865856031435 3865359435974798784047153)
                ·
                  refine ⟨2899019576981099088035365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865359435974798784047153 2899019576981099088035365)
                  ·
                    refine ⟨543566170683956079006631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2899019576981099088035365 543566170683956079006631)
                    ·
                      rfl

theorem cell22_1587887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_1587887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587887 prefixEnd_1587887 := by exact prefixLift 1587887
  have htrace : WordTrace (prefixWord ++ tailWord_1587887) baseStart_1587887 baseEnd_1587887 := by
    simpa [prefixWord, tailWord_1587887, baseEnd_1587887] using wordTrace_append hprefix tailTrace_1587887
  have hstable : (prefixWord ++ tailWord_1587887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587887).length < 2 ^ (prefixWord ++ tailWord_1587887).sum := by decide
  have hdescent : baseEnd_1587887 < baseStart_1587887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587945 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_1587945 : Nat := 118140960795 + 1587945 * 2 ^ 59
def prefixEnd_1587945 : Nat := 4983230072969 + 3 ^ 40 * 1587945 * 2
def baseEnd_1587945 : Nat := 543586025269263261056453

theorem tailTrace_1587945 : CollatzResearch.WordTrace tailWord_1587945 prefixEnd_1587945 543586025269263261056453 := by
  unfold tailWord_1587945
  simp only [CollatzResearch.WordTrace]
  refine ⟨57917112232153939259821289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38611408154769292839880859 57917112232153939259821289)
  ·
    refine ⟨43437834174115454444865967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57917112232153939259821289 43437834174115454444865967)
    ·
      refine ⟨65156751261173181667298951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43437834174115454444865967 65156751261173181667298951)
      ·
        refine ⟨97735126891759772500948427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65156751261173181667298951 97735126891759772500948427)
        ·
          refine ⟨146602690337639658751422641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97735126891759772500948427 146602690337639658751422641)
          ·
            refine ⟨109952017753229744063566981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146602690337639658751422641 109952017753229744063566981)
            ·
              refine ⟨20616003328730577011918809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109952017753229744063566981 20616003328730577011918809)
              ·
                refine ⟨15462002496547932758939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20616003328730577011918809 15462002496547932758939107)
                ·
                  refine ⟨23193003744821899138408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15462002496547932758939107 23193003744821899138408661)
                  ·
                    refine ⟨543586025269263261056453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23193003744821899138408661 543586025269263261056453)
                    ·
                      rfl

theorem cell22_1587945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_1587945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587945 prefixEnd_1587945 := by exact prefixLift 1587945
  have htrace : WordTrace (prefixWord ++ tailWord_1587945) baseStart_1587945 baseEnd_1587945 := by
    simpa [prefixWord, tailWord_1587945, baseEnd_1587945] using wordTrace_append hprefix tailTrace_1587945
  have hstable : (prefixWord ++ tailWord_1587945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587945).length < 2 ^ (prefixWord ++ tailWord_1587945).sum := by decide
  have hdescent : baseEnd_1587945 < baseStart_1587945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587951 : List Nat := [1, 1, 2, 1, 5, 2, 3, 3, 1, 3]
def baseStart_1587951 : Nat := 118140960795 + 1587951 * 2 ^ 59
def prefixEnd_1587951 : Nat := 4983230072969 + 3 ^ 40 * 1587951 * 2
def baseEnd_1587951 : Nat := 543588079191881245406435

theorem tailTrace_1587951 : CollatzResearch.WordTrace tailWord_1587951 prefixEnd_1587951 543588079191881245406435 := by
  unfold tailWord_1587951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57917331070132202284539707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38611554046754801523026471 57917331070132202284539707)
  ·
    refine ⟨86875996605198303426809561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57917331070132202284539707 86875996605198303426809561)
    ·
      refine ⟨65156997453898727570107171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86875996605198303426809561 65156997453898727570107171)
      ·
        refine ⟨97735496180848091355160757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65156997453898727570107171 97735496180848091355160757)
        ·
          refine ⟨9162702766954508564546321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97735496180848091355160757 9162702766954508564546321)
          ·
            refine ⟨6872027075215881423409741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9162702766954508564546321 6872027075215881423409741)
            ·
              refine ⟨2577010153205955533778653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6872027075215881423409741 2577010153205955533778653)
              ·
                refine ⟨966378807452233325166995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2577010153205955533778653 966378807452233325166995)
                ·
                  refine ⟨1449568211178349987750493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966378807452233325166995 1449568211178349987750493)
                  ·
                    refine ⟨543588079191881245406435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449568211178349987750493 543588079191881245406435)
                    ·
                      rfl

theorem cell22_1587951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_1587951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1587951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1587951 prefixEnd_1587951 := by exact prefixLift 1587951
  have htrace : WordTrace (prefixWord ++ tailWord_1587951) baseStart_1587951 baseEnd_1587951 := by
    simpa [prefixWord, tailWord_1587951, baseEnd_1587951] using wordTrace_append hprefix tailTrace_1587951
  have hstable : (prefixWord ++ tailWord_1587951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587951).length < 2 ^ (prefixWord ++ tailWord_1587951).sum := by decide
  have hdescent : baseEnd_1587951 < baseStart_1587951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588026 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_1588026 : Nat := 118140960795 + 1588026 * 2 ^ 59
def prefixEnd_1588026 : Nat := 4983230072969 + 3 ^ 40 * 1588026 * 2
def baseEnd_1588026 : Nat := 181204584408202016593735

theorem tailTrace_1588026 : CollatzResearch.WordTrace tailWord_1588026 prefixEnd_1588026 181204584408202016593735 := by
  unfold tailWord_1588026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480016636215122523379983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38613377696573660062346621 14480016636215122523379983)
  ·
    refine ⟨21720024954322683785069975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14480016636215122523379983 21720024954322683785069975)
    ·
      refine ⟨32580037431484025677604963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21720024954322683785069975 32580037431484025677604963)
      ·
        refine ⟨48870056147226038516407445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32580037431484025677604963 48870056147226038516407445)
        ·
          refine ⟨2290783881901220555456599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48870056147226038516407445 2290783881901220555456599)
          ·
            refine ⟨3436175822851830833184899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290783881901220555456599 3436175822851830833184899)
            ·
              refine ⟨5154263734277746249777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436175822851830833184899 5154263734277746249777349)
              ·
                refine ⟨966424450177077421833253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5154263734277746249777349 966424450177077421833253)
                ·
                  refine ⟨181204584408202016593735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966424450177077421833253 181204584408202016593735)
                  ·
                    rfl

theorem cell22_1588026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_1588026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588026 prefixEnd_1588026 := by exact prefixLift 1588026
  have htrace : WordTrace (prefixWord ++ tailWord_1588026) baseStart_1588026 baseEnd_1588026 := by
    simpa [prefixWord, tailWord_1588026, baseEnd_1588026] using wordTrace_append hprefix tailTrace_1588026
  have hstable : (prefixWord ++ tailWord_1588026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588026).length < 2 ^ (prefixWord ++ tailWord_1588026).sum := by decide
  have hdescent : baseEnd_1588026 < baseStart_1588026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588159 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 6, 3]
def baseStart_1588159 : Nat := 118140960795 + 1588159 * 2 ^ 59
def prefixEnd_1588159 : Nat := 4983230072969 + 3 ^ 40 * 1588159 * 2
def baseEnd_1588159 : Nat := 543659281842638036205797

theorem tailTrace_1588159 : CollatzResearch.WordTrace tailWord_1588159 prefixEnd_1588159 543659281842638036205797 := by
  unfold tailWord_1588159
  simp only [CollatzResearch.WordTrace]
  refine ⟨57924917453378653808111531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38616611635585769205407687 57924917453378653808111531)
  ·
    refine ⟨86887376180067980712167297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57924917453378653808111531 86887376180067980712167297)
    ·
      refine ⟨65165532135050985534125473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86887376180067980712167297 65165532135050985534125473)
      ·
        refine ⟨48874149101288239150594105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65165532135050985534125473 48874149101288239150594105)
        ·
          refine ⟨36655611825966179362945579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48874149101288239150594105 36655611825966179362945579)
          ·
            refine ⟨54983417738949269044418369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36655611825966179362945579 54983417738949269044418369)
            ·
              refine ⟨41237563304211951783313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54983417738949269044418369 41237563304211951783313777)
              ·
                refine ⟨30928172478158963837485333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41237563304211951783313777 30928172478158963837485333)
                ·
                  refine ⟨1449758084913701429882125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30928172478158963837485333 1449758084913701429882125)
                  ·
                    refine ⟨543659281842638036205797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449758084913701429882125 543659281842638036205797)
                    ·
                      rfl

theorem cell22_1588159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_1588159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588159 prefixEnd_1588159 := by exact prefixLift 1588159
  have htrace : WordTrace (prefixWord ++ tailWord_1588159) baseStart_1588159 baseEnd_1588159 := by
    simpa [prefixWord, tailWord_1588159, baseEnd_1588159] using wordTrace_append hprefix tailTrace_1588159
  have hstable : (prefixWord ++ tailWord_1588159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588159).length < 2 ^ (prefixWord ++ tailWord_1588159).sum := by decide
  have hdescent : baseEnd_1588159 < baseStart_1588159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588189 : List Nat := [1, 4, 3, 1, 2, 11]
def baseStart_1588189 : Nat := 118140960795 + 1588189 * 2 ^ 59
def prefixEnd_1588189 : Nat := 4983230072969 + 3 ^ 40 * 1588189 * 2
def baseEnd_1588189 : Nat := 6711969771058369851305

theorem tailTrace_1588189 : CollatzResearch.WordTrace tailWord_1588189 prefixEnd_1588189 6711969771058369851305 := by
  unfold tailWord_1588189
  simp only [CollatzResearch.WordTrace]
  refine ⟨57926011643269968931703621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38617341095513312621135747 57926011643269968931703621)
  ·
    refine ⟨10861127183113119174694429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57926011643269968931703621 10861127183113119174694429)
    ·
      refine ⟨4072922693667419690510411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10861127183113119174694429 4072922693667419690510411)
      ·
        refine ⟨6109384040501129535765617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072922693667419690510411 6109384040501129535765617)
        ·
          refine ⟨4582038030375847151824213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6109384040501129535765617 4582038030375847151824213)
          ·
            refine ⟨6711969771058369851305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4582038030375847151824213 6711969771058369851305)
            ·
              rfl

theorem cell22_1588189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 11].length) (baseStart_1588189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588189 prefixEnd_1588189 := by exact prefixLift 1588189
  have htrace : WordTrace (prefixWord ++ tailWord_1588189) baseStart_1588189 baseEnd_1588189 := by
    simpa [prefixWord, tailWord_1588189, baseEnd_1588189] using wordTrace_append hprefix tailTrace_1588189
  have hstable : (prefixWord ++ tailWord_1588189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588189).length < 2 ^ (prefixWord ++ tailWord_1588189).sum := by decide
  have hdescent : baseEnd_1588189 < baseStart_1588189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588212 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1588212 : Nat := 118140960795 + 1588212 * 2 ^ 59
def prefixEnd_1588212 : Nat := 4983230072969 + 3 ^ 40 * 1588212 * 2
def baseEnd_1588212 : Nat := 181225808275254521543545

theorem tailTrace_1588212 : CollatzResearch.WordTrace tailWord_1588212 prefixEnd_1588212 181225808275254521543545 := by
  unfold tailWord_1588212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28963425261093321929895445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38617900348124429239860593 28963425261093321929895445)
  ·
    refine ⟨1357660559113749465463849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28963425261093321929895445 1357660559113749465463849)
    ·
      refine ⟨1018245419335312099097887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1357660559113749465463849 1018245419335312099097887)
      ·
        refine ⟨1527368129002968148646831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018245419335312099097887 1527368129002968148646831)
        ·
          refine ⟨2291052193504452222970247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527368129002968148646831 2291052193504452222970247)
          ·
            refine ⟨3436578290256678334455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291052193504452222970247 3436578290256678334455371)
            ·
              refine ⟨5154867435385017501683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436578290256678334455371 5154867435385017501683057)
              ·
                refine ⟨3866150576538763126262293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154867435385017501683057 3866150576538763126262293)
                ·
                  refine ⟨181225808275254521543545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3866150576538763126262293 181225808275254521543545)
                  ·
                    rfl

theorem cell22_1588212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1588212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588212 prefixEnd_1588212 := by exact prefixLift 1588212
  have htrace : WordTrace (prefixWord ++ tailWord_1588212) baseStart_1588212 baseEnd_1588212 := by
    simpa [prefixWord, tailWord_1588212, baseEnd_1588212] using wordTrace_append hprefix tailTrace_1588212
  have hstable : (prefixWord ++ tailWord_1588212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588212).length < 2 ^ (prefixWord ++ tailWord_1588212).sum := by decide
  have hdescent : baseEnd_1588212 < baseStart_1588212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588249 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_1588249 : Nat := 118140960795 + 1588249 * 2 ^ 59
def prefixEnd_1588249 : Nat := 4983230072969 + 3 ^ 40 * 1588249 * 2
def baseEnd_1588249 : Nat := 543690090681907801455521

theorem tailTrace_1588249 : CollatzResearch.WordTrace tailWord_1588249 prefixEnd_1588249 543690090681907801455521 := by
  unfold tailWord_1588249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57928200023052599178887801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38618800015368399452591867 57928200023052599178887801)
  ·
    refine ⟨43446150017289449384165851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57928200023052599178887801 43446150017289449384165851)
    ·
      refine ⟨65169225025934174076248777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43446150017289449384165851 65169225025934174076248777)
      ·
        refine ⟨48876918769450630557186583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65169225025934174076248777 48876918769450630557186583)
        ·
          refine ⟨73315378154175945835779875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48876918769450630557186583 73315378154175945835779875)
          ·
            refine ⟨109973067231263918753669813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73315378154175945835779875 109973067231263918753669813)
            ·
              refine ⟨10309975052930992383156545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109973067231263918753669813 10309975052930992383156545)
              ·
                refine ⟨7732481289698244287367409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309975052930992383156545 7732481289698244287367409)
                ·
                  refine ⟨5799360967273683215525557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7732481289698244287367409 5799360967273683215525557)
                  ·
                    refine ⟨543690090681907801455521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5799360967273683215525557 543690090681907801455521)
                    ·
                      rfl

theorem cell22_1588249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_1588249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588249 prefixEnd_1588249 := by exact prefixLift 1588249
  have htrace : WordTrace (prefixWord ++ tailWord_1588249) baseStart_1588249 baseEnd_1588249 := by
    simpa [prefixWord, tailWord_1588249, baseEnd_1588249] using wordTrace_append hprefix tailTrace_1588249
  have hstable : (prefixWord ++ tailWord_1588249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588249).length < 2 ^ (prefixWord ++ tailWord_1588249).sum := by decide
  have hdescent : baseEnd_1588249 < baseStart_1588249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588289 : List Nat := [1, 2, 5, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1588289 : Nat := 118140960795 + 1588289 * 2 ^ 59
def prefixEnd_1588289 : Nat := 4983230072969 + 3 ^ 40 * 1588289 * 2
def baseEnd_1588289 : Nat := 543703783499361030455399

theorem tailTrace_1588289 : CollatzResearch.WordTrace tailWord_1588289 prefixEnd_1588289 543703783499361030455399 := by
  unfold tailWord_1588289
  simp only [CollatzResearch.WordTrace]
  refine ⟨57929658942907686010343921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38619772628605124006895947 57929658942907686010343921)
  ·
    refine ⟨43447244207180764507757941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57929658942907686010343921 43447244207180764507757941)
    ·
      refine ⟨4073179144423196672602307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43447244207180764507757941 4073179144423196672602307)
      ·
        refine ⟨6109768716634795008903461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073179144423196672602307 6109768716634795008903461)
        ·
          refine ⟨1145581634369024064169399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6109768716634795008903461 1145581634369024064169399)
          ·
            refine ⟨1718372451553536096254099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145581634369024064169399 1718372451553536096254099)
            ·
              refine ⟨2577558677330304144381149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718372451553536096254099 2577558677330304144381149)
              ·
                refine ⟨966584503998864054142931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2577558677330304144381149 966584503998864054142931)
                ·
                  refine ⟨1449876755998296081214397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966584503998864054142931 1449876755998296081214397)
                  ·
                    refine ⟨543703783499361030455399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1449876755998296081214397 543703783499361030455399)
                    ·
                      rfl

theorem cell22_1588289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1588289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588289 prefixEnd_1588289 := by exact prefixLift 1588289
  have htrace : WordTrace (prefixWord ++ tailWord_1588289) baseStart_1588289 baseEnd_1588289 := by
    simpa [prefixWord, tailWord_1588289, baseEnd_1588289] using wordTrace_append hprefix tailTrace_1588289
  have hstable : (prefixWord ++ tailWord_1588289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588289).length < 2 ^ (prefixWord ++ tailWord_1588289).sum := by decide
  have hdescent : baseEnd_1588289 < baseStart_1588289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588482 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1588482 : Nat := 118140960795 + 1588482 * 2 ^ 59
def prefixEnd_1588482 : Nat := 4983230072969 + 3 ^ 40 * 1588482 * 2
def baseEnd_1588482 : Nat := 181256617114524286793269

theorem tailTrace_1588482 : CollatzResearch.WordTrace tailWord_1588482 prefixEnd_1588482 181256617114524286793269 := by
  unfold tailWord_1588482
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484174557802119993029925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38624465487472319981413133 14484174557802119993029925)
  ·
    refine ⟨2715782729587897498693111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14484174557802119993029925 2715782729587897498693111)
    ·
      refine ⟨4073674094381846248039667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715782729587897498693111 4073674094381846248039667)
      ·
        refine ⟨6110511141572769372059501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073674094381846248039667 6110511141572769372059501)
        ·
          refine ⟨2291441678089788514522313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6110511141572769372059501 2291441678089788514522313)
          ·
            refine ⟨1718581258567341385891735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291441678089788514522313 1718581258567341385891735)
            ·
              refine ⟨2577871887851012078837603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718581258567341385891735 2577871887851012078837603)
              ·
                refine ⟨3866807831776518118256405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577871887851012078837603 3866807831776518118256405)
                ·
                  refine ⟨181256617114524286793269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3866807831776518118256405 181256617114524286793269)
                  ·
                    rfl

theorem cell22_1588482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1588482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588482 prefixEnd_1588482 := by exact prefixLift 1588482
  have htrace : WordTrace (prefixWord ++ tailWord_1588482) baseStart_1588482 baseEnd_1588482 := by
    simpa [prefixWord, tailWord_1588482, baseEnd_1588482] using wordTrace_append hprefix tailTrace_1588482
  have hstable : (prefixWord ++ tailWord_1588482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588482).length < 2 ^ (prefixWord ++ tailWord_1588482).sum := by decide
  have hdescent : baseEnd_1588482 < baseStart_1588482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588568 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1588568 : Nat := 118140960795 + 1588568 * 2 ^ 59
def prefixEnd_1588568 : Nat := 4983230072969 + 3 ^ 40 * 1588568 * 2
def baseEnd_1588568 : Nat := 543799290901097302729543

theorem tailTrace_1588568 : CollatzResearch.WordTrace tailWord_1588568 prefixEnd_1588568 543799290901097302729543 := by
  unfold tailWord_1588568
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969917454448458329875179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38626556605931277773166905 28969917454448458329875179)
  ·
    refine ⟨43454876181672687494812769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28969917454448458329875179 43454876181672687494812769)
    ·
      refine ⟨32591157136254515621109577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43454876181672687494812769 32591157136254515621109577)
      ·
        refine ⟨24443367852190886715832183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32591157136254515621109577 24443367852190886715832183)
        ·
          refine ⟨36665051778286330073748275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24443367852190886715832183 36665051778286330073748275)
          ·
            refine ⟨54997577667429495110622413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36665051778286330073748275 54997577667429495110622413)
            ·
              refine ⟨20624091625286060666483405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54997577667429495110622413 20624091625286060666483405)
              ·
                refine ⟨7734034359482272749931277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20624091625286060666483405 7734034359482272749931277)
                ·
                  refine ⟨2900262884805852281224229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7734034359482272749931277 2900262884805852281224229)
                  ·
                    refine ⟨543799290901097302729543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900262884805852281224229 543799290901097302729543)
                    ·
                      rfl

theorem cell22_1588568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1588568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588568 prefixEnd_1588568 := by exact prefixLift 1588568
  have htrace : WordTrace (prefixWord ++ tailWord_1588568) baseStart_1588568 baseEnd_1588568 := by
    simpa [prefixWord, tailWord_1588568, baseEnd_1588568] using wordTrace_append hprefix tailTrace_1588568
  have hstable : (prefixWord ++ tailWord_1588568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588568).length < 2 ^ (prefixWord ++ tailWord_1588568).sum := by decide
  have hdescent : baseEnd_1588568 < baseStart_1588568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588606 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1588606 : Nat := 118140960795 + 1588606 * 2 ^ 59
def prefixEnd_1588606 : Nat := 4983230072969 + 3 ^ 40 * 1588606 * 2
def baseEnd_1588606 : Nat := 181270766359225956759809

theorem tailTrace_1588606 : CollatzResearch.WordTrace tailWord_1588606 prefixEnd_1588606 181270766359225956759809 := by
  unfold tailWord_1588606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242652610344906143704209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38627480588506166099755781 7242652610344906143704209)
  ·
    refine ⟨5431989457758679607778157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7242652610344906143704209 5431989457758679607778157)
    ·
      refine ⟨2036996046659504852916809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5431989457758679607778157 2036996046659504852916809)
      ·
        refine ⟨1527747034994628639687607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036996046659504852916809 1527747034994628639687607)
        ·
          refine ⟨2291620552491942959531411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527747034994628639687607 2291620552491942959531411)
          ·
            refine ⟨3437430828737914439297117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291620552491942959531411 3437430828737914439297117)
            ·
              refine ⟨1289036560776717914736419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3437430828737914439297117 1289036560776717914736419)
              ·
                refine ⟨1933554841165076872104629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289036560776717914736419 1933554841165076872104629)
                ·
                  refine ⟨181270766359225956759809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1933554841165076872104629 181270766359225956759809)
                  ·
                    rfl

theorem cell22_1588606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1588606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588606 prefixEnd_1588606 := by exact prefixLift 1588606
  have htrace : WordTrace (prefixWord ++ tailWord_1588606) baseStart_1588606 baseEnd_1588606 := by
    simpa [prefixWord, tailWord_1588606, baseEnd_1588606] using wordTrace_append hprefix tailTrace_1588606
  have hstable : (prefixWord ++ tailWord_1588606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588606).length < 2 ^ (prefixWord ++ tailWord_1588606).sum := by decide
  have hdescent : baseEnd_1588606 < baseStart_1588606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588613 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_1588613 : Nat := 118140960795 + 1588613 * 2 ^ 59
def prefixEnd_1588613 : Nat := 4983230072969 + 3 ^ 40 * 1588613 * 2
def baseEnd_1588613 : Nat := 543814695320732185354405

theorem tailTrace_1588613 : CollatzResearch.WordTrace tailWord_1588613 prefixEnd_1588613 543814695320732185354405 := by
  unfold tailWord_1588613
  simp only [CollatzResearch.WordTrace]
  refine ⟨57941476193733889345138493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38627650795822592896758995 57941476193733889345138493)
  ·
    refine ⟨21728053572650208504426935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57941476193733889345138493 21728053572650208504426935)
    ·
      refine ⟨32592080358975312756640403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21728053572650208504426935 32592080358975312756640403)
      ·
        refine ⟨48888120538462969134960605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32592080358975312756640403 48888120538462969134960605)
        ·
          refine ⟨18333045201923613425610227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48888120538462969134960605 18333045201923613425610227)
          ·
            refine ⟨27499567802885420138415341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18333045201923613425610227 27499567802885420138415341)
            ·
              refine ⟨10312337926082032551905753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27499567802885420138415341 10312337926082032551905753)
              ·
                refine ⟨7734253444561524413929315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312337926082032551905753 7734253444561524413929315)
                ·
                  refine ⟨11601380166842286620893973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7734253444561524413929315 11601380166842286620893973)
                  ·
                    refine ⟨543814695320732185354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11601380166842286620893973 543814695320732185354405)
                    ·
                      rfl

theorem cell22_1588613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_1588613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588613 prefixEnd_1588613 := by exact prefixLift 1588613
  have htrace : WordTrace (prefixWord ++ tailWord_1588613) baseStart_1588613 baseEnd_1588613 := by
    simpa [prefixWord, tailWord_1588613, baseEnd_1588613] using wordTrace_append hprefix tailTrace_1588613
  have hstable : (prefixWord ++ tailWord_1588613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588613).length < 2 ^ (prefixWord ++ tailWord_1588613).sum := by decide
  have hdescent : baseEnd_1588613 < baseStart_1588613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588615 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1588615 : Nat := 118140960795 + 1588615 * 2 ^ 59
def prefixEnd_1588615 : Nat := 4983230072969 + 3 ^ 40 * 1588615 * 2
def baseEnd_1588615 : Nat := 543815379961604846804399

theorem tailTrace_1588615 : CollatzResearch.WordTrace tailWord_1588615 prefixEnd_1588615 543815379961604846804399 := by
  unfold tailWord_1588615
  simp only [CollatzResearch.WordTrace]
  refine ⟨57941549139726643686711299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38627699426484429124474199 57941549139726643686711299)
  ·
    refine ⟨86912323709589965530066949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57941549139726643686711299 86912323709589965530066949)
    ·
      refine ⟨16296060695548118536887553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86912323709589965530066949 16296060695548118536887553)
      ·
        refine ⟨12222045521661088902665665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296060695548118536887553 12222045521661088902665665)
        ·
          refine ⟨9166534141245816676999249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12222045521661088902665665 9166534141245816676999249)
          ·
            refine ⟨6874900605934362507749437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9166534141245816676999249 6874900605934362507749437)
            ·
              refine ⟨2578087727225385940406039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874900605934362507749437 2578087727225385940406039)
              ·
                refine ⟨3867131590838078910609059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578087727225385940406039 3867131590838078910609059)
                ·
                  refine ⟨5800697386257118365913589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867131590838078910609059 5800697386257118365913589)
                  ·
                    refine ⟨543815379961604846804399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5800697386257118365913589 543815379961604846804399)
                    ·
                      rfl

theorem cell22_1588615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1588615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588615 prefixEnd_1588615 := by exact prefixLift 1588615
  have htrace : WordTrace (prefixWord ++ tailWord_1588615) baseStart_1588615 baseEnd_1588615 := by
    simpa [prefixWord, tailWord_1588615, baseEnd_1588615] using wordTrace_append hprefix tailTrace_1588615
  have hstable : (prefixWord ++ tailWord_1588615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588615).length < 2 ^ (prefixWord ++ tailWord_1588615).sum := by decide
  have hdescent : baseEnd_1588615 < baseStart_1588615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588688 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1588688 : Nat := 118140960795 + 1588688 * 2 ^ 59
def prefixEnd_1588688 : Nat := 4983230072969 + 3 ^ 40 * 1588688 * 2
def baseEnd_1588688 : Nat := 543840369353456989729175

theorem tailTrace_1588688 : CollatzResearch.WordTrace tailWord_1588688 prefixEnd_1588688 543840369353456989729175 := by
  unfold tailWord_1588688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972105834231088577059359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38629474445641451436079145 28972105834231088577059359)
  ·
    refine ⟨43458158751346632865589039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972105834231088577059359 43458158751346632865589039)
    ·
      refine ⟨65187238127019949298383559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43458158751346632865589039 65187238127019949298383559)
      ·
        refine ⟨97780857190529923947575339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65187238127019949298383559 97780857190529923947575339)
        ·
          refine ⟨146671285785794885921363009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97780857190529923947575339 146671285785794885921363009)
          ·
            refine ⟨110003464339346164441022257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146671285785794885921363009 110003464339346164441022257)
            ·
              refine ⟨82502598254509623330766693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110003464339346164441022257 82502598254509623330766693)
              ·
                refine ⟨15469237172720554374518755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82502598254509623330766693 15469237172720554374518755)
                ·
                  refine ⟨23203855759080831561778133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469237172720554374518755 23203855759080831561778133)
                  ·
                    refine ⟨543840369353456989729175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23203855759080831561778133 543840369353456989729175)
                    ·
                      rfl

theorem cell22_1588688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1588688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588688 prefixEnd_1588688 := by exact prefixLift 1588688
  have htrace : WordTrace (prefixWord ++ tailWord_1588688) baseStart_1588688 baseEnd_1588688 := by
    simpa [prefixWord, tailWord_1588688, baseEnd_1588688] using wordTrace_append hprefix tailTrace_1588688
  have hstable : (prefixWord ++ tailWord_1588688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588688).length < 2 ^ (prefixWord ++ tailWord_1588688).sum := by decide
  have hdescent : baseEnd_1588688 < baseStart_1588688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588707 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 5]
def baseStart_1588707 : Nat := 118140960795 + 1588707 * 2 ^ 59
def prefixEnd_1588707 : Nat := 4983230072969 + 3 ^ 40 * 1588707 * 2
def baseEnd_1588707 : Nat := 181282291147249091168039

theorem tailTrace_1588707 : CollatzResearch.WordTrace tailWord_1588707 prefixEnd_1588707 181282291147249091168039 := by
  unfold tailWord_1588707
  simp only [CollatzResearch.WordTrace]
  refine ⟨57944904655393343399060375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38629936436928895599373583 57944904655393343399060375)
  ·
    refine ⟨86917356983090015098590563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57944904655393343399060375 86917356983090015098590563)
    ·
      refine ⟨130376035474635022647885845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86917356983090015098590563 130376035474635022647885845)
      ·
        refine ⟨6111376662873516686619649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130376035474635022647885845 6111376662873516686619649)
        ·
          refine ⟨4583532497155137514964737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111376662873516686619649 4583532497155137514964737)
          ·
            refine ⟨3437649372866353136223553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583532497155137514964737 3437649372866353136223553)
            ·
              refine ⟨2578237029649764852167665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437649372866353136223553 2578237029649764852167665)
              ·
                refine ⟨1933677772237323639125749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578237029649764852167665 1933677772237323639125749)
                ·
                  refine ⟨181282291147249091168039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1933677772237323639125749 181282291147249091168039)
                  ·
                    rfl

theorem cell22_1588707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].length) (baseStart_1588707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588707 prefixEnd_1588707 := by exact prefixLift 1588707
  have htrace : WordTrace (prefixWord ++ tailWord_1588707) baseStart_1588707 baseEnd_1588707 := by
    simpa [prefixWord, tailWord_1588707, baseEnd_1588707] using wordTrace_append hprefix tailTrace_1588707
  have hstable : (prefixWord ++ tailWord_1588707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588707).length < 2 ^ (prefixWord ++ tailWord_1588707).sum := by decide
  have hdescent : baseEnd_1588707 < baseStart_1588707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588711 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1588711 : Nat := 118140960795 + 1588711 * 2 ^ 59
def prefixEnd_1588711 : Nat := 4983230072969 + 3 ^ 40 * 1588711 * 2
def baseEnd_1588711 : Nat := 543848242723492596404105

theorem tailTrace_1588711 : CollatzResearch.WordTrace tailWord_1588711 prefixEnd_1588711 543848242723492596404105 := by
  unfold tailWord_1588711
  simp only [CollatzResearch.WordTrace]
  refine ⟨57945050547378852082205987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38630033698252568054803991 57945050547378852082205987)
  ·
    refine ⟨86917575821068278123308981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57945050547378852082205987 86917575821068278123308981)
    ·
      refine ⟨8148522733225151074060217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86917575821068278123308981 8148522733225151074060217)
      ·
        refine ⟨6111392049918863305545163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8148522733225151074060217 6111392049918863305545163)
        ·
          refine ⟨9167088074878294958317745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111392049918863305545163 9167088074878294958317745)
          ·
            refine ⟨6875316056158721218738309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167088074878294958317745 6875316056158721218738309)
            ·
              refine ⟨1289121760529760228513433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6875316056158721218738309 1289121760529760228513433)
              ·
                refine ⟨966841320397320171385075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289121760529760228513433 966841320397320171385075)
                ·
                  refine ⟨1450261980595980257077613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966841320397320171385075 1450261980595980257077613)
                  ·
                    refine ⟨543848242723492596404105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1450261980595980257077613 543848242723492596404105)
                    ·
                      rfl

theorem cell22_1588711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1588711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588711 prefixEnd_1588711 := by exact prefixLift 1588711
  have htrace : WordTrace (prefixWord ++ tailWord_1588711) baseStart_1588711 baseEnd_1588711 := by
    simpa [prefixWord, tailWord_1588711, baseEnd_1588711] using wordTrace_append hprefix tailTrace_1588711
  have hstable : (prefixWord ++ tailWord_1588711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588711).length < 2 ^ (prefixWord ++ tailWord_1588711).sum := by decide
  have hdescent : baseEnd_1588711 < baseStart_1588711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588720 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_1588720 : Nat := 118140960795 + 1588720 * 2 ^ 59
def prefixEnd_1588720 : Nat := 4983230072969 + 3 ^ 40 * 1588720 * 2
def baseEnd_1588720 : Nat := 543851323607419572929077

theorem tailTrace_1588720 : CollatzResearch.WordTrace tailWord_1588720 prefixEnd_1588720 543851323607419572929077 := by
  unfold tailWord_1588720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972689402173123309641807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38630252536230831079522409 28972689402173123309641807)
  ·
    refine ⟨43459034103259684964462711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972689402173123309641807 43459034103259684964462711)
    ·
      refine ⟨65188551154889527446694067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43459034103259684964462711 65188551154889527446694067)
      ·
        refine ⟨97782826732334291170041101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65188551154889527446694067 97782826732334291170041101)
        ·
          refine ⟨36668560024625359188765413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97782826732334291170041101 36668560024625359188765413)
          ·
            refine ⟨6875355004617254847893515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36668560024625359188765413 6875355004617254847893515)
            ·
              refine ⟨10313032506925882271840273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875355004617254847893515 10313032506925882271840273)
              ·
                refine ⟨7734774380194411703880205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10313032506925882271840273 7734774380194411703880205)
                ·
                  refine ⟨2900540392572904388955077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7734774380194411703880205 2900540392572904388955077)
                  ·
                    refine ⟨543851323607419572929077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2900540392572904388955077 543851323607419572929077)
                    ·
                      rfl

theorem cell22_1588720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_1588720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588720 prefixEnd_1588720 := by exact prefixLift 1588720
  have htrace : WordTrace (prefixWord ++ tailWord_1588720) baseStart_1588720 baseEnd_1588720 := by
    simpa [prefixWord, tailWord_1588720, baseEnd_1588720] using wordTrace_append hprefix tailTrace_1588720
  have hstable : (prefixWord ++ tailWord_1588720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588720).length < 2 ^ (prefixWord ++ tailWord_1588720).sum := by decide
  have hdescent : baseEnd_1588720 < baseStart_1588720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588722 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1588722 : Nat := 118140960795 + 1588722 * 2 ^ 59
def prefixEnd_1588722 : Nat := 4983230072969 + 3 ^ 40 * 1588722 * 2
def baseEnd_1588722 : Nat := 543852008248292234379071

theorem tailTrace_1588722 : CollatzResearch.WordTrace tailWord_1588722 prefixEnd_1588722 543852008248292234379071 := by
  unfold tailWord_1588722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486362937584750240214105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38630301166892667307237613 14486362937584750240214105)
  ·
    refine ⟨10864772203188562680160579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14486362937584750240214105 10864772203188562680160579)
    ·
      refine ⟨16297158304782844020240869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864772203188562680160579 16297158304782844020240869)
      ·
        refine ⟨3055717182146783253795163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16297158304782844020240869 3055717182146783253795163)
        ·
          refine ⟨4583575773220174880692745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055717182146783253795163 4583575773220174880692745)
          ·
            refine ⟨3437681829915131160519559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583575773220174880692745 3437681829915131160519559)
            ·
              refine ⟨5156522744872696740779339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437681829915131160519559 5156522744872696740779339)
              ·
                refine ⟨7734784117309045111169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156522744872696740779339 7734784117309045111169009)
                ·
                  refine ⟨5801088087981783833376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7734784117309045111169009 5801088087981783833376757)
                  ·
                    refine ⟨543852008248292234379071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5801088087981783833376757 543852008248292234379071)
                    ·
                      rfl

theorem cell22_1588722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1588722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588722 prefixEnd_1588722 := by exact prefixLift 1588722
  have htrace : WordTrace (prefixWord ++ tailWord_1588722) baseStart_1588722 baseEnd_1588722 := by
    simpa [prefixWord, tailWord_1588722, baseEnd_1588722] using wordTrace_append hprefix tailTrace_1588722
  have hstable : (prefixWord ++ tailWord_1588722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588722).length < 2 ^ (prefixWord ++ tailWord_1588722).sum := by decide
  have hdescent : baseEnd_1588722 < baseStart_1588722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588782 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1588782 : Nat := 118140960795 + 1588782 * 2 ^ 59
def prefixEnd_1588782 : Nat := 4983230072969 + 3 ^ 40 * 1588782 * 2
def baseEnd_1588782 : Nat := 543872547474472077878887

theorem tailTrace_1588782 : CollatzResearch.WordTrace tailWord_1588782 prefixEnd_1588782 543872547474472077878887 := by
  unfold tailWord_1588782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7243455016265203901005075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38631760086747754138693733 7243455016265203901005075)
  ·
    refine ⟨10865182524397805851507613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7243455016265203901005075 10865182524397805851507613)
    ·
      refine ⟨4074443446649177194315355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10865182524397805851507613 4074443446649177194315355)
      ·
        refine ⟨6111665169973765791473033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074443446649177194315355 6111665169973765791473033)
        ·
          refine ⟨4583748877480324343604775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111665169973765791473033 4583748877480324343604775)
          ·
            refine ⟨6875623316220486515407163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583748877480324343604775 6875623316220486515407163)
            ·
              refine ⟨10313434974330729773110745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875623316220486515407163 10313434974330729773110745)
              ·
                refine ⟨7735076230748047329833059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10313434974330729773110745 7735076230748047329833059)
                ·
                  refine ⟨11602614346122070994749589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7735076230748047329833059 11602614346122070994749589)
                  ·
                    refine ⟨543872547474472077878887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11602614346122070994749589 543872547474472077878887)
                    ·
                      rfl

theorem cell22_1588782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1588782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1588782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1588782 prefixEnd_1588782 := by exact prefixLift 1588782
  have htrace : WordTrace (prefixWord ++ tailWord_1588782) baseStart_1588782 baseEnd_1588782 := by
    simpa [prefixWord, tailWord_1588782, baseEnd_1588782] using wordTrace_append hprefix tailTrace_1588782
  have hstable : (prefixWord ++ tailWord_1588782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588782).length < 2 ^ (prefixWord ++ tailWord_1588782).sum := by decide
  have hdescent : baseEnd_1588782 < baseStart_1588782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
