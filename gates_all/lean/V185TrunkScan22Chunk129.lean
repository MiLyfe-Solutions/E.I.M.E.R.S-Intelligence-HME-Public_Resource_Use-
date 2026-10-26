import V185TrunkScan22Chunk128

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1154639 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1154639 : Nat := 118140960795 + 1154639 * 2 ^ 59
def prefixEnd_1154639 : Nat := 4983230072969 + 3 ^ 40 * 1154639 * 2
def baseEnd_1154639 : Nat := 395256526284542135534945

theorem tailTrace_1154639 : CollatzResearch.WordTrace tailWord_1154639 prefixEnd_1154639 395256526284542135534945 := by
  unfold tailWord_1154639
  simp only [CollatzResearch.WordTrace]
  refine ⟨42113144063947574486682971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28075429375965049657788647 42113144063947574486682971)
  ·
    refine ⟨63169716095921361730024457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42113144063947574486682971 63169716095921361730024457)
    ·
      refine ⟨47377287071941021297518343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63169716095921361730024457 47377287071941021297518343)
      ·
        refine ⟨71065930607911531946277515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47377287071941021297518343 71065930607911531946277515)
        ·
          refine ⟨106598895911867297919416273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71065930607911531946277515 106598895911867297919416273)
          ·
            refine ⟨79949171933900473439562205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106598895911867297919416273 79949171933900473439562205)
            ·
              refine ⟨29980939475212677539835827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79949171933900473439562205 29980939475212677539835827)
              ·
                refine ⟨44971409212819016309753741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29980939475212677539835827 44971409212819016309753741)
                ·
                  refine ⟨16864278454807131116157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44971409212819016309753741 16864278454807131116157653)
                  ·
                    refine ⟨395256526284542135534945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16864278454807131116157653 395256526284542135534945)
                    ·
                      rfl

theorem cell22_1154639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1154639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154639 prefixEnd_1154639 := by exact prefixLift 1154639
  have htrace : WordTrace (prefixWord ++ tailWord_1154639) baseStart_1154639 baseEnd_1154639 := by
    simpa [prefixWord, tailWord_1154639, baseEnd_1154639] using wordTrace_append hprefix tailTrace_1154639
  have hstable : (prefixWord ++ tailWord_1154639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154639).length < 2 ^ (prefixWord ++ tailWord_1154639).sum := by decide
  have hdescent : baseEnd_1154639 < baseStart_1154639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154688 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_1154688 : Nat := 118140960795 + 1154688 * 2 ^ 59
def prefixEnd_1154688 : Nat := 4983230072969 + 3 ^ 40 * 1154688 * 2
def baseEnd_1154688 : Nat := 395273299985922341059795

theorem tailTrace_1154688 : CollatzResearch.WordTrace tailWord_1154688 prefixEnd_1154688 395273299985922341059795 := by
  unfold tailWord_1154688
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057465620385027927608359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28076620827180037236811145 21057465620385027927608359)
  ·
    refine ⟨31586198430577541891412539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21057465620385027927608359 31586198430577541891412539)
    ·
      refine ⟨47379297645866312837118809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31586198430577541891412539 47379297645866312837118809)
      ·
        refine ⟨35534473234399734627839107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47379297645866312837118809 35534473234399734627839107)
        ·
          refine ⟨53301709851599601941758661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35534473234399734627839107 53301709851599601941758661)
          ·
            refine ⟨9994070597174925364079749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53301709851599601941758661 9994070597174925364079749)
            ·
              refine ⟨1873888236970298505764953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9994070597174925364079749 1873888236970298505764953)
              ·
                refine ⟨1405416177727723879323715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873888236970298505764953 1405416177727723879323715)
                ·
                  refine ⟨2108124266591585818985573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405416177727723879323715 2108124266591585818985573)
                  ·
                    refine ⟨395273299985922341059795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108124266591585818985573 395273299985922341059795)
                    ·
                      rfl

theorem cell22_1154688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_1154688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154688 prefixEnd_1154688 := by exact prefixLift 1154688
  have htrace : WordTrace (prefixWord ++ tailWord_1154688) baseStart_1154688 baseEnd_1154688 := by
    simpa [prefixWord, tailWord_1154688, baseEnd_1154688] using wordTrace_append hprefix tailTrace_1154688
  have hstable : (prefixWord ++ tailWord_1154688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154688).length < 2 ^ (prefixWord ++ tailWord_1154688).sum := by decide
  have hdescent : baseEnd_1154688 < baseStart_1154688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154696 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_1154696 : Nat := 118140960795 + 1154696 * 2 ^ 59
def prefixEnd_1154696 : Nat := 4983230072969 + 3 ^ 40 * 1154696 * 2
def baseEnd_1154696 : Nat := 395276038549412986859771

theorem tailTrace_1154696 : CollatzResearch.WordTrace tailWord_1154696 prefixEnd_1154696 395276038549412986859771 := by
  unfold tailWord_1154696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057611512370536610753971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28076815349827382147671961 21057611512370536610753971)
  ·
    refine ⟨31586417268555804916130957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21057611512370536610753971 31586417268555804916130957)
    ·
      refine ⟨11844906475708426843549109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31586417268555804916130957 11844906475708426843549109)
      ·
        refine ⟨1110459982097665016582729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11844906475708426843549109 1110459982097665016582729)
        ·
          refine ⟨832844986573248762437047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110459982097665016582729 832844986573248762437047)
          ·
            refine ⟨1249267479859873143655571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832844986573248762437047 1249267479859873143655571)
            ·
              refine ⟨1873901219789809715483357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249267479859873143655571 1873901219789809715483357)
              ·
                refine ⟨702712957421178643306259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873901219789809715483357 702712957421178643306259)
                ·
                  refine ⟨1054069436131767964959389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702712957421178643306259 1054069436131767964959389)
                  ·
                    refine ⟨395276038549412986859771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054069436131767964959389 395276038549412986859771)
                    ·
                      rfl

theorem cell22_1154696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_1154696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154696 prefixEnd_1154696 := by exact prefixLift 1154696
  have htrace : WordTrace (prefixWord ++ tailWord_1154696) baseStart_1154696 baseEnd_1154696 := by
    simpa [prefixWord, tailWord_1154696, baseEnd_1154696] using wordTrace_append hprefix tailTrace_1154696
  have hstable : (prefixWord ++ tailWord_1154696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154696).length < 2 ^ (prefixWord ++ tailWord_1154696).sum := by decide
  have hdescent : baseEnd_1154696 < baseStart_1154696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154733 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1154733 : Nat := 118140960795 + 1154733 * 2 ^ 59
def prefixEnd_1154733 : Nat := 4983230072969 + 3 ^ 40 * 1154733 * 2
def baseEnd_1154733 : Nat := 395288704405557223684657

theorem tailTrace_1154733 : CollatzResearch.WordTrace tailWord_1154733 prefixEnd_1154733 395288704405557223684657 := by
  unfold tailWord_1154733
  simp only [CollatzResearch.WordTrace]
  refine ⟨42116572525607028540604853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28077715017071352360403235 42116572525607028540604853)
  ·
    refine ⟨3948428674275658925681705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42116572525607028540604853 3948428674275658925681705)
    ·
      refine ⟨2961321505706744194261279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3948428674275658925681705 2961321505706744194261279)
      ·
        refine ⟨4441982258560116291391919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2961321505706744194261279 4441982258560116291391919)
        ·
          refine ⟨6662973387840174437087879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4441982258560116291391919 6662973387840174437087879)
          ·
            refine ⟨9994460081760261655631819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6662973387840174437087879 9994460081760261655631819)
            ·
              refine ⟨14991690122640392483447729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9994460081760261655631819 14991690122640392483447729)
              ·
                refine ⟨11243767591980294362585797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14991690122640392483447729 11243767591980294362585797)
                ·
                  refine ⟨2108206423496305192984837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11243767591980294362585797 2108206423496305192984837)
                  ·
                    refine ⟨395288704405557223684657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108206423496305192984837 395288704405557223684657)
                    ·
                      rfl

theorem cell22_1154733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1154733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154733 prefixEnd_1154733 := by exact prefixLift 1154733
  have htrace : WordTrace (prefixWord ++ tailWord_1154733) baseStart_1154733 baseEnd_1154733 := by
    simpa [prefixWord, tailWord_1154733, baseEnd_1154733] using wordTrace_append hprefix tailTrace_1154733
  have hstable : (prefixWord ++ tailWord_1154733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154733).length < 2 ^ (prefixWord ++ tailWord_1154733).sum := by decide
  have hdescent : baseEnd_1154733 < baseStart_1154733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154750 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1154750 : Nat := 118140960795 + 1154750 * 2 ^ 59
def prefixEnd_1154750 : Nat := 4983230072969 + 3 ^ 40 * 1154750 * 2
def baseEnd_1154750 : Nat := 395294523852974846009605

theorem tailTrace_1154750 : CollatzResearch.WordTrace tailWord_1154750 prefixEnd_1154750 395294523852974846009605 := by
  unfold tailWord_1154750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5264649070818180055496713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28078128377696960295982469 5264649070818180055496713)
  ·
    refine ⟨3948486803113635041622535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5264649070818180055496713 3948486803113635041622535)
    ·
      refine ⟨5922730204670452562433803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948486803113635041622535 5922730204670452562433803)
      ·
        refine ⟨8884095307005678843650705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922730204670452562433803 8884095307005678843650705)
        ·
          refine ⟨6663071480254259132738029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8884095307005678843650705 6663071480254259132738029)
          ·
            refine ⟨2498651805095347174776761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6663071480254259132738029 2498651805095347174776761)
            ·
              refine ⟨1873988853821510381082571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498651805095347174776761 1873988853821510381082571)
              ·
                refine ⟨2810983280732265571623857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873988853821510381082571 2810983280732265571623857)
                ·
                  refine ⟨2108237460549199178717893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2810983280732265571623857 2108237460549199178717893)
                  ·
                    refine ⟨395294523852974846009605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108237460549199178717893 395294523852974846009605)
                    ·
                      rfl

theorem cell22_1154750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1154750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154750 prefixEnd_1154750 := by exact prefixLift 1154750
  have htrace : WordTrace (prefixWord ++ tailWord_1154750) baseStart_1154750 baseEnd_1154750 := by
    simpa [prefixWord, tailWord_1154750, baseEnd_1154750] using wordTrace_append hprefix tailTrace_1154750
  have hstable : (prefixWord ++ tailWord_1154750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154750).length < 2 ^ (prefixWord ++ tailWord_1154750).sum := by decide
  have hdescent : baseEnd_1154750 < baseStart_1154750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154872 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 4]
def baseStart_1154872 : Nat := 118140960795 + 1154872 * 2 ^ 59
def prefixEnd_1154872 : Nat := 4983230072969 + 3 ^ 40 * 1154872 * 2
def baseEnd_1154872 : Nat := 131778762315402398153077

theorem tailTrace_1154872 : CollatzResearch.WordTrace tailWord_1154872 prefixEnd_1154872 131778762315402398153077 := by
  unfold tailWord_1154872
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060821136051727639957435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28081094848068970186609913 21060821136051727639957435)
  ·
    refine ⟨31591231704077591459936153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21060821136051727639957435 31591231704077591459936153)
    ·
      refine ⟨23693423778058193594952115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31591231704077591459936153 23693423778058193594952115)
      ·
        refine ⟨35540135667087290392428173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23693423778058193594952115 35540135667087290392428173)
        ·
          refine ⟨13327550875157733897160565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35540135667087290392428173 13327550875157733897160565)
          ·
            refine ⟨1249457894546037552858803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13327550875157733897160565 1249457894546037552858803)
            ·
              refine ⟨1874186841819056329288205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249457894546037552858803 1874186841819056329288205)
              ·
                refine ⟨702820065682146123483077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874186841819056329288205 702820065682146123483077)
                ·
                  refine ⟨131778762315402398153077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 702820065682146123483077 131778762315402398153077)
                  ·
                    rfl

theorem cell22_1154872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_1154872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154872 prefixEnd_1154872 := by exact prefixLift 1154872
  have htrace : WordTrace (prefixWord ++ tailWord_1154872) baseStart_1154872 baseEnd_1154872 := by
    simpa [prefixWord, tailWord_1154872, baseEnd_1154872] using wordTrace_append hprefix tailTrace_1154872
  have hstable : (prefixWord ++ tailWord_1154872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154872).length < 2 ^ (prefixWord ++ tailWord_1154872).sum := by decide
  have hdescent : baseEnd_1154872 < baseStart_1154872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154883 : List Nat := [1, 1, 1, 3, 1, 7, 8]
def baseStart_1154883 : Nat := 118140960795 + 1154883 * 2 ^ 59
def prefixEnd_1154883 : Nat := 4983230072969 + 3 ^ 40 * 1154883 * 2
def baseEnd_1154883 : Nat := 14642224165592845645711

theorem tailTrace_1154883 : CollatzResearch.WordTrace tailWord_1154883 prefixEnd_1154883 14642224165592845645711 := by
  unfold tailWord_1154883
  simp only [CollatzResearch.WordTrace]
  refine ⟨42122043475063604158565303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28081362316709069439043535 42122043475063604158565303)
  ·
    refine ⟨63183065212595406237847955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42122043475063604158565303 63183065212595406237847955)
    ·
      refine ⟨94774597818893109356771933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63183065212595406237847955 94774597818893109356771933)
      ·
        refine ⟨35540474182084916008789475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94774597818893109356771933 35540474182084916008789475)
        ·
          refine ⟨53310711273127374013184213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35540474182084916008789475 53310711273127374013184213)
          ·
            refine ⟨1249469795463922828434005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53310711273127374013184213 1249469795463922828434005)
            ·
              refine ⟨14642224165592845645711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1249469795463922828434005 14642224165592845645711)
              ·
                rfl

theorem cell22_1154883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 8].length) (baseStart_1154883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154883 prefixEnd_1154883 := by exact prefixLift 1154883
  have htrace : WordTrace (prefixWord ++ tailWord_1154883) baseStart_1154883 baseEnd_1154883 := by
    simpa [prefixWord, tailWord_1154883, baseEnd_1154883] using wordTrace_append hprefix tailTrace_1154883
  have hstable : (prefixWord ++ tailWord_1154883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154883).length < 2 ^ (prefixWord ++ tailWord_1154883).sum := by decide
  have hdescent : baseEnd_1154883 < baseStart_1154883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154900 : List Nat := [2, 4, 1, 1, 3, 2, 2, 7]
def baseStart_1154900 : Nat := 118140960795 + 1154900 * 2 ^ 59
def prefixEnd_1154900 : Nat := 4983230072969 + 3 ^ 40 * 1154900 * 2
def baseEnd_1154900 : Nat := 43927319102047161639905

theorem tailTrace_1154900 : CollatzResearch.WordTrace tailWord_1154900 prefixEnd_1154900 43927319102047161639905 := by
  unfold tailWord_1154900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21061331758001008030967077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28081775677334677374622769 21061331758001008030967077)
  ·
    refine ⟨3948999704625189005806327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21061331758001008030967077 3948999704625189005806327)
    ·
      refine ⟨5923499556937783508709491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948999704625189005806327 5923499556937783508709491)
      ·
        refine ⟨8885249335406675263064237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5923499556937783508709491 8885249335406675263064237)
        ·
          refine ⟨3331968500777503223649089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8885249335406675263064237 3331968500777503223649089)
          ·
            refine ⟨2498976375583127417736817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3331968500777503223649089 2498976375583127417736817)
            ·
              refine ⟨1874232281687345563302613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498976375583127417736817 1874232281687345563302613)
              ·
                refine ⟨43927319102047161639905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1874232281687345563302613 43927319102047161639905)
                ·
                  rfl

theorem cell22_1154900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 7].length) (baseStart_1154900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154900 prefixEnd_1154900 := by exact prefixLift 1154900
  have htrace : WordTrace (prefixWord ++ tailWord_1154900) baseStart_1154900 baseEnd_1154900 := by
    simpa [prefixWord, tailWord_1154900, baseEnd_1154900] using wordTrace_append hprefix tailTrace_1154900
  have hstable : (prefixWord ++ tailWord_1154900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154900).length < 2 ^ (prefixWord ++ tailWord_1154900).sum := by decide
  have hdescent : baseEnd_1154900 < baseStart_1154900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154943 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_1154943 : Nat := 118140960795 + 1154943 * 2 ^ 59
def prefixEnd_1154943 : Nat := 4983230072969 + 3 ^ 40 * 1154943 * 2
def baseEnd_1154943 : Nat := 395360591697186675934013

theorem tailTrace_1154943 : CollatzResearch.WordTrace tailWord_1154943 prefixEnd_1154943 395360591697186675934013 := by
  unfold tailWord_1154943
  simp only [CollatzResearch.WordTrace]
  refine ⟨42124231854846234405749483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28082821236564156270499655 42124231854846234405749483)
  ·
    refine ⟨63186347782269351608624225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42124231854846234405749483 63186347782269351608624225)
    ·
      refine ⟨47389760836702013706468169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63186347782269351608624225 47389760836702013706468169)
      ·
        refine ⟨35542320627526510279851127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47389760836702013706468169 35542320627526510279851127)
        ·
          refine ⟨53313480941289765419776691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35542320627526510279851127 53313480941289765419776691)
          ·
            refine ⟨79970221411934648129665037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53313480941289765419776691 79970221411934648129665037)
            ·
              refine ⟨29988833029475493048624389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79970221411934648129665037 29988833029475493048624389)
              ·
                refine ⟨5622906193026654946617073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29988833029475493048624389 5622906193026654946617073)
                ·
                  refine ⟨4217179644769991209962805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5622906193026654946617073 4217179644769991209962805)
                  ·
                    refine ⟨395360591697186675934013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4217179644769991209962805 395360591697186675934013)
                    ·
                      rfl

theorem cell22_1154943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_1154943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154943 prefixEnd_1154943 := by exact prefixLift 1154943
  have htrace : WordTrace (prefixWord ++ tailWord_1154943) baseStart_1154943 baseEnd_1154943 := by
    simpa [prefixWord, tailWord_1154943, baseEnd_1154943] using wordTrace_append hprefix tailTrace_1154943
  have hstable : (prefixWord ++ tailWord_1154943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154943).length < 2 ^ (prefixWord ++ tailWord_1154943).sum := by decide
  have hdescent : baseEnd_1154943 < baseStart_1154943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154962 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1154962 : Nat := 118140960795 + 1154962 * 2 ^ 59
def prefixEnd_1154962 : Nat := 4983230072969 + 3 ^ 40 * 1154962 * 2
def baseEnd_1154962 : Nat := 131789031928492319902985

theorem tailTrace_1154962 : CollatzResearch.WordTrace tailWord_1154962 prefixEnd_1154962 131789031928492319902985 := by
  unfold tailWord_1154962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10531231210444350162672785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28083283227851600433794093 10531231210444350162672785)
  ·
    refine ⟨7898423407833262622004589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10531231210444350162672785 7898423407833262622004589)
    ·
      refine ⟨2961908777937473483251721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7898423407833262622004589 2961908777937473483251721)
      ·
        refine ⟨2221431583453105112438791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2961908777937473483251721 2221431583453105112438791)
        ·
          refine ⟨3332147375179657668658187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2221431583453105112438791 3332147375179657668658187)
          ·
            refine ⟨4998221062769486502987281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332147375179657668658187 4998221062769486502987281)
            ·
              refine ⟨3748665797077114877240461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998221062769486502987281 3748665797077114877240461)
              ·
                refine ⟨1405749673903918078965173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3748665797077114877240461 1405749673903918078965173)
                ·
                  refine ⟨131789031928492319902985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1405749673903918078965173 131789031928492319902985)
                  ·
                    rfl

theorem cell22_1154962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1154962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154962 prefixEnd_1154962 := by exact prefixLift 1154962
  have htrace : WordTrace (prefixWord ++ tailWord_1154962) baseStart_1154962 baseEnd_1154962 := by
    simpa [prefixWord, tailWord_1154962, baseEnd_1154962] using wordTrace_append hprefix tailTrace_1154962
  have hstable : (prefixWord ++ tailWord_1154962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154962).length < 2 ^ (prefixWord ++ tailWord_1154962).sum := by decide
  have hdescent : baseEnd_1154962 < baseStart_1154962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1154996 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1154996 : Nat := 118140960795 + 1154996 * 2 ^ 59
def prefixEnd_1154996 : Nat := 4983230072969 + 3 ^ 40 * 1154996 * 2
def baseEnd_1154996 : Nat := 131792911560104068119617

theorem tailTrace_1154996 : CollatzResearch.WordTrace tailWord_1154996 prefixEnd_1154996 131792911560104068119617 := by
  unfold tailWord_1154996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063082461827112228714421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28084109949102816304952561 21063082461827112228714421)
  ·
    refine ⟨1974663980796291771441977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21063082461827112228714421 1974663980796291771441977)
    ·
      refine ⟨1480997985597218828581483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1974663980796291771441977 1480997985597218828581483)
      ·
        refine ⟨2221496978395828242872225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480997985597218828581483 2221496978395828242872225)
        ·
          refine ⟨1666122733796871182154169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221496978395828242872225 1666122733796871182154169)
          ·
            refine ⟨1249592050347653386615627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666122733796871182154169 1249592050347653386615627)
            ·
              refine ⟨1874388075521480079923441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249592050347653386615627 1874388075521480079923441)
              ·
                refine ⟨1405791056641110059942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874388075521480079923441 1405791056641110059942581)
                ·
                  refine ⟨131792911560104068119617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1405791056641110059942581 131792911560104068119617)
                  ·
                    rfl

theorem cell22_1154996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1154996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1154996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1154996 prefixEnd_1154996 := by exact prefixLift 1154996
  have htrace : WordTrace (prefixWord ++ tailWord_1154996) baseStart_1154996 baseEnd_1154996 := by
    simpa [prefixWord, tailWord_1154996, baseEnd_1154996] using wordTrace_append hprefix tailTrace_1154996
  have hstable : (prefixWord ++ tailWord_1154996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1154996).length < 2 ^ (prefixWord ++ tailWord_1154996).sum := by decide
  have hdescent : baseEnd_1154996 < baseStart_1154996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1154996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_1155003 : Nat := 118140960795 + 1155003 * 2 ^ 59
def prefixEnd_1155003 : Nat := 4983230072969 + 3 ^ 40 * 1155003 * 2
def baseEnd_1155003 : Nat := 395381130923366519433829

theorem tailTrace_1155003 : CollatzResearch.WordTrace tailWord_1155003 prefixEnd_1155003 395381130923366519433829 := by
  unfold tailWord_1155003
  simp only [CollatzResearch.WordTrace]
  refine ⟨42126420234628864652933663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28084280156419243101955775 42126420234628864652933663)
  ·
    refine ⟨63189630351943296979400495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42126420234628864652933663 63189630351943296979400495)
    ·
      refine ⟨94784445527914945469100743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63189630351943296979400495 94784445527914945469100743)
      ·
        refine ⟨142176668291872418203651115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94784445527914945469100743 142176668291872418203651115)
        ·
          refine ⟨213265002437808627305476673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142176668291872418203651115 213265002437808627305476673)
          ·
            refine ⟨159948751828356470479107505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213265002437808627305476673 159948751828356470479107505)
            ·
              refine ⟨119961563871267352859330629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159948751828356470479107505 119961563871267352859330629)
              ·
                refine ⟨22492793225862628661124493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119961563871267352859330629 22492793225862628661124493)
                ·
                  refine ⟨8434797459698485747921685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22492793225862628661124493 8434797459698485747921685)
                  ·
                    refine ⟨395381130923366519433829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8434797459698485747921685 395381130923366519433829)
                    ·
                      rfl

theorem cell22_1155003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_1155003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155003 prefixEnd_1155003 := by exact prefixLift 1155003
  have htrace : WordTrace (prefixWord ++ tailWord_1155003) baseStart_1155003 baseEnd_1155003 := by
    simpa [prefixWord, tailWord_1155003, baseEnd_1155003] using wordTrace_append hprefix tailTrace_1155003
  have hstable : (prefixWord ++ tailWord_1155003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155003).length < 2 ^ (prefixWord ++ tailWord_1155003).sum := by decide
  have hdescent : baseEnd_1155003 < baseStart_1155003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155020 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1155020 : Nat := 118140960795 + 1155020 * 2 ^ 59
def prefixEnd_1155020 : Nat := 4983230072969 + 3 ^ 40 * 1155020 * 2
def baseEnd_1155020 : Nat := 395386950370784141758777

theorem tailTrace_1155020 : CollatzResearch.WordTrace tailWord_1155020 prefixEnd_1155020 395386950370784141758777 := by
  unfold tailWord_1155020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21063520137783638278151257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28084693517044851037535009 21063520137783638278151257)
  ·
    refine ⟨15797640103337728708613443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21063520137783638278151257 15797640103337728708613443)
    ·
      refine ⟨23696460155006593062920165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15797640103337728708613443 23696460155006593062920165)
      ·
        refine ⟨4443086279063736199297531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23696460155006593062920165 4443086279063736199297531)
        ·
          refine ⟨6664629418595604298946297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443086279063736199297531 6664629418595604298946297)
          ·
            refine ⟨4998472063946703224209723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6664629418595604298946297 4998472063946703224209723)
            ·
              refine ⟨7497708095920054836314585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4998472063946703224209723 7497708095920054836314585)
              ·
                refine ⟨5623281071940041127235939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7497708095920054836314585 5623281071940041127235939)
                ·
                  refine ⟨8434921607910061690853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5623281071940041127235939 8434921607910061690853909)
                  ·
                    refine ⟨395386950370784141758777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8434921607910061690853909 395386950370784141758777)
                    ·
                      rfl

theorem cell22_1155020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1155020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155020 prefixEnd_1155020 := by exact prefixLift 1155020
  have htrace : WordTrace (prefixWord ++ tailWord_1155020) baseStart_1155020 baseEnd_1155020 := by
    simpa [prefixWord, tailWord_1155020, baseEnd_1155020] using wordTrace_append hprefix tailTrace_1155020
  have hstable : (prefixWord ++ tailWord_1155020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155020).length < 2 ^ (prefixWord ++ tailWord_1155020).sum := by decide
  have hdescent : baseEnd_1155020 < baseStart_1155020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155067 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 3, 3]
def baseStart_1155067 : Nat := 118140960795 + 1155067 * 2 ^ 59
def prefixEnd_1155067 : Nat := 4983230072969 + 3 ^ 40 * 1155067 * 2
def baseEnd_1155067 : Nat := 395403039431291685833633

theorem tailTrace_1155067 : CollatzResearch.WordTrace tailWord_1155067 prefixEnd_1155067 395403039431291685833633 := by
  unfold tailWord_1155067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42128754506397003583263455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28085836337598002388842303 42128754506397003583263455)
  ·
    refine ⟨63193131759595505374895183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42128754506397003583263455 63193131759595505374895183)
    ·
      refine ⟨94789697639393258062342775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63193131759595505374895183 94789697639393258062342775)
      ·
        refine ⟨142184546459089887093514163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94789697639393258062342775 142184546459089887093514163)
        ·
          refine ⟨213276819688634830640271245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142184546459089887093514163 213276819688634830640271245)
          ·
            refine ⟨79978807383238061490101717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213276819688634830640271245 79978807383238061490101717)
            ·
              refine ⟨1874503298044642066174259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79978807383238061490101717 1874503298044642066174259)
              ·
                refine ⟨2811754947066963099261389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874503298044642066174259 2811754947066963099261389)
                ·
                  refine ⟨1054408105150111162223021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2811754947066963099261389 1054408105150111162223021)
                  ·
                    refine ⟨395403039431291685833633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054408105150111162223021 395403039431291685833633)
                    ·
                      rfl

theorem cell22_1155067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 3].length) (baseStart_1155067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155067 prefixEnd_1155067 := by exact prefixLift 1155067
  have htrace : WordTrace (prefixWord ++ tailWord_1155067) baseStart_1155067 baseEnd_1155067 := by
    simpa [prefixWord, tailWord_1155067, baseEnd_1155067] using wordTrace_append hprefix tailTrace_1155067
  have hstable : (prefixWord ++ tailWord_1155067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155067).length < 2 ^ (prefixWord ++ tailWord_1155067).sum := by decide
  have hdescent : baseEnd_1155067 < baseStart_1155067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155114 : List Nat := [3, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_1155114 : Nat := 118140960795 + 1155114 * 2 ^ 59
def prefixEnd_1155114 : Nat := 4983230072969 + 3 ^ 40 * 1155114 * 2
def baseEnd_1155114 : Nat := 131806376163933076636163

theorem tailTrace_1155114 : CollatzResearch.WordTrace tailWord_1155114 prefixEnd_1155114 131806376163933076636163 := by
  unfold tailWord_1155114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532617184306682652556099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28086979158151153740149597 10532617184306682652556099)
  ·
    refine ⟨15798925776460023978834149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10532617184306682652556099 15798925776460023978834149)
    ·
      refine ⟨2962298583086254496031403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15798925776460023978834149 2962298583086254496031403)
      ·
        refine ⟨4443447874629381744047105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962298583086254496031403 4443447874629381744047105)
        ·
          refine ⟨3332585905972036308035329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4443447874629381744047105 3332585905972036308035329)
          ·
            refine ⟨2499439429479027231026497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3332585905972036308035329 2499439429479027231026497)
            ·
              refine ⟨1874579572109270423269873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2499439429479027231026497 1874579572109270423269873)
              ·
                refine ⟨1405934679081952817452405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1874579572109270423269873 1405934679081952817452405)
                ·
                  refine ⟨131806376163933076636163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1405934679081952817452405 131806376163933076636163)
                  ·
                    rfl

theorem cell22_1155114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_1155114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155114 prefixEnd_1155114 := by exact prefixLift 1155114
  have htrace : WordTrace (prefixWord ++ tailWord_1155114) baseStart_1155114 baseEnd_1155114 := by
    simpa [prefixWord, tailWord_1155114, baseEnd_1155114] using wordTrace_append hprefix tailTrace_1155114
  have hstable : (prefixWord ++ tailWord_1155114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155114).length < 2 ^ (prefixWord ++ tailWord_1155114).sum := by decide
  have hdescent : baseEnd_1155114 < baseStart_1155114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155118 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1155118 : Nat := 118140960795 + 1155118 * 2 ^ 59
def prefixEnd_1155118 : Nat := 4983230072969 + 3 ^ 40 * 1155118 * 2
def baseEnd_1155118 : Nat := 395420497773544552808477

theorem tailTrace_1155118 : CollatzResearch.WordTrace tailWord_1155118 prefixEnd_1155118 395420497773544552808477 := by
  unfold tailWord_1155118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5266326828651529911671251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28087076419474826195580005 5266326828651529911671251)
  ·
    refine ⟨7899490242977294867506877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5266326828651529911671251 7899490242977294867506877)
    ·
      refine ⟨2962308841116485575315079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7899490242977294867506877 2962308841116485575315079)
      ·
        refine ⟨4443463261674728362972619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962308841116485575315079 4443463261674728362972619)
        ·
          refine ⟨6665194892512092544458929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443463261674728362972619 6665194892512092544458929)
          ·
            refine ⟨4998896169384069408344197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6665194892512092544458929 4998896169384069408344197)
            ·
              refine ⟨937293031759513014064537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4998896169384069408344197 937293031759513014064537)
              ·
                refine ⟨702969773819634760548403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937293031759513014064537 702969773819634760548403)
                ·
                  refine ⟨1054454660729452140822605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702969773819634760548403 1054454660729452140822605)
                  ·
                    refine ⟨395420497773544552808477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054454660729452140822605 395420497773544552808477)
                    ·
                      rfl

theorem cell22_1155118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1155118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155118 prefixEnd_1155118 := by exact prefixLift 1155118
  have htrace : WordTrace (prefixWord ++ tailWord_1155118) baseStart_1155118 baseEnd_1155118 := by
    simpa [prefixWord, tailWord_1155118, baseEnd_1155118] using wordTrace_append hprefix tailTrace_1155118
  have hstable : (prefixWord ++ tailWord_1155118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155118).length < 2 ^ (prefixWord ++ tailWord_1155118).sum := by decide
  have hdescent : baseEnd_1155118 < baseStart_1155118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155157 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1155157 : Nat := 118140960795 + 1155157 * 2 ^ 59
def prefixEnd_1155157 : Nat := 4983230072969 + 3 ^ 40 * 1155157 * 2
def baseEnd_1155157 : Nat := 395433848270561451083357

theorem tailTrace_1155157 : CollatzResearch.WordTrace tailWord_1155157 prefixEnd_1155157 395433848270561451083357 := by
  unfold tailWord_1155157
  simp only [CollatzResearch.WordTrace]
  refine ⟨42132037076070948954039725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28088024717380632636026483 42132037076070948954039725)
  ·
    refine ⟨15799513903526605857764897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42132037076070948954039725 15799513903526605857764897)
    ·
      refine ⟨11849635427644954393323673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15799513903526605857764897 11849635427644954393323673)
      ·
        refine ⟨8887226570733715794992755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11849635427644954393323673 8887226570733715794992755)
        ·
          refine ⟨13330839856100573692489133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8887226570733715794992755 13330839856100573692489133)
          ·
            refine ⟨4999064946037715134683425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13330839856100573692489133 4999064946037715134683425)
            ·
              refine ⟨3749298709528286351012569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4999064946037715134683425 3749298709528286351012569)
              ·
                refine ⟨2811974032146214763259427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3749298709528286351012569 2811974032146214763259427)
                ·
                  refine ⟨4217961048219322144889141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811974032146214763259427 4217961048219322144889141)
                  ·
                    refine ⟨395433848270561451083357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4217961048219322144889141 395433848270561451083357)
                    ·
                      rfl

theorem cell22_1155157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1155157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155157 prefixEnd_1155157 := by exact prefixLift 1155157
  have htrace : WordTrace (prefixWord ++ tailWord_1155157) baseStart_1155157 baseEnd_1155157 := by
    simpa [prefixWord, tailWord_1155157, baseEnd_1155157] using wordTrace_append hprefix tailTrace_1155157
  have hstable : (prefixWord ++ tailWord_1155157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155157).length < 2 ^ (prefixWord ++ tailWord_1155157).sum := by decide
  have hdescent : baseEnd_1155157 < baseStart_1155157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155172 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1155172 : Nat := 118140960795 + 1155172 * 2 ^ 59
def prefixEnd_1155172 : Nat := 4983230072969 + 3 ^ 40 * 1155172 * 2
def baseEnd_1155172 : Nat := 395438983077106411958311

theorem tailTrace_1155172 : CollatzResearch.WordTrace tailWord_1155172 prefixEnd_1155172 395438983077106411958311 := by
  unfold tailWord_1155172
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066292085508303257917885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28088389447344404343890513 21066292085508303257917885)
  ·
    refine ⟨7899859532065613721719207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21066292085508303257917885 7899859532065613721719207)
    ·
      refine ⟨11849789298098420582578811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7899859532065613721719207 11849789298098420582578811)
      ·
        refine ⟨17774683947147630873868217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11849789298098420582578811 17774683947147630873868217)
        ·
          refine ⟨13331012960360723155401163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17774683947147630873868217 13331012960360723155401163)
          ·
            refine ⟨19996519440541084733101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13331012960360723155401163 19996519440541084733101745)
            ·
              refine ⟨14997389580405813549826309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19996519440541084733101745 14997389580405813549826309)
              ·
                refine ⟨2812010546326090040592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14997389580405813549826309 2812010546326090040592433)
                ·
                  refine ⟨2109007909744567530444325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812010546326090040592433 2109007909744567530444325)
                  ·
                    refine ⟨395438983077106411958311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109007909744567530444325 395438983077106411958311)
                    ·
                      rfl

theorem cell22_1155172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1155172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155172 prefixEnd_1155172 := by exact prefixLift 1155172
  have htrace : WordTrace (prefixWord ++ tailWord_1155172) baseStart_1155172 baseEnd_1155172 := by
    simpa [prefixWord, tailWord_1155172, baseEnd_1155172] using wordTrace_append hprefix tailTrace_1155172
  have hstable : (prefixWord ++ tailWord_1155172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155172).length < 2 ^ (prefixWord ++ tailWord_1155172).sum := by decide
  have hdescent : baseEnd_1155172 < baseStart_1155172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155191 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 2, 3]
def baseStart_1155191 : Nat := 118140960795 + 1155191 * 2 ^ 59
def prefixEnd_1155191 : Nat := 4983230072969 + 3 ^ 40 * 1155191 * 2
def baseEnd_1155191 : Nat := 395445487165396695733253

theorem tailTrace_1155191 : CollatzResearch.WordTrace tailWord_1155191 prefixEnd_1155191 395445487165396695733253 := by
  unfold tailWord_1155191
  simp only [CollatzResearch.WordTrace]
  refine ⟨42133277157947772760777427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28088851438631848507184951 42133277157947772760777427)
  ·
    refine ⟨63199915736921659141166141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42133277157947772760777427 63199915736921659141166141)
    ·
      refine ⟨23699968401345622177937303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63199915736921659141166141 23699968401345622177937303)
      ·
        refine ⟨35549952602018433266905955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23699968401345622177937303 35549952602018433266905955)
        ·
          refine ⟨53324928903027649900358933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35549952602018433266905955 53324928903027649900358933)
          ·
            refine ⟨2499606042329421089079325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53324928903027649900358933 2499606042329421089079325)
            ·
              refine ⟨937352265873532908404747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2499606042329421089079325 937352265873532908404747)
              ·
                refine ⟨1406028398810299362607121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937352265873532908404747 1406028398810299362607121)
                ·
                  refine ⟨1054521299107724521955341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1406028398810299362607121 1054521299107724521955341)
                  ·
                    refine ⟨395445487165396695733253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054521299107724521955341 395445487165396695733253)
                    ·
                      rfl

theorem cell22_1155191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_1155191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155191 prefixEnd_1155191 := by exact prefixLift 1155191
  have htrace : WordTrace (prefixWord ++ tailWord_1155191) baseStart_1155191 baseEnd_1155191 := by
    simpa [prefixWord, tailWord_1155191, baseEnd_1155191] using wordTrace_append hprefix tailTrace_1155191
  have hstable : (prefixWord ++ tailWord_1155191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155191).length < 2 ^ (prefixWord ++ tailWord_1155191).sum := by decide
  have hdescent : baseEnd_1155191 < baseStart_1155191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155232 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_1155232 : Nat := 118140960795 + 1155232 * 2 ^ 59
def prefixEnd_1155232 : Nat := 4983230072969 + 3 ^ 40 * 1155232 * 2
def baseEnd_1155232 : Nat := 131819840767762085152709

theorem tailTrace_1155232 : CollatzResearch.WordTrace tailWord_1155232 prefixEnd_1155232 131819840767762085152709 := by
  unfold tailWord_1155232
  simp only [CollatzResearch.WordTrace]
  refine ⟨21067386275399618381509975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28089848367199491175346633 21067386275399618381509975)
  ·
    refine ⟨31601079413099427572264963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21067386275399618381509975 31601079413099427572264963)
    ·
      refine ⟨47401619119649141358397445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31601079413099427572264963 47401619119649141358397445)
      ·
        refine ⟨8887803584934214004699521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47401619119649141358397445 8887803584934214004699521)
        ·
          refine ⟨6665852688700660503524641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8887803584934214004699521 6665852688700660503524641)
          ·
            refine ⟨4999389516525495377643481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6665852688700660503524641 4999389516525495377643481)
            ·
              refine ⟨3749542137394121533232611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4999389516525495377643481 3749542137394121533232611)
              ·
                refine ⟨5624313206091182299848917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749542137394121533232611 5624313206091182299848917)
                ·
                  refine ⟨131819840767762085152709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5624313206091182299848917 131819840767762085152709)
                  ·
                    rfl

theorem cell22_1155232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_1155232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155232 prefixEnd_1155232 := by exact prefixLift 1155232
  have htrace : WordTrace (prefixWord ++ tailWord_1155232) baseStart_1155232 baseEnd_1155232 := by
    simpa [prefixWord, tailWord_1155232, baseEnd_1155232] using wordTrace_append hprefix tailTrace_1155232
  have hstable : (prefixWord ++ tailWord_1155232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155232).length < 2 ^ (prefixWord ++ tailWord_1155232).sum := by decide
  have hdescent : baseEnd_1155232 < baseStart_1155232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155242 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1155242 : Nat := 118140960795 + 1155242 * 2 ^ 59
def prefixEnd_1155242 : Nat := 4983230072969 + 3 ^ 40 * 1155242 * 2
def baseEnd_1155242 : Nat := 395462945507649562708097

theorem tailTrace_1155242 : CollatzResearch.WordTrace tailWord_1155242 prefixEnd_1155242 395462945507649562708097 := by
  unfold tailWord_1155242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533784320190752117720995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28090091520508672313922653 10533784320190752117720995)
  ·
    refine ⟨15800676480286128176581493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10533784320190752117720995 15800676480286128176581493)
    ·
      refine ⟨1481313420026824516554515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15800676480286128176581493 1481313420026824516554515)
      ·
        refine ⟨2221970130040236774831773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481313420026824516554515 2221970130040236774831773)
        ·
          refine ⟨833238798765088790561915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2221970130040236774831773 833238798765088790561915)
          ·
            refine ⟨1249858198147633185842873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833238798765088790561915 1249858198147633185842873)
            ·
              refine ⟨937393648610724889382155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249858198147633185842873 937393648610724889382155)
              ·
                refine ⟨1406090472916087334073233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937393648610724889382155 1406090472916087334073233)
                ·
                  refine ⟨1054567854687065500554925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1406090472916087334073233 1054567854687065500554925)
                  ·
                    refine ⟨395462945507649562708097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054567854687065500554925 395462945507649562708097)
                    ·
                      rfl

theorem cell22_1155242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1155242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155242 prefixEnd_1155242 := by exact prefixLift 1155242
  have htrace : WordTrace (prefixWord ++ tailWord_1155242) baseStart_1155242 baseEnd_1155242 := by
    simpa [prefixWord, tailWord_1155242, baseEnd_1155242] using wordTrace_append hprefix tailTrace_1155242
  have hstable : (prefixWord ++ tailWord_1155242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155242).length < 2 ^ (prefixWord ++ tailWord_1155242).sum := by decide
  have hdescent : baseEnd_1155242 < baseStart_1155242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155307 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_1155307 : Nat := 118140960795 + 1155307 * 2 ^ 59
def prefixEnd_1155307 : Nat := 4983230072969 + 3 ^ 40 * 1155307 * 2
def baseEnd_1155307 : Nat := 395485196336011059832897

theorem tailTrace_1155307 : CollatzResearch.WordTrace tailWord_1155307 prefixEnd_1155307 395485196336011059832897 := by
  unfold tailWord_1155307
  simp only [CollatzResearch.WordTrace]
  refine ⟨42137508025527524572000175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28091672017018349714666783 42137508025527524572000175)
  ·
    refine ⟨63206262038291286858000263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42137508025527524572000175 63206262038291286858000263)
    ·
      refine ⟨94809393057436930287000395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63206262038291286858000263 94809393057436930287000395)
      ·
        refine ⟨142214089586155395430500593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94809393057436930287000395 142214089586155395430500593)
        ·
          refine ⟨106660567189616546572875445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142214089586155395430500593 106660567189616546572875445)
          ·
            refine ⟨9999428174026551241207073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106660567189616546572875445 9999428174026551241207073)
            ·
              refine ⟨7499571130519913430905305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9999428174026551241207073 7499571130519913430905305)
              ·
                refine ⟨5624678347889935073178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499571130519913430905305 5624678347889935073178979)
                ·
                  refine ⟨8437017521834902609768469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624678347889935073178979 8437017521834902609768469)
                  ·
                    refine ⟨395485196336011059832897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8437017521834902609768469 395485196336011059832897)
                    ·
                      rfl

theorem cell22_1155307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_1155307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155307 prefixEnd_1155307 := by exact prefixLift 1155307
  have htrace : WordTrace (prefixWord ++ tailWord_1155307) baseStart_1155307 baseEnd_1155307 := by
    simpa [prefixWord, tailWord_1155307, baseEnd_1155307] using wordTrace_append hprefix tailTrace_1155307
  have hstable : (prefixWord ++ tailWord_1155307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155307).length < 2 ^ (prefixWord ++ tailWord_1155307).sum := by decide
  have hdescent : baseEnd_1155307 < baseStart_1155307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155324 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1155324 : Nat := 118140960795 + 1155324 * 2 ^ 59
def prefixEnd_1155324 : Nat := 4983230072969 + 3 ^ 40 * 1155324 * 2
def baseEnd_1155324 : Nat := 395491015783428682157845

theorem tailTrace_1155324 : CollatzResearch.WordTrace tailWord_1155324 prefixEnd_1155324 395491015783428682157845 := by
  unfold tailWord_1155324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21069064033232968237684513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28092085377643957650246017 21069064033232968237684513)
  ·
    refine ⟨15801798024924726178263385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21069064033232968237684513 15801798024924726178263385)
    ·
      refine ⟨11851348518693544633697539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15801798024924726178263385 11851348518693544633697539)
      ·
        refine ⟨17777022778040316950546309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11851348518693544633697539 17777022778040316950546309)
        ·
          refine ⟨3333191770882559428227433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17777022778040316950546309 3333191770882559428227433)
          ·
            refine ⟨2499893828161919571170575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333191770882559428227433 2499893828161919571170575)
            ·
              refine ⟨3749840742242879356755863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499893828161919571170575 3749840742242879356755863)
              ·
                refine ⟨5624761113364319035133795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3749840742242879356755863 5624761113364319035133795)
                ·
                  refine ⟨8437141670046478552700693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5624761113364319035133795 8437141670046478552700693)
                  ·
                    refine ⟨395491015783428682157845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8437141670046478552700693 395491015783428682157845)
                    ·
                      rfl

theorem cell22_1155324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1155324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155324 prefixEnd_1155324 := by exact prefixLift 1155324
  have htrace : WordTrace (prefixWord ++ tailWord_1155324) baseStart_1155324 baseEnd_1155324 := by
    simpa [prefixWord, tailWord_1155324, baseEnd_1155324] using wordTrace_append hprefix tailTrace_1155324
  have hstable : (prefixWord ++ tailWord_1155324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155324).length < 2 ^ (prefixWord ++ tailWord_1155324).sum := by decide
  have hdescent : baseEnd_1155324 < baseStart_1155324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155326 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1155326 : Nat := 118140960795 + 1155326 * 2 ^ 59
def prefixEnd_1155326 : Nat := 4983230072969 + 3 ^ 40 * 1155326 * 2
def baseEnd_1155326 : Nat := 395491700424301343607839

theorem tailTrace_1155326 : CollatzResearch.WordTrace tailWord_1155326 prefixEnd_1155326 395491700424301343607839 := by
  unfold tailWord_1155326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267275126557336352117729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28092134008305793877961221 5267275126557336352117729)
  ·
    refine ⟨3950456344918002264088297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5267275126557336352117729 3950456344918002264088297)
    ·
      refine ⟨2962842258688501698066223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3950456344918002264088297 2962842258688501698066223)
      ·
        refine ⟨4444263388032752547099335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962842258688501698066223 4444263388032752547099335)
        ·
          refine ⟨6666395082049128820649003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4444263388032752547099335 6666395082049128820649003)
          ·
            refine ⟨9999592623073693230973505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6666395082049128820649003 9999592623073693230973505)
            ·
              refine ⟨7499694467305269923230129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9999592623073693230973505 7499694467305269923230129)
              ·
                refine ⟨5624770850478952442422597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7499694467305269923230129 5624770850478952442422597)
                ·
                  refine ⟨1054644534464803582954237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5624770850478952442422597 1054644534464803582954237)
                  ·
                    refine ⟨395491700424301343607839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054644534464803582954237 395491700424301343607839)
                    ·
                      rfl

theorem cell22_1155326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1155326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155326 prefixEnd_1155326 := by exact prefixLift 1155326
  have htrace : WordTrace (prefixWord ++ tailWord_1155326) baseStart_1155326 baseEnd_1155326 := by
    simpa [prefixWord, tailWord_1155326, baseEnd_1155326] using wordTrace_append hprefix tailTrace_1155326
  have hstable : (prefixWord ++ tailWord_1155326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155326).length < 2 ^ (prefixWord ++ tailWord_1155326).sum := by decide
  have hdescent : baseEnd_1155326 < baseStart_1155326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155330 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1155330 : Nat := 118140960795 + 1155330 * 2 ^ 59
def prefixEnd_1155330 : Nat := 4983230072969 + 3 ^ 40 * 1155330 * 2
def baseEnd_1155330 : Nat := 395493069706046666507827

theorem tailTrace_1155330 : CollatzResearch.WordTrace tailWord_1155330 prefixEnd_1155330 395493069706046666507827 := by
  unfold tailWord_1155330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534586726111049875021861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28092231269629466333391629 10534586726111049875021861)
  ·
    refine ⟨1975235011145821851566599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10534586726111049875021861 1975235011145821851566599)
    ·
      refine ⟨2962852516718732777349899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975235011145821851566599 2962852516718732777349899)
      ·
        refine ⟨4444278775078099166024849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962852516718732777349899 4444278775078099166024849)
        ·
          refine ⟨3333209081308574374518637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4444278775078099166024849 3333209081308574374518637)
          ·
            refine ⟨1249953405490715390444489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3333209081308574374518637 1249953405490715390444489)
            ·
              refine ⟨937465054118036542833367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249953405490715390444489 937465054118036542833367)
              ·
                refine ⟨1406197581177054814250051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937465054118036542833367 1406197581177054814250051)
                ·
                  refine ⟨2109296371765582221375077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406197581177054814250051 2109296371765582221375077)
                  ·
                    refine ⟨395493069706046666507827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109296371765582221375077 395493069706046666507827)
                    ·
                      rfl

theorem cell22_1155330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1155330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155330 prefixEnd_1155330 := by exact prefixLift 1155330
  have htrace : WordTrace (prefixWord ++ tailWord_1155330) baseStart_1155330 baseEnd_1155330 := by
    simpa [prefixWord, tailWord_1155330, baseEnd_1155330] using wordTrace_append hprefix tailTrace_1155330
  have hstable : (prefixWord ++ tailWord_1155330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155330).length < 2 ^ (prefixWord ++ tailWord_1155330).sum := by decide
  have hdescent : baseEnd_1155330 < baseStart_1155330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155431 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1155431 : Nat := 118140960795 + 1155431 * 2 ^ 59
def prefixEnd_1155431 : Nat := 4983230072969 + 3 ^ 40 * 1155431 * 2
def baseEnd_1155431 : Nat := 395527644070116069732517

theorem tailTrace_1155431 : CollatzResearch.WordTrace tailWord_1155431 prefixEnd_1155431 395527644070116069732517 := by
  unfold tailWord_1155431
  simp only [CollatzResearch.WordTrace]
  refine ⟨42142030677078293749514147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28094687118052195833009431 42142030677078293749514147)
  ·
    refine ⟨63213046015617440624271221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42142030677078293749514147 63213046015617440624271221)
    ·
      refine ⟨5926223063964135058525427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63213046015617440624271221 5926223063964135058525427)
      ·
        refine ⟨8889334595946202587788141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5926223063964135058525427 8889334595946202587788141)
        ·
          refine ⟨3333500473479825970420553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8889334595946202587788141 3333500473479825970420553)
          ·
            refine ⟨2500125355109869477815415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333500473479825970420553 2500125355109869477815415)
            ·
              refine ⟨3750188032664804216723123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500125355109869477815415 3750188032664804216723123)
              ·
                refine ⟨5625282048997206325084685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750188032664804216723123 5625282048997206325084685)
                ·
                  refine ⟨2109480768373952371906757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5625282048997206325084685 2109480768373952371906757)
                  ·
                    refine ⟨395527644070116069732517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109480768373952371906757 395527644070116069732517)
                    ·
                      rfl

theorem cell22_1155431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1155431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155431 prefixEnd_1155431 := by exact prefixLift 1155431
  have htrace : WordTrace (prefixWord ++ tailWord_1155431) baseStart_1155431 baseEnd_1155431 := by
    simpa [prefixWord, tailWord_1155431, baseEnd_1155431] using wordTrace_append hprefix tailTrace_1155431
  have hstable : (prefixWord ++ tailWord_1155431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155431).length < 2 ^ (prefixWord ++ tailWord_1155431).sum := by decide
  have hdescent : baseEnd_1155431 < baseStart_1155431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155491 : List Nat := [1, 1, 1, 4, 1, 5, 3, 6]
def baseStart_1155491 : Nat := 118140960795 + 1155491 * 2 ^ 59
def prefixEnd_1155491 : Nat := 4983230072969 + 3 ^ 40 * 1155491 * 2
def baseEnd_1155491 : Nat := 43949798144032879248037

theorem tailTrace_1155491 : CollatzResearch.WordTrace tailWord_1155491 prefixEnd_1155491 43949798144032879248037 := by
  unfold tailWord_1155491
  simp only [CollatzResearch.WordTrace]
  refine ⟨42144219056860923996698327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28096146037907282664465551 42144219056860923996698327)
  ·
    refine ⟨63216328585291385995047491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42144219056860923996698327 63216328585291385995047491)
    ·
      refine ⟨94824492877937078992571237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63216328585291385995047491 94824492877937078992571237)
      ·
        refine ⟨17779592414613202311107107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94824492877937078992571237 17779592414613202311107107)
        ·
          refine ⟨26669388621919803466660661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17779592414613202311107107 26669388621919803466660661)
          ·
            refine ⟨2500255183304981574999437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26669388621919803466660661 2500255183304981574999437)
            ·
              refine ⟨937595693739368090624789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500255183304981574999437 937595693739368090624789)
              ·
                refine ⟨43949798144032879248037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 937595693739368090624789 43949798144032879248037)
                ·
                  rfl

theorem cell22_1155491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 6].length) (baseStart_1155491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155491 prefixEnd_1155491 := by exact prefixLift 1155491
  have htrace : WordTrace (prefixWord ++ tailWord_1155491) baseStart_1155491 baseEnd_1155491 := by
    simpa [prefixWord, tailWord_1155491, baseEnd_1155491] using wordTrace_append hprefix tailTrace_1155491
  have hstable : (prefixWord ++ tailWord_1155491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155491).length < 2 ^ (prefixWord ++ tailWord_1155491).sum := by decide
  have hdescent : baseEnd_1155491 < baseStart_1155491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155506 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1155506 : Nat := 118140960795 + 1155506 * 2 ^ 59
def prefixEnd_1155506 : Nat := 4983230072969 + 3 ^ 40 * 1155506 * 2
def baseEnd_1155506 : Nat := 395553318102840874107287

theorem tailTrace_1155506 : CollatzResearch.WordTrace tailWord_1155506 prefixEnd_1155506 395553318102840874107287 := by
  unfold tailWord_1155506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536191537951645389623593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28096510767871054372329581 10536191537951645389623593)
  ·
    refine ⟨7902143653463734042217695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10536191537951645389623593 7902143653463734042217695)
    ·
      refine ⟨11853215480195601063326543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7902143653463734042217695 11853215480195601063326543)
      ·
        refine ⟨17779823220293401594989815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853215480195601063326543 17779823220293401594989815)
        ·
          refine ⟨26669734830440102392484723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17779823220293401594989815 26669734830440102392484723)
          ·
            refine ⟨40004602245660153588727085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26669734830440102392484723 40004602245660153588727085)
            ·
              refine ⟨15001725842122557595772657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40004602245660153588727085 15001725842122557595772657)
              ·
                refine ⟨11251294381591918196829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15001725842122557595772657 11251294381591918196829493)
                ·
                  refine ⟨1054808848274242330952765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11251294381591918196829493 1054808848274242330952765)
                  ·
                    refine ⟨395553318102840874107287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054808848274242330952765 395553318102840874107287)
                    ·
                      rfl

theorem cell22_1155506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1155506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155506 prefixEnd_1155506 := by exact prefixLift 1155506
  have htrace : WordTrace (prefixWord ++ tailWord_1155506) baseStart_1155506 baseEnd_1155506 := by
    simpa [prefixWord, tailWord_1155506, baseEnd_1155506] using wordTrace_append hprefix tailTrace_1155506
  have hstable : (prefixWord ++ tailWord_1155506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155506).length < 2 ^ (prefixWord ++ tailWord_1155506).sum := by decide
  have hdescent : baseEnd_1155506 < baseStart_1155506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_1155579 : Nat := 118140960795 + 1155579 * 2 ^ 59
def prefixEnd_1155579 : Nat := 4983230072969 + 3 ^ 40 * 1155579 * 2
def baseEnd_1155579 : Nat := 395578307494693017032063

theorem tailTrace_1155579 : CollatzResearch.WordTrace tailWord_1155579 prefixEnd_1155579 395578307494693017032063 := by
  unfold tailWord_1155579
  simp only [CollatzResearch.WordTrace]
  refine ⟨42147428680542115025901791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28098285787028076683934527 42147428680542115025901791)
  ·
    refine ⟨63221143020813172538852687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42147428680542115025901791 63221143020813172538852687)
    ·
      refine ⟨94831714531219758808279031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63221143020813172538852687 94831714531219758808279031)
      ·
        refine ⟨142247571796829638212418547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94831714531219758808279031 142247571796829638212418547)
        ·
          refine ⟨213371357695244457318627821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142247571796829638212418547 213371357695244457318627821)
          ·
            refine ⟨80014259135716671494485433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213371357695244457318627821 80014259135716671494485433)
            ·
              refine ⟨60010694351787503620864075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80014259135716671494485433 60010694351787503620864075)
              ·
                refine ⟨90016041527681255431296113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60010694351787503620864075 90016041527681255431296113)
                ·
                  refine ⟨67512031145760941573472085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90016041527681255431296113 67512031145760941573472085)
                  ·
                    refine ⟨395578307494693017032063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 67512031145760941573472085 395578307494693017032063)
                    ·
                      rfl

theorem cell22_1155579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_1155579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155579 prefixEnd_1155579 := by exact prefixLift 1155579
  have htrace : WordTrace (prefixWord ++ tailWord_1155579) baseStart_1155579 baseEnd_1155579 := by
    simpa [prefixWord, tailWord_1155579, baseEnd_1155579] using wordTrace_append hprefix tailTrace_1155579
  have hstable : (prefixWord ++ tailWord_1155579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155579).length < 2 ^ (prefixWord ++ tailWord_1155579).sum := by decide
  have hdescent : baseEnd_1155579 < baseStart_1155579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155613 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1155613 : Nat := 118140960795 + 1155613 * 2 ^ 59
def prefixEnd_1155613 : Nat := 4983230072969 + 3 ^ 40 * 1155613 * 2
def baseEnd_1155613 : Nat := 395589946389528261681959

theorem tailTrace_1155613 : CollatzResearch.WordTrace tailWord_1155613 prefixEnd_1155613 395589946389528261681959 := by
  unfold tailWord_1155613
  simp only [CollatzResearch.WordTrace]
  refine ⟨42148668762418938832639493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28099112508279292555092995 42148668762418938832639493)
  ·
    refine ⟨7902875392953551031119905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42148668762418938832639493 7902875392953551031119905)
    ·
      refine ⟨5927156544715163273339929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7902875392953551031119905 5927156544715163273339929)
      ·
        refine ⟨4445367408536372455004947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5927156544715163273339929 4445367408536372455004947)
        ·
          refine ⟨6668051112804558682507421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445367408536372455004947 6668051112804558682507421)
          ·
            refine ⟨2500519167301709505940283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668051112804558682507421 2500519167301709505940283)
            ·
              refine ⟨3750778750952564258910425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500519167301709505940283 3750778750952564258910425)
              ·
                refine ⟨2813084063214423194182819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3750778750952564258910425 2813084063214423194182819)
                ·
                  refine ⟨4219626094821634791274229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2813084063214423194182819 4219626094821634791274229)
                  ·
                    refine ⟨395589946389528261681959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4219626094821634791274229 395589946389528261681959)
                    ·
                      rfl

theorem cell22_1155613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1155613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155613 prefixEnd_1155613 := by exact prefixLift 1155613
  have htrace : WordTrace (prefixWord ++ tailWord_1155613) baseStart_1155613 baseEnd_1155613 := by
    simpa [prefixWord, tailWord_1155613, baseEnd_1155613] using wordTrace_append hprefix tailTrace_1155613
  have hstable : (prefixWord ++ tailWord_1155613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155613).length < 2 ^ (prefixWord ++ tailWord_1155613).sum := by decide
  have hdescent : baseEnd_1155613 < baseStart_1155613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155626 : List Nat := [3, 1, 4, 1, 1, 12]
def baseStart_1155626 : Nat := 118140960795 + 1155626 * 2 ^ 59
def prefixEnd_1155626 : Nat := 4983230072969 + 3 ^ 40 * 1155626 * 2
def baseEnd_1155626 : Nat := 4883881438953093346999

theorem tailTrace_1155626 : CollatzResearch.WordTrace tailWord_1155626 prefixEnd_1155626 4883881438953093346999 := by
  unfold tailWord_1155626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537285727842960513215683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28099428607581228035241821 10537285727842960513215683)
  ·
    refine ⟨15805928591764440769823525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537285727842960513215683 15805928591764440769823525)
    ·
      refine ⟨2963611610955832644341911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15805928591764440769823525 2963611610955832644341911)
      ·
        refine ⟨4445417416433748966512867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963611610955832644341911 4445417416433748966512867)
        ·
          refine ⟨6668126124650623449769301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4445417416433748966512867 6668126124650623449769301)
          ·
            refine ⟨4883881438953093346999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6668126124650623449769301 4883881438953093346999)
            ·
              rfl

theorem cell22_1155626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 12].length) (baseStart_1155626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155626 prefixEnd_1155626 := by exact prefixLift 1155626
  have htrace : WordTrace (prefixWord ++ tailWord_1155626) baseStart_1155626 baseEnd_1155626 := by
    simpa [prefixWord, tailWord_1155626, baseEnd_1155626] using wordTrace_append hprefix tailTrace_1155626
  have hstable : (prefixWord ++ tailWord_1155626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155626).length < 2 ^ (prefixWord ++ tailWord_1155626).sum := by decide
  have hdescent : baseEnd_1155626 < baseStart_1155626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155658 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1155658 : Nat := 118140960795 + 1155658 * 2 ^ 59
def prefixEnd_1155658 : Nat := 4983230072969 + 3 ^ 40 * 1155658 * 2
def baseEnd_1155658 : Nat := 395605350809163144306821

theorem tailTrace_1155658 : CollatzResearch.WordTrace tailWord_1155658 prefixEnd_1155658 395605350809163144306821 := by
  unfold tailWord_1155658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10537577511813977879506907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28100206698170607678685085 10537577511813977879506907)
  ·
    refine ⟨15806366267720966819260361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10537577511813977879506907 15806366267720966819260361)
    ·
      refine ⟨11854774700790725114445271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15806366267720966819260361 11854774700790725114445271)
      ·
        refine ⟨17782162051186087671667907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11854774700790725114445271 17782162051186087671667907)
        ·
          refine ⟨26673243076779131507501861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17782162051186087671667907 26673243076779131507501861)
          ·
            refine ⟨5001233076896087157656599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26673243076779131507501861 5001233076896087157656599)
            ·
              refine ⟨7501849615344130736484899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001233076896087157656599 7501849615344130736484899)
              ·
                refine ⟨11252774423016196104727349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7501849615344130736484899 11252774423016196104727349)
                ·
                  refine ⟨1054947602157768384818189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11252774423016196104727349 1054947602157768384818189)
                  ·
                    refine ⟨395605350809163144306821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054947602157768384818189 395605350809163144306821)
                    ·
                      rfl

theorem cell22_1155658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1155658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155658 prefixEnd_1155658 := by exact prefixLift 1155658
  have htrace : WordTrace (prefixWord ++ tailWord_1155658) baseStart_1155658 baseEnd_1155658 := by
    simpa [prefixWord, tailWord_1155658, baseEnd_1155658] using wordTrace_append hprefix tailTrace_1155658
  have hstable : (prefixWord ++ tailWord_1155658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155658).length < 2 ^ (prefixWord ++ tailWord_1155658).sum := by decide
  have hdescent : baseEnd_1155658 < baseStart_1155658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155671 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 7]
def baseStart_1155671 : Nat := 118140960795 + 1155671 * 2 ^ 59
def prefixEnd_1155671 : Nat := 4983230072969 + 3 ^ 40 * 1155671 * 2
def baseEnd_1155671 : Nat := 131869933658278481243927

theorem tailTrace_1155671 : CollatzResearch.WordTrace tailWord_1155671 prefixEnd_1155671 131869933658278481243927 := by
  unfold tailWord_1155671
  simp only [CollatzResearch.WordTrace]
  refine ⟨42150784196208814738250867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28100522797472543158833911 42150784196208814738250867)
  ·
    refine ⟨63226176294313222107376301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42150784196208814738250867 63226176294313222107376301)
    ·
      refine ⟨23709816110367458290266113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63226176294313222107376301 23709816110367458290266113)
      ·
        refine ⟨17782362082775593717699585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23709816110367458290266113 17782362082775593717699585)
        ·
          refine ⟨13336771562081695288274689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17782362082775593717699585 13336771562081695288274689)
          ·
            refine ⟨10002578671561271466206017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13336771562081695288274689 10002578671561271466206017)
            ·
              refine ⟨7501934003670953599654513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10002578671561271466206017 7501934003670953599654513)
              ·
                refine ⟨5626450502753215199740885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7501934003670953599654513 5626450502753215199740885)
                ·
                  refine ⟨131869933658278481243927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5626450502753215199740885 131869933658278481243927)
                  ·
                    rfl

theorem cell22_1155671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_1155671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155671 prefixEnd_1155671 := by exact prefixLift 1155671
  have htrace : WordTrace (prefixWord ++ tailWord_1155671) baseStart_1155671 baseEnd_1155671 := by
    simpa [prefixWord, tailWord_1155671, baseEnd_1155671] using wordTrace_append hprefix tailTrace_1155671
  have hstable : (prefixWord ++ tailWord_1155671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155671).length < 2 ^ (prefixWord ++ tailWord_1155671).sum := by decide
  have hdescent : baseEnd_1155671 < baseStart_1155671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155705 : List Nat := [1, 2, 1, 3, 3, 3, 3, 1, 5]
def baseStart_1155705 : Nat := 118140960795 + 1155705 * 2 ^ 59
def prefixEnd_1155705 : Nat := 4983230072969 + 3 ^ 40 * 1155705 * 2
def baseEnd_1155705 : Nat := 131873813289890229460559

theorem tailTrace_1155705 : CollatzResearch.WordTrace tailWord_1155705 prefixEnd_1155705 131873813289890229460559 := by
  unfold tailWord_1155705
  simp only [CollatzResearch.WordTrace]
  refine ⟨42152024278085638544988569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28101349518723759029992379 42152024278085638544988569)
  ·
    refine ⟨31614018208564228908741427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42152024278085638544988569 31614018208564228908741427)
    ·
      refine ⟨47421027312846343363112141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31614018208564228908741427 47421027312846343363112141)
      ·
        refine ⟨17782885242317378761167053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47421027312846343363112141 17782885242317378761167053)
        ·
          refine ⟨6668581965869017035437645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17782885242317378761167053 6668581965869017035437645)
          ·
            refine ⟨2500718237200881388289117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6668581965869017035437645 2500718237200881388289117)
            ·
              refine ⟨937769338950330520608419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2500718237200881388289117 937769338950330520608419)
              ·
                refine ⟨1406654008425495780912629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937769338950330520608419 1406654008425495780912629)
                ·
                  refine ⟨131873813289890229460559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1406654008425495780912629 131873813289890229460559)
                  ·
                    rfl

theorem cell22_1155705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_1155705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155705 prefixEnd_1155705 := by exact prefixLift 1155705
  have htrace : WordTrace (prefixWord ++ tailWord_1155705) baseStart_1155705 baseEnd_1155705 := by
    simpa [prefixWord, tailWord_1155705, baseEnd_1155705] using wordTrace_append hprefix tailTrace_1155705
  have hstable : (prefixWord ++ tailWord_1155705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155705).length < 2 ^ (prefixWord ++ tailWord_1155705).sum := by decide
  have hdescent : baseEnd_1155705 < baseStart_1155705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155780 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1155780 : Nat := 118140960795 + 1155780 * 2 ^ 59
def prefixEnd_1155780 : Nat := 4983230072969 + 3 ^ 40 * 1155780 * 2
def baseEnd_1155780 : Nat := 395647113902395492756447

theorem tailTrace_1155780 : CollatzResearch.WordTrace tailWord_1155780 prefixEnd_1155780 395647113902395492756447 := by
  unfold tailWord_1155780
  simp only [CollatzResearch.WordTrace]
  refine ⟨21077379876406963176984397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28103173168542617569312529 21077379876406963176984397)
  ·
    refine ⟨7904017453652611191369149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21077379876406963176984397 7904017453652611191369149)
    ·
      refine ⟨2964006545119729196763431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7904017453652611191369149 2964006545119729196763431)
      ·
        refine ⟨4446009817679593795145147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964006545119729196763431 4446009817679593795145147)
        ·
          refine ⟨6669014726519390692717721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446009817679593795145147 6669014726519390692717721)
          ·
            refine ⟨5001761044889543019538291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6669014726519390692717721 5001761044889543019538291)
            ·
              refine ⟨7502641567334314529307437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001761044889543019538291 7502641567334314529307437)
              ·
                refine ⟨2813490587750367948490289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7502641567334314529307437 2813490587750367948490289)
                ·
                  refine ⟨2110117940812775961367717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2813490587750367948490289 2110117940812775961367717)
                  ·
                    refine ⟨395647113902395492756447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110117940812775961367717 395647113902395492756447)
                    ·
                      rfl

theorem cell22_1155780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1155780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155780 prefixEnd_1155780 := by exact prefixLift 1155780
  have htrace : WordTrace (prefixWord ++ tailWord_1155780) baseStart_1155780 baseEnd_1155780 := by
    simpa [prefixWord, tailWord_1155780, baseEnd_1155780] using wordTrace_append hprefix tailTrace_1155780
  have hstable : (prefixWord ++ tailWord_1155780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155780).length < 2 ^ (prefixWord ++ tailWord_1155780).sum := by decide
  have hdescent : baseEnd_1155780 < baseStart_1155780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155844 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_1155844 : Nat := 118140960795 + 1155844 * 2 ^ 59
def prefixEnd_1155844 : Nat := 4983230072969 + 3 ^ 40 * 1155844 * 2
def baseEnd_1155844 : Nat := 395669022410320659156251

theorem tailTrace_1155844 : CollatzResearch.WordTrace tailWord_1155844 prefixEnd_1155844 395669022410320659156251 := by
  unfold tailWord_1155844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21078547012291032642149293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28104729349721376856199057 21078547012291032642149293)
  ·
    refine ⟨7904455129609137240805985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21078547012291032642149293 7904455129609137240805985)
    ·
      refine ⟨5928341347206852930604489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7904455129609137240805985 5928341347206852930604489)
      ·
        refine ⟨4446256010405139697953367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5928341347206852930604489 4446256010405139697953367)
        ·
          refine ⟨6669384015607709546930051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446256010405139697953367 6669384015607709546930051)
          ·
            refine ⟨10004076023411564320395077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6669384015607709546930051 10004076023411564320395077)
            ·
              refine ⟨1875764254389668310074077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10004076023411564320395077 1875764254389668310074077)
              ·
                refine ⟨703411595396125616277779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1875764254389668310074077 703411595396125616277779)
                ·
                  refine ⟨1055117393094188424416669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703411595396125616277779 1055117393094188424416669)
                  ·
                    refine ⟨395669022410320659156251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055117393094188424416669 395669022410320659156251)
                    ·
                      rfl

theorem cell22_1155844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_1155844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155844 prefixEnd_1155844 := by exact prefixLift 1155844
  have htrace : WordTrace (prefixWord ++ tailWord_1155844) baseStart_1155844 baseEnd_1155844 := by
    simpa [prefixWord, tailWord_1155844, baseEnd_1155844] using wordTrace_append hprefix tailTrace_1155844
  have hstable : (prefixWord ++ tailWord_1155844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155844).length < 2 ^ (prefixWord ++ tailWord_1155844).sum := by decide
  have hdescent : baseEnd_1155844 < baseStart_1155844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155913 : List Nat := [1, 2, 1, 1, 2, 5, 10]
def baseStart_1155913 : Nat := 118140960795 + 1155913 * 2 ^ 59
def prefixEnd_1155913 : Nat := 4983230072969 + 3 ^ 40 * 1155913 * 2
def baseEnd_1155913 : Nat := 14655283056312128858557

theorem tailTrace_1155913 : CollatzResearch.WordTrace tailWord_1155913 prefixEnd_1155913 14655283056312128858557 := by
  unfold tailWord_1155913
  simp only [CollatzResearch.WordTrace]
  refine ⟨42159610661332090068560393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28106407107554726712373595 42159610661332090068560393)
  ·
    refine ⟨31619707995999067551420295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42159610661332090068560393 31619707995999067551420295)
    ·
      refine ⟨47429561993998601327130443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31619707995999067551420295 47429561993998601327130443)
      ·
        refine ⟨71144342990997901990695665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47429561993998601327130443 71144342990997901990695665)
        ·
          refine ⟨53358257243248426493021749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71144342990997901990695665 53358257243248426493021749)
          ·
            refine ⟨5002336616554539983720789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53358257243248426493021749 5002336616554539983720789)
            ·
              refine ⟨14655283056312128858557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5002336616554539983720789 14655283056312128858557)
              ·
                rfl

theorem cell22_1155913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 10].length) (baseStart_1155913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155913 prefixEnd_1155913 := by exact prefixLift 1155913
  have htrace : WordTrace (prefixWord ++ tailWord_1155913) baseStart_1155913 baseEnd_1155913 := by
    simpa [prefixWord, tailWord_1155913, baseEnd_1155913] using wordTrace_append hprefix tailTrace_1155913
  have hstable : (prefixWord ++ tailWord_1155913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155913).length < 2 ^ (prefixWord ++ tailWord_1155913).sum := by decide
  have hdescent : baseEnd_1155913 < baseStart_1155913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155930 : List Nat := [3, 1, 1, 2, 1, 5, 2, 7]
def baseStart_1155930 : Nat := 118140960795 + 1155930 * 2 ^ 59
def prefixEnd_1155930 : Nat := 4983230072969 + 3 ^ 40 * 1155930 * 2
def baseEnd_1155930 : Nat := 43966495774205011278443

theorem tailTrace_1155930 : CollatzResearch.WordTrace tailWord_1155930 prefixEnd_1155930 43966495774205011278443 := by
  unfold tailWord_1155930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540057675567625492982311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28106820468180334647952829 10540057675567625492982311)
  ·
    refine ⟨15810086513351438239473467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10540057675567625492982311 15810086513351438239473467)
    ·
      refine ⟨23715129770027157359210201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15810086513351438239473467 23715129770027157359210201)
      ·
        refine ⟨17786347327520368019407651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23715129770027157359210201 17786347327520368019407651)
        ·
          refine ⟨26679520991280552029111477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17786347327520368019407651 26679520991280552029111477)
          ·
            refine ⟨2501205092932551752729201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26679520991280552029111477 2501205092932551752729201)
            ·
              refine ⟨1875903819699413814546901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501205092932551752729201 1875903819699413814546901)
              ·
                refine ⟨43966495774205011278443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1875903819699413814546901 43966495774205011278443)
                ·
                  rfl

theorem cell22_1155930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_1155930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155930 prefixEnd_1155930 := by exact prefixLift 1155930
  have htrace : WordTrace (prefixWord ++ tailWord_1155930) baseStart_1155930 baseEnd_1155930 := by
    simpa [prefixWord, tailWord_1155930, baseEnd_1155930] using wordTrace_append hprefix tailTrace_1155930
  have hstable : (prefixWord ++ tailWord_1155930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155930).length < 2 ^ (prefixWord ++ tailWord_1155930).sum := by decide
  have hdescent : baseEnd_1155930 < baseStart_1155930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1155970 : List Nat := [3, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1155970 : Nat := 118140960795 + 1155970 * 2 ^ 59
def prefixEnd_1155970 : Nat := 4983230072969 + 3 ^ 40 * 1155970 * 2
def baseEnd_1155970 : Nat := 131904051595099443501955

theorem tailTrace_1155970 : CollatzResearch.WordTrace tailWord_1155970 prefixEnd_1155970 131904051595099443501955 := by
  unfold tailWord_1155970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10540422405531397200846341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28107793081417059202256909 10540422405531397200846341)
  ·
    refine ⟨1976329201037136975158689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10540422405531397200846341 1976329201037136975158689)
    ·
      refine ⟨1482246900777852731369017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1976329201037136975158689 1482246900777852731369017)
      ·
        refine ⟨1111685175583389548526763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1482246900777852731369017 1111685175583389548526763)
        ·
          refine ⟨1667527763375084322790145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111685175583389548526763 1667527763375084322790145)
          ·
            refine ⟨1250645822531313242092609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667527763375084322790145 1250645822531313242092609)
            ·
              refine ⟨937984366898484931569457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250645822531313242092609 937984366898484931569457)
              ·
                refine ⟨703488275173863698677093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937984366898484931569457 703488275173863698677093)
                ·
                  refine ⟨131904051595099443501955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703488275173863698677093 131904051595099443501955)
                  ·
                    rfl

theorem cell22_1155970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1155970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1155970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1155970 prefixEnd_1155970 := by exact prefixLift 1155970
  have htrace : WordTrace (prefixWord ++ tailWord_1155970) baseStart_1155970 baseEnd_1155970 := by
    simpa [prefixWord, tailWord_1155970, baseEnd_1155970] using wordTrace_append hprefix tailTrace_1155970
  have hstable : (prefixWord ++ tailWord_1155970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1155970).length < 2 ^ (prefixWord ++ tailWord_1155970).sum := by decide
  have hdescent : baseEnd_1155970 < baseStart_1155970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1155970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156054 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1156054 : Nat := 118140960795 + 1156054 * 2 ^ 59
def prefixEnd_1156054 : Nat := 4983230072969 + 3 ^ 40 * 1156054 * 2
def baseEnd_1156054 : Nat := 131913636567316703801869

theorem tailTrace_1156054 : CollatzResearch.WordTrace tailWord_1156054 prefixEnd_1156054 131913636567316703801869 := by
  unfold tailWord_1156054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635297084613829446840201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28109835569214180766295477 2635297084613829446840201)
  ·
    refine ⟨1976472813460372085130151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635297084613829446840201 1976472813460372085130151)
    ·
      refine ⟨2964709220190558127695227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976472813460372085130151 2964709220190558127695227)
      ·
        refine ⟨4447063830285837191542841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964709220190558127695227 4447063830285837191542841)
        ·
          refine ⟨3335297872714377893657131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447063830285837191542841 3335297872714377893657131)
          ·
            refine ⟨5002946809071566840485697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335297872714377893657131 5002946809071566840485697)
            ·
              refine ⟨3752210106803675130364273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002946809071566840485697 3752210106803675130364273)
              ·
                refine ⟨2814157580102756347773205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3752210106803675130364273 2814157580102756347773205)
                ·
                  refine ⟨131913636567316703801869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2814157580102756347773205 131913636567316703801869)
                  ·
                    rfl

theorem cell22_1156054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1156054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156054 prefixEnd_1156054 := by exact prefixLift 1156054
  have htrace : WordTrace (prefixWord ++ tailWord_1156054) baseStart_1156054 baseEnd_1156054 := by
    simpa [prefixWord, tailWord_1156054, baseEnd_1156054] using wordTrace_append hprefix tailTrace_1156054
  have hstable : (prefixWord ++ tailWord_1156054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156054).length < 2 ^ (prefixWord ++ tailWord_1156054).sum := by decide
  have hdescent : baseEnd_1156054 < baseStart_1156054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156067 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_1156067 : Nat := 118140960795 + 1156067 * 2 ^ 59
def prefixEnd_1156067 : Nat := 4983230072969 + 3 ^ 40 * 1156067 * 2
def baseEnd_1156067 : Nat := 395745359867622410830567

theorem tailTrace_1156067 : CollatzResearch.WordTrace tailWord_1156067 prefixEnd_1156067 395745359867622410830567 := by
  unfold tailWord_1156067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42165227502774174369666455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28110151668516116246444303 42165227502774174369666455)
  ·
    refine ⟨63247841254161261554499683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42165227502774174369666455 63247841254161261554499683)
    ·
      refine ⟨94871761881241892331749525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63247841254161261554499683 94871761881241892331749525)
      ·
        refine ⟨4447113838183213703050759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94871761881241892331749525 4447113838183213703050759)
        ·
          refine ⟨6670670757274820554576139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447113838183213703050759 6670670757274820554576139)
          ·
            refine ⟨10006006135912230831864209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6670670757274820554576139 10006006135912230831864209)
            ·
              refine ⟨7504504601934173123898157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10006006135912230831864209 7504504601934173123898157)
              ·
                refine ⟨2814189225725314921461809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7504504601934173123898157 2814189225725314921461809)
                ·
                  refine ⟨2110641919293986191096357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2814189225725314921461809 2110641919293986191096357)
                  ·
                    refine ⟨395745359867622410830567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110641919293986191096357 395745359867622410830567)
                    ·
                      rfl

theorem cell22_1156067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_1156067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156067 prefixEnd_1156067 := by exact prefixLift 1156067
  have htrace : WordTrace (prefixWord ++ tailWord_1156067) baseStart_1156067 baseEnd_1156067 := by
    simpa [prefixWord, tailWord_1156067, baseEnd_1156067] using wordTrace_append hprefix tailTrace_1156067
  have hstable : (prefixWord ++ tailWord_1156067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156067).length < 2 ^ (prefixWord ++ tailWord_1156067).sum := by decide
  have hdescent : baseEnd_1156067 < baseStart_1156067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156071 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 4]
def baseStart_1156071 : Nat := 118140960795 + 1156071 * 2 ^ 59
def prefixEnd_1156071 : Nat := 4983230072969 + 3 ^ 40 * 1156071 * 2
def baseEnd_1156071 : Nat := 131915576383122577910185

theorem tailTrace_1156071 : CollatzResearch.WordTrace tailWord_1156071 prefixEnd_1156071 131915576383122577910185 := by
  unfold tailWord_1156071
  simp only [CollatzResearch.WordTrace]
  refine ⟨42165373394759683052812067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28110248929839788701874711 42165373394759683052812067)
  ·
    refine ⟨63248060092139524579218101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42165373394759683052812067 63248060092139524579218101)
    ·
      refine ⟨5929505633638080429301697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63248060092139524579218101 5929505633638080429301697)
      ·
        refine ⟨4447129225228560321976273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5929505633638080429301697 4447129225228560321976273)
        ·
          refine ⟨3335346918921420241482205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4447129225228560321976273 3335346918921420241482205)
          ·
            refine ⟨1250755094595532590555827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3335346918921420241482205 1250755094595532590555827)
            ·
              refine ⟨1876132641893298885833741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250755094595532590555827 1876132641893298885833741)
              ·
                refine ⟨703549740709987082187653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1876132641893298885833741 703549740709987082187653)
                ·
                  refine ⟨131915576383122577910185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703549740709987082187653 131915576383122577910185)
                  ·
                    rfl

theorem cell22_1156071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 4].length) (baseStart_1156071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156071 prefixEnd_1156071 := by exact prefixLift 1156071
  have htrace : WordTrace (prefixWord ++ tailWord_1156071) baseStart_1156071 baseEnd_1156071 := by
    simpa [prefixWord, tailWord_1156071, baseEnd_1156071] using wordTrace_append hprefix tailTrace_1156071
  have hstable : (prefixWord ++ tailWord_1156071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156071).length < 2 ^ (prefixWord ++ tailWord_1156071).sum := by decide
  have hdescent : baseEnd_1156071 < baseStart_1156071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156174 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1156174 : Nat := 118140960795 + 1156174 * 2 ^ 59
def prefixEnd_1156174 : Nat := 4983230072969 + 3 ^ 40 * 1156174 * 2
def baseEnd_1156174 : Nat := 395781988154309798405239

theorem tailTrace_1156174 : CollatzResearch.WordTrace tailWord_1156174 prefixEnd_1156174 395781988154309798405239 := by
  unfold tailWord_1156174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271141264173316455476447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28112753408924354429207717 5271141264173316455476447)
  ·
    refine ⟨7906711896259974683214671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5271141264173316455476447 7906711896259974683214671)
    ·
      refine ⟨11860067844389962024822007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906711896259974683214671 11860067844389962024822007)
      ·
        refine ⟨17790101766584943037233011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860067844389962024822007 17790101766584943037233011)
        ·
          refine ⟨26685152649877414555849517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17790101766584943037233011 26685152649877414555849517)
          ·
            refine ⟨10006932243704030458443569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26685152649877414555849517 10006932243704030458443569)
            ·
              refine ⟨7505199182778022843832677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10006932243704030458443569 7505199182778022843832677)
              ·
                refine ⟨1407224846770879283218627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7505199182778022843832677 1407224846770879283218627)
                ·
                  refine ⟨2110837270156318924827941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407224846770879283218627 2110837270156318924827941)
                  ·
                    refine ⟨395781988154309798405239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2110837270156318924827941 395781988154309798405239)
                    ·
                      rfl

theorem cell22_1156174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1156174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156174 prefixEnd_1156174 := by exact prefixLift 1156174
  have htrace : WordTrace (prefixWord ++ tailWord_1156174) baseStart_1156174 baseEnd_1156174 := by
    simpa [prefixWord, tailWord_1156174, baseEnd_1156174] using wordTrace_append hprefix tailTrace_1156174
  have hstable : (prefixWord ++ tailWord_1156174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156174).length < 2 ^ (prefixWord ++ tailWord_1156174).sum := by decide
  have hdescent : baseEnd_1156174 < baseStart_1156174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156182 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1156182 : Nat := 118140960795 + 1156182 * 2 ^ 59
def prefixEnd_1156182 : Nat := 4983230072969 + 3 ^ 40 * 1156182 * 2
def baseEnd_1156182 : Nat := 395784726717800444205215

theorem tailTrace_1156182 : CollatzResearch.WordTrace tailWord_1156182 prefixEnd_1156182 395784726717800444205215 := by
  unfold tailWord_1156182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635588868584846813131425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28112947931571699340068533 2635588868584846813131425)
  ·
    refine ⟨1976691651438635109848569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2635588868584846813131425 1976691651438635109848569)
    ·
      refine ⟨1482518738578976332386427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1976691651438635109848569 1482518738578976332386427)
      ·
        refine ⟨2223778107868464498579641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482518738578976332386427 2223778107868464498579641)
        ·
          refine ⟨1667833580901348373934731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2223778107868464498579641 1667833580901348373934731)
          ·
            refine ⟨2501750371352022560902097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667833580901348373934731 2501750371352022560902097)
            ·
              refine ⟨1876312778514016920676573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501750371352022560902097 1876312778514016920676573)
              ·
                refine ⟨703617291942756345253715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1876312778514016920676573 703617291942756345253715)
                ·
                  refine ⟨1055425937914134517880573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703617291942756345253715 1055425937914134517880573)
                  ·
                    refine ⟨395784726717800444205215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055425937914134517880573 395784726717800444205215)
                    ·
                      rfl

theorem cell22_1156182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1156182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156182 prefixEnd_1156182 := by exact prefixLift 1156182
  have htrace : WordTrace (prefixWord ++ tailWord_1156182) baseStart_1156182 baseEnd_1156182 := by
    simpa [prefixWord, tailWord_1156182, baseEnd_1156182] using wordTrace_append hprefix tailTrace_1156182
  have hstable : (prefixWord ++ tailWord_1156182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156182).length < 2 ^ (prefixWord ++ tailWord_1156182).sum := by decide
  have hdescent : baseEnd_1156182 < baseStart_1156182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156204 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_1156204 : Nat := 118140960795 + 1156204 * 2 ^ 59
def prefixEnd_1156204 : Nat := 4983230072969 + 3 ^ 40 * 1156204 * 2
def baseEnd_1156204 : Nat := 395792257767399720155147

theorem tailTrace_1156204 : CollatzResearch.WordTrace tailWord_1156204 prefixEnd_1156204 395792257767399720155147 := by
  unfold tailWord_1156204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085112151638923383701833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28113482868851897844935777 21085112151638923383701833)
  ·
    refine ⟨15813834113729192537776375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21085112151638923383701833 15813834113729192537776375)
    ·
      refine ⟨23720751170593788806664563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15813834113729192537776375 23720751170593788806664563)
      ·
        refine ⟨35581126755890683209996845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23720751170593788806664563 35581126755890683209996845)
        ·
          refine ⟨13342922533459006203748817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35581126755890683209996845 13342922533459006203748817)
          ·
            refine ⟨10007191900094254652811613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13342922533459006203748817 10007191900094254652811613)
            ·
              refine ⟨3752696962535345494804355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10007191900094254652811613 3752696962535345494804355)
              ·
                refine ⟨5629045443803018242206533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752696962535345494804355 5629045443803018242206533)
                ·
                  refine ⟨1055446020713065920413725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5629045443803018242206533 1055446020713065920413725)
                  ·
                    refine ⟨395792257767399720155147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055446020713065920413725 395792257767399720155147)
                    ·
                      rfl

theorem cell22_1156204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_1156204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156204 prefixEnd_1156204 := by exact prefixLift 1156204
  have htrace : WordTrace (prefixWord ++ tailWord_1156204) baseStart_1156204 baseEnd_1156204 := by
    simpa [prefixWord, tailWord_1156204, baseEnd_1156204] using wordTrace_append hprefix tailTrace_1156204
  have hstable : (prefixWord ++ tailWord_1156204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156204).length < 2 ^ (prefixWord ++ tailWord_1156204).sum := by decide
  have hdescent : baseEnd_1156204 < baseStart_1156204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156206 : List Nat := [4, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_1156206 : Nat := 118140960795 + 1156206 * 2 ^ 59
def prefixEnd_1156206 : Nat := 4983230072969 + 3 ^ 40 * 1156206 * 2
def baseEnd_1156206 : Nat := 131930980802757460535047

theorem tailTrace_1156206 : CollatzResearch.WordTrace tailWord_1156206 prefixEnd_1156206 131930980802757460535047 := by
  unfold tailWord_1156206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271287156158825138622059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28113531499513734072650981 5271287156158825138622059)
  ·
    refine ⟨7906930734238237707933089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5271287156158825138622059 7906930734238237707933089)
    ·
      refine ⟨5930198050678678280949817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7906930734238237707933089 5930198050678678280949817)
      ·
        refine ⟨4447648538009008710712363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930198050678678280949817 4447648538009008710712363)
        ·
          refine ⟨6671472807013513066068545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4447648538009008710712363 6671472807013513066068545)
          ·
            refine ⟨5003604605260134799551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671472807013513066068545 5003604605260134799551409)
            ·
              refine ⟨3752703453945101099663557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5003604605260134799551409 3752703453945101099663557)
              ·
                refine ⟨703631897614706456186917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3752703453945101099663557 703631897614706456186917)
                ·
                  refine ⟨131930980802757460535047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 703631897614706456186917 131930980802757460535047)
                  ·
                    rfl

theorem cell22_1156206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_1156206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156206 prefixEnd_1156206 := by exact prefixLift 1156206
  have htrace : WordTrace (prefixWord ++ tailWord_1156206) baseStart_1156206 baseEnd_1156206 := by
    simpa [prefixWord, tailWord_1156206, baseEnd_1156206] using wordTrace_append hprefix tailTrace_1156206
  have hstable : (prefixWord ++ tailWord_1156206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156206).length < 2 ^ (prefixWord ++ tailWord_1156206).sum := by decide
  have hdescent : baseEnd_1156206 < baseStart_1156206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156279 : List Nat := [1, 1, 3, 1, 4, 1, 3, 3, 5]
def baseStart_1156279 : Nat := 118140960795 + 1156279 * 2 ^ 59
def prefixEnd_1156279 : Nat := 4983230072969 + 3 ^ 40 * 1156279 * 2
def baseEnd_1156279 : Nat := 131939310600041508176639

theorem tailTrace_1156279 : CollatzResearch.WordTrace tailWord_1156279 prefixEnd_1156279 131939310600041508176639 := by
  unfold tailWord_1156279
  simp only [CollatzResearch.WordTrace]
  refine ⟨42172959778006134576383891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28115306518670756384255927 42172959778006134576383891)
  ·
    refine ⟨63259439667009201864575837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42172959778006134576383891 63259439667009201864575837)
    ·
      refine ⟨23722289875128450699215939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63259439667009201864575837 23722289875128450699215939)
      ·
        refine ⟨35583434812692676048823909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23722289875128450699215939 35583434812692676048823909)
        ·
          refine ⟨6671894027379876759154483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35583434812692676048823909 6671894027379876759154483)
          ·
            refine ⟨10007841041069815138731725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6671894027379876759154483 10007841041069815138731725)
            ·
              refine ⟨3752940390401180677024397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10007841041069815138731725 3752940390401180677024397)
              ·
                refine ⟨1407352646400442753884149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3752940390401180677024397 1407352646400442753884149)
                ·
                  refine ⟨131939310600041508176639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1407352646400442753884149 131939310600041508176639)
                  ·
                    rfl

theorem cell22_1156279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 5].length) (baseStart_1156279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156279 prefixEnd_1156279 := by exact prefixLift 1156279
  have htrace : WordTrace (prefixWord ++ tailWord_1156279) baseStart_1156279 baseEnd_1156279 := by
    simpa [prefixWord, tailWord_1156279, baseEnd_1156279] using wordTrace_append hprefix tailTrace_1156279
  have hstable : (prefixWord ++ tailWord_1156279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156279).length < 2 ^ (prefixWord ++ tailWord_1156279).sum := by decide
  have hdescent : baseEnd_1156279 < baseStart_1156279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156307 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 8]
def baseStart_1156307 : Nat := 118140960795 + 1156307 * 2 ^ 59
def prefixEnd_1156307 : Nat := 4983230072969 + 3 ^ 40 * 1156307 * 2
def baseEnd_1156307 : Nat := 131942505590780594943277

theorem tailTrace_1156307 : CollatzResearch.WordTrace tailWord_1156307 prefixEnd_1156307 131942505590780594943277 := by
  unfold tailWord_1156307
  simp only [CollatzResearch.WordTrace]
  refine ⟨42173981021904695358403175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28115987347936463572268783 42173981021904695358403175)
  ·
    refine ⟨63260971532857043037604763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42173981021904695358403175 63260971532857043037604763)
    ·
      refine ⟨94891457299285564556407145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63260971532857043037604763 94891457299285564556407145)
      ·
        refine ⟨71168592974464173417305359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94891457299285564556407145 71168592974464173417305359)
        ·
          refine ⟨106752889461696260125958039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71168592974464173417305359 106752889461696260125958039)
          ·
            refine ⟨160129334192544390188937059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106752889461696260125958039 160129334192544390188937059)
            ·
              refine ⟨240194001288816585283405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160129334192544390188937059 240194001288816585283405589)
              ·
                refine ⟨11259093810413277435159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 240194001288816585283405589 11259093810413277435159637)
                ·
                  refine ⟨131942505590780594943277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11259093810413277435159637 131942505590780594943277)
                  ·
                    rfl

theorem cell22_1156307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_1156307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156307 prefixEnd_1156307 := by exact prefixLift 1156307
  have htrace : WordTrace (prefixWord ++ tailWord_1156307) baseStart_1156307 baseEnd_1156307 := by
    simpa [prefixWord, tailWord_1156307, baseEnd_1156307] using wordTrace_append hprefix tailTrace_1156307
  have hstable : (prefixWord ++ tailWord_1156307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156307).length < 2 ^ (prefixWord ++ tailWord_1156307).sum := by decide
  have hdescent : baseEnd_1156307 < baseStart_1156307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156339 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_1156339 : Nat := 118140960795 + 1156339 * 2 ^ 59
def prefixEnd_1156339 : Nat := 4983230072969 + 3 ^ 40 * 1156339 * 2
def baseEnd_1156339 : Nat := 395838471026304368029733

theorem tailTrace_1156339 : CollatzResearch.WordTrace tailWord_1156339 prefixEnd_1156339 395838471026304368029733 := by
  unfold tailWord_1156339
  simp only [CollatzResearch.WordTrace]
  refine ⟨42175148157788764823568071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28116765438525843215712047 42175148157788764823568071)
  ·
    refine ⟨63262722236683147235352107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42175148157788764823568071 63262722236683147235352107)
    ·
      refine ⟨94894083355024720853028161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63262722236683147235352107 94894083355024720853028161)
      ·
        refine ⟨71170562516268540639771121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94894083355024720853028161 71170562516268540639771121)
        ·
          refine ⟨53377921887201405479828341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71170562516268540639771121 53377921887201405479828341)
          ·
            refine ⟨5004180176925131763733907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53377921887201405479828341 5004180176925131763733907)
            ·
              refine ⟨7506270265387697645600861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5004180176925131763733907 7506270265387697645600861)
              ·
                refine ⟨2814851349520386617100323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7506270265387697645600861 2814851349520386617100323)
                ·
                  refine ⟨4222277024280579925650485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814851349520386617100323 4222277024280579925650485)
                  ·
                    refine ⟨395838471026304368029733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4222277024280579925650485 395838471026304368029733)
                    ·
                      rfl

theorem cell22_1156339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_1156339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156339 prefixEnd_1156339 := by exact prefixLift 1156339
  have htrace : WordTrace (prefixWord ++ tailWord_1156339) baseStart_1156339 baseEnd_1156339 := by
    simpa [prefixWord, tailWord_1156339, baseEnd_1156339] using wordTrace_append hprefix tailTrace_1156339
  have hstable : (prefixWord ++ tailWord_1156339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156339).length < 2 ^ (prefixWord ++ tailWord_1156339).sum := by decide
  have hdescent : baseEnd_1156339 < baseStart_1156339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156356 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1156356 : Nat := 118140960795 + 1156356 * 2 ^ 59
def prefixEnd_1156356 : Nat := 4983230072969 + 3 ^ 40 * 1156356 * 2
def baseEnd_1156356 : Nat := 395844290473721990354681

theorem tailTrace_1156356 : CollatzResearch.WordTrace tailWord_1156356 prefixEnd_1156356 395844290473721990354681 := by
  unfold tailWord_1156356
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087884099363588363468461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28117178799151451151291281 21087884099363588363468461)
  ·
    refine ⟨7907956537261345636300673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21087884099363588363468461 7907956537261345636300673)
    ·
      refine ⟨5930967402946009227225505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7907956537261345636300673 5930967402946009227225505)
      ·
        refine ⟨4448225552209506920419129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5930967402946009227225505 4448225552209506920419129)
        ·
          refine ⟨3336169164157130190314347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4448225552209506920419129 3336169164157130190314347)
          ·
            refine ⟨5004253746235695285471521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336169164157130190314347 5004253746235695285471521)
            ·
              refine ⟨3753190309676771464103641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5004253746235695285471521 3753190309676771464103641)
              ·
                refine ⟨2814892732257578598077731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753190309676771464103641 2814892732257578598077731)
                ·
                  refine ⟨4222339098386367897116597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814892732257578598077731 4222339098386367897116597)
                  ·
                    refine ⟨395844290473721990354681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4222339098386367897116597 395844290473721990354681)
                    ·
                      rfl

theorem cell22_1156356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1156356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156356 prefixEnd_1156356 := by exact prefixLift 1156356
  have htrace : WordTrace (prefixWord ++ tailWord_1156356) baseStart_1156356 baseEnd_1156356 := by
    simpa [prefixWord, tailWord_1156356, baseEnd_1156356] using wordTrace_append hprefix tailTrace_1156356
  have hstable : (prefixWord ++ tailWord_1156356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156356).length < 2 ^ (prefixWord ++ tailWord_1156356).sum := by decide
  have hdescent : baseEnd_1156356 < baseStart_1156356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156360 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_1156360 : Nat := 118140960795 + 1156360 * 2 ^ 59
def prefixEnd_1156360 : Nat := 4983230072969 + 3 ^ 40 * 1156360 * 2
def baseEnd_1156360 : Nat := 395845659755467313254669

theorem tailTrace_1156360 : CollatzResearch.WordTrace tailWord_1156360 prefixEnd_1156360 395845659755467313254669 := by
  unfold tailWord_1156360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087957045356342705041267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28117276060475123606721689 21087957045356342705041267)
  ·
    refine ⟨31631935568034514057561901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21087957045356342705041267 31631935568034514057561901)
    ·
      refine ⟨11861975838012942771585713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31631935568034514057561901 11861975838012942771585713)
      ·
        refine ⟨8896481878509707078689285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11861975838012942771585713 8896481878509707078689285)
        ·
          refine ⟨1668090352220570077254241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8896481878509707078689285 1668090352220570077254241)
          ·
            refine ⟨1251067764165427557940681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1668090352220570077254241 1251067764165427557940681)
            ·
              refine ⟨938300823124070668455511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1251067764165427557940681 938300823124070668455511)
              ·
                refine ⟨1407451234686106002683267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938300823124070668455511 1407451234686106002683267)
                ·
                  refine ⟨2111176852029159004024901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1407451234686106002683267 2111176852029159004024901)
                  ·
                    refine ⟨395845659755467313254669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111176852029159004024901 395845659755467313254669)
                    ·
                      rfl

theorem cell22_1156360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_1156360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156360 prefixEnd_1156360 := by exact prefixLift 1156360
  have htrace : WordTrace (prefixWord ++ tailWord_1156360) baseStart_1156360 baseEnd_1156360 := by
    simpa [prefixWord, tailWord_1156360, baseEnd_1156360] using wordTrace_append hprefix tailTrace_1156360
  have hstable : (prefixWord ++ tailWord_1156360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156360).length < 2 ^ (prefixWord ++ tailWord_1156360).sum := by decide
  have hdescent : baseEnd_1156360 < baseStart_1156360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156422 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1156422 : Nat := 118140960795 + 1156422 * 2 ^ 59
def prefixEnd_1156422 : Nat := 4983230072969 + 3 ^ 40 * 1156422 * 2
def baseEnd_1156422 : Nat := 395866883622519818204479

theorem tailTrace_1156422 : CollatzResearch.WordTrace tailWord_1156422 prefixEnd_1156422 395866883622519818204479 := by
  unfold tailWord_1156422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318067981765252187463735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28118783610992046665893013 1318067981765252187463735)
  ·
    refine ⟨1977101972647878281195603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318067981765252187463735 1977101972647878281195603)
    ·
      refine ⟨2965652958971817421793405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1977101972647878281195603 2965652958971817421793405)
      ·
        refine ⟨1112119859614431533172527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2965652958971817421793405 1112119859614431533172527)
        ·
          refine ⟨1668179789421647299758791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112119859614431533172527 1668179789421647299758791)
          ·
            refine ⟨2502269684132470949638187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668179789421647299758791 2502269684132470949638187)
            ·
              refine ⟨3753404526198706424457281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502269684132470949638187 3753404526198706424457281)
              ·
                refine ⟨2815053394649029818342961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753404526198706424457281 2815053394649029818342961)
                ·
                  refine ⟨2111290045986772363757221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2815053394649029818342961 2111290045986772363757221)
                  ·
                    refine ⟨395866883622519818204479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2111290045986772363757221 395866883622519818204479)
                    ·
                      rfl

theorem cell22_1156422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1156422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156422 prefixEnd_1156422 := by exact prefixLift 1156422
  have htrace : WordTrace (prefixWord ++ tailWord_1156422) baseStart_1156422 baseEnd_1156422 := by
    simpa [prefixWord, tailWord_1156422, baseEnd_1156422] using wordTrace_append hprefix tailTrace_1156422
  have hstable : (prefixWord ++ tailWord_1156422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156422).length < 2 ^ (prefixWord ++ tailWord_1156422).sum := by decide
  have hdescent : baseEnd_1156422 < baseStart_1156422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156435 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 1, 3]
def baseStart_1156435 : Nat := 118140960795 + 1156435 * 2 ^ 59
def prefixEnd_1156435 : Nat := 4983230072969 + 3 ^ 40 * 1156435 * 2
def baseEnd_1156435 : Nat := 395871333788192117629439

theorem tailTrace_1156435 : CollatzResearch.WordTrace tailWord_1156435 prefixEnd_1156435 395871333788192117629439 := by
  unfold tailWord_1156435
  simp only [CollatzResearch.WordTrace]
  refine ⟨42178649565440973219062759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28119099710293982146041839 42178649565440973219062759)
  ·
    refine ⟨63267974348161459828594139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42178649565440973219062759 63267974348161459828594139)
    ·
      refine ⟨94901961522242189742891209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63267974348161459828594139 94901961522242189742891209)
      ·
        refine ⟨71176471141681642307168407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94901961522242189742891209 71176471141681642307168407)
        ·
          refine ⟨106764706712522463460752611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71176471141681642307168407 106764706712522463460752611)
          ·
            refine ⟨160147060068783695191128917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106764706712522463460752611 160147060068783695191128917)
            ·
              refine ⟨938361680090529464010521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 160147060068783695191128917 938361680090529464010521)
              ·
                refine ⟨703771260067897098007891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938361680090529464010521 703771260067897098007891)
                ·
                  refine ⟨1055656890101845647011837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703771260067897098007891 1055656890101845647011837)
                  ·
                    refine ⟨395871333788192117629439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055656890101845647011837 395871333788192117629439)
                    ·
                      rfl

theorem cell22_1156435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 3].length) (baseStart_1156435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156435 prefixEnd_1156435 := by exact prefixLift 1156435
  have htrace : WordTrace (prefixWord ++ tailWord_1156435) baseStart_1156435 baseEnd_1156435 := by
    simpa [prefixWord, tailWord_1156435, baseEnd_1156435] using wordTrace_append hprefix tailTrace_1156435
  have hstable : (prefixWord ++ tailWord_1156435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156435).length < 2 ^ (prefixWord ++ tailWord_1156435).sum := by decide
  have hdescent : baseEnd_1156435 < baseStart_1156435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156448 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 5]
def baseStart_1156448 : Nat := 118140960795 + 1156448 * 2 ^ 59
def prefixEnd_1156448 : Nat := 4983230072969 + 3 ^ 40 * 1156448 * 2
def baseEnd_1156448 : Nat := 131958594651288139018133

theorem tailTrace_1156448 : CollatzResearch.WordTrace tailWord_1156448 prefixEnd_1156448 131958594651288139018133 := by
  unfold tailWord_1156448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21089561857196938219642999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28119415809595917626190665 21089561857196938219642999)
  ·
    refine ⟨31634342785795407329464499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21089561857196938219642999 31634342785795407329464499)
    ·
      refine ⟨47451514178693110994196749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31634342785795407329464499 47451514178693110994196749)
      ·
        refine ⟨17794317817009916622823781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47451514178693110994196749 17794317817009916622823781)
        ·
          refine ⟨3336434590689359366779459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17794317817009916622823781 3336434590689359366779459)
          ·
            refine ⟨5004651886034039050169189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3336434590689359366779459 5004651886034039050169189)
            ·
              refine ⟨938372228631382321906723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5004651886034039050169189 938372228631382321906723)
              ·
                refine ⟨1407558342947073482860085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938372228631382321906723 1407558342947073482860085)
                ·
                  refine ⟨131958594651288139018133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1407558342947073482860085 131958594651288139018133)
                  ·
                    rfl

theorem cell22_1156448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_1156448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156448 prefixEnd_1156448 := by exact prefixLift 1156448
  have htrace : WordTrace (prefixWord ++ tailWord_1156448) baseStart_1156448 baseEnd_1156448 := by
    simpa [prefixWord, tailWord_1156448, baseEnd_1156448] using wordTrace_append hprefix tailTrace_1156448
  have hstable : (prefixWord ++ tailWord_1156448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156448).length < 2 ^ (prefixWord ++ tailWord_1156448).sum := by decide
  have hdescent : baseEnd_1156448 < baseStart_1156448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156506 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1156506 : Nat := 118140960795 + 1156506 * 2 ^ 59
def prefixEnd_1156506 : Nat := 4983230072969 + 3 ^ 40 * 1156506 * 2
def baseEnd_1156506 : Nat := 395895638539171599104221

theorem tailTrace_1156506 : CollatzResearch.WordTrace tailWord_1156506 prefixEnd_1156506 395895638539171599104221 := by
  unfold tailWord_1156506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10545309787045938086224343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28120826098789168229931581 10545309787045938086224343)
  ·
    refine ⟨15817964680568907129336515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10545309787045938086224343 15817964680568907129336515)
    ·
      refine ⟨23726947020853360694004773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15817964680568907129336515 23726947020853360694004773)
      ·
        refine ⟨4448802566410005130125895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23726947020853360694004773 4448802566410005130125895)
        ·
          refine ⟨6673203849615007695188843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448802566410005130125895 6673203849615007695188843)
          ·
            refine ⟨10009805774422511542783265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6673203849615007695188843 10009805774422511542783265)
            ·
              refine ⟨7507354330816883657087449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10009805774422511542783265 7507354330816883657087449)
              ·
                refine ⟨5630515748112662742815587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7507354330816883657087449 5630515748112662742815587)
                ·
                  refine ⟨8445773622168994114223381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5630515748112662742815587 8445773622168994114223381)
                  ·
                    refine ⟨395895638539171599104221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8445773622168994114223381 395895638539171599104221)
                    ·
                      rfl

theorem cell22_1156506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1156506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156506 prefixEnd_1156506 := by exact prefixLift 1156506
  have htrace : WordTrace (prefixWord ++ tailWord_1156506) baseStart_1156506 baseEnd_1156506 := by
    simpa [prefixWord, tailWord_1156506, baseEnd_1156506] using wordTrace_append hprefix tailTrace_1156506
  have hstable : (prefixWord ++ tailWord_1156506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156506).length < 2 ^ (prefixWord ++ tailWord_1156506).sum := by decide
  have hdescent : baseEnd_1156506 < baseStart_1156506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156510 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1156510 : Nat := 118140960795 + 1156510 * 2 ^ 59
def prefixEnd_1156510 : Nat := 4983230072969 + 3 ^ 40 * 1156510 * 2
def baseEnd_1156510 : Nat := 131965669273638974001403

theorem tailTrace_1156510 : CollatzResearch.WordTrace tailWord_1156510 prefixEnd_1156510 131965669273638974001403 := by
  unfold tailWord_1156510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5272673130021157628505373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28120923360112840685361989 5272673130021157628505373)
  ·
    refine ⟨1977252423757934110689515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5272673130021157628505373 1977252423757934110689515)
    ·
      refine ⟨2965878635636901166034273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1977252423757934110689515 2965878635636901166034273)
      ·
        refine ⟨2224408976727675874525705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2965878635636901166034273 2224408976727675874525705)
        ·
          refine ⟨1668306732545756905894279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224408976727675874525705 1668306732545756905894279)
          ·
            refine ⟨2502460098818635358841419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668306732545756905894279 2502460098818635358841419)
            ·
              refine ⟨3753690148227953038262129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2502460098818635358841419 3753690148227953038262129)
              ·
                refine ⟨2815267611170964778696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3753690148227953038262129 2815267611170964778696597)
                ·
                  refine ⟨131965669273638974001403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2815267611170964778696597 131965669273638974001403)
                  ·
                    rfl

theorem cell22_1156510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1156510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156510 prefixEnd_1156510 := by exact prefixLift 1156510
  have htrace : WordTrace (prefixWord ++ tailWord_1156510) baseStart_1156510 baseEnd_1156510 := by
    simpa [prefixWord, tailWord_1156510, baseEnd_1156510] using wordTrace_append hprefix tailTrace_1156510
  have hstable : (prefixWord ++ tailWord_1156510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156510).length < 2 ^ (prefixWord ++ tailWord_1156510).sum := by decide
  have hdescent : baseEnd_1156510 < baseStart_1156510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156611 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 6]
def baseStart_1156611 : Nat := 118140960795 + 1156611 * 2 ^ 59
def prefixEnd_1156611 : Nat := 4983230072969 + 3 ^ 40 * 1156611 * 2
def baseEnd_1156611 : Nat := 131977194061662108409633

theorem tailTrace_1156611 : CollatzResearch.WordTrace tailWord_1156611 prefixEnd_1156611 131977194061662108409633 := by
  unfold tailWord_1156611
  simp only [CollatzResearch.WordTrace]
  refine ⟨42185068812803355277469687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28123379208535570184979791 42185068812803355277469687)
  ·
    refine ⟨63277603219205032916204531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42185068812803355277469687 63277603219205032916204531)
    ·
      refine ⟨94916404828807549374306797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63277603219205032916204531 94916404828807549374306797)
      ·
        refine ⟨35593651810802831015365049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94916404828807549374306797 35593651810802831015365049)
        ·
          refine ⟨26695238858102123261523787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35593651810802831015365049 26695238858102123261523787)
          ·
            refine ⟨40042858287153184892285681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26695238858102123261523787 40042858287153184892285681)
            ·
              refine ⟨30032143715364888669214261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40042858287153184892285681 30032143715364888669214261)
              ·
                refine ⟨2815513473315458312738837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30032143715364888669214261 2815513473315458312738837)
                ·
                  refine ⟨131977194061662108409633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2815513473315458312738837 131977194061662108409633)
                  ·
                    rfl

theorem cell22_1156611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_1156611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156611 prefixEnd_1156611 := by exact prefixLift 1156611
  have htrace : WordTrace (prefixWord ++ tailWord_1156611) baseStart_1156611 baseEnd_1156611 := by
    simpa [prefixWord, tailWord_1156611, baseEnd_1156611] using wordTrace_append hprefix tailTrace_1156611
  have hstable : (prefixWord ++ tailWord_1156611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156611).length < 2 ^ (prefixWord ++ tailWord_1156611).sum := by decide
  have hdescent : baseEnd_1156611 < baseStart_1156611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156690 : List Nat := [3, 2, 2, 1, 2, 3, 3, 6]
def baseStart_1156690 : Nat := 118140960795 + 1156690 * 2 ^ 59
def prefixEnd_1156690 : Nat := 4983230072969 + 3 ^ 40 * 1156690 * 2
def baseEnd_1156690 : Nat := 43995402833272939167073

theorem tailTrace_1156690 : CollatzResearch.WordTrace tailWord_1156690 prefixEnd_1156690 43995402833272939167073 := by
  unfold tailWord_1156690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10546987544879287942398881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28125300119678101179730349 10546987544879287942398881)
  ·
    refine ⟨7910240658659465956799161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10546987544879287942398881 7910240658659465956799161)
    ·
      refine ⟨5932680493994599467599371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7910240658659465956799161 5932680493994599467599371)
      ·
        refine ⟨8899020740991899201399057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5932680493994599467599371 8899020740991899201399057)
        ·
          refine ⟨6674265555743924401049293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8899020740991899201399057 6674265555743924401049293)
          ·
            refine ⟨2502849583403971650393485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6674265555743924401049293 2502849583403971650393485)
            ·
              refine ⟨938568593776489368897557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2502849583403971650393485 938568593776489368897557)
              ·
                refine ⟨43995402833272939167073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 938568593776489368897557 43995402833272939167073)
                ·
                  rfl

theorem cell22_1156690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_1156690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156690 prefixEnd_1156690 := by exact prefixLift 1156690
  have htrace : WordTrace (prefixWord ++ tailWord_1156690) baseStart_1156690 baseEnd_1156690 := by
    simpa [prefixWord, tailWord_1156690, baseEnd_1156690] using wordTrace_append hprefix tailTrace_1156690
  have hstable : (prefixWord ++ tailWord_1156690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156690).length < 2 ^ (prefixWord ++ tailWord_1156690).sum := by decide
  have hdescent : baseEnd_1156690 < baseStart_1156690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156722 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1156722 : Nat := 118140960795 + 1156722 * 2 ^ 59
def prefixEnd_1156722 : Nat := 4983230072969 + 3 ^ 40 * 1156722 * 2
def baseEnd_1156722 : Nat := 395969579753419035703559

theorem tailTrace_1156722 : CollatzResearch.WordTrace tailWord_1156722 prefixEnd_1156722 395969579753419035703559 := by
  unfold tailWord_1156722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10547279328850305308690105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28126078210267480823173613 10547279328850305308690105)
  ·
    refine ⟨7910459496637728981517579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10547279328850305308690105 7910459496637728981517579)
    ·
      refine ⟨11865689244956593472276369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7910459496637728981517579 11865689244956593472276369)
      ·
        refine ⟨8899266933717445104207277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11865689244956593472276369 8899266933717445104207277)
        ·
          refine ⟨3337225100144041914077729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8899266933717445104207277 3337225100144041914077729)
          ·
            refine ⟨2502918825108031435558297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3337225100144041914077729 2502918825108031435558297)
            ·
              refine ⟨1877189118831023576668723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2502918825108031435558297 1877189118831023576668723)
              ·
                refine ⟨2815783678246535365003085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877189118831023576668723 2815783678246535365003085)
                ·
                  refine ⟨1055918879342450761876157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2815783678246535365003085 1055918879342450761876157)
                  ·
                    refine ⟨395969579753419035703559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055918879342450761876157 395969579753419035703559)
                    ·
                      rfl

theorem cell22_1156722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1156722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156722 prefixEnd_1156722 := by exact prefixLift 1156722
  have htrace : WordTrace (prefixWord ++ tailWord_1156722) baseStart_1156722 baseEnd_1156722 := by
    simpa [prefixWord, tailWord_1156722, baseEnd_1156722] using wordTrace_append hprefix tailTrace_1156722
  have hstable : (prefixWord ++ tailWord_1156722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156722).length < 2 ^ (prefixWord ++ tailWord_1156722).sum := by decide
  have hdescent : baseEnd_1156722 < baseStart_1156722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156793 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1156793 : Nat := 118140960795 + 1156793 * 2 ^ 59
def prefixEnd_1156793 : Nat := 4983230072969 + 3 ^ 40 * 1156793 * 2
def baseEnd_1156793 : Nat := 395993884504398517178341

theorem tailTrace_1156793 : CollatzResearch.WordTrace tailWord_1156793 prefixEnd_1156793 395993884504398517178341 := by
  unfold tailWord_1156793
  simp only [CollatzResearch.WordTrace]
  refine ⟨42191706898144000360595033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28127804598762666907063355 42191706898144000360595033)
  ·
    refine ⟨31643780173608000270446275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42191706898144000360595033 31643780173608000270446275)
    ·
      refine ⟨47465670260412000405669413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31643780173608000270446275 47465670260412000405669413)
      ·
        refine ⟨8899813173827250076063015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47465670260412000405669413 8899813173827250076063015)
        ·
          refine ⟨13349719760740875114094523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8899813173827250076063015 13349719760740875114094523)
          ·
            refine ⟨20024579641111312671141785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13349719760740875114094523 20024579641111312671141785)
            ·
              refine ⟨15018434730833484503356339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20024579641111312671141785 15018434730833484503356339)
              ·
                refine ⟨22527652096250226755034509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15018434730833484503356339 22527652096250226755034509)
                ·
                  refine ⟨8447869536093835033137941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22527652096250226755034509 8447869536093835033137941)
                  ·
                    refine ⟨395993884504398517178341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8447869536093835033137941 395993884504398517178341)
                    ·
                      rfl

theorem cell22_1156793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1156793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156793 prefixEnd_1156793 := by exact prefixLift 1156793
  have htrace : WordTrace (prefixWord ++ tailWord_1156793) baseStart_1156793 baseEnd_1156793 := by
    simpa [prefixWord, tailWord_1156793, baseEnd_1156793] using wordTrace_append hprefix tailTrace_1156793
  have hstable : (prefixWord ++ tailWord_1156793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156793).length < 2 ^ (prefixWord ++ tailWord_1156793).sum := by decide
  have hdescent : baseEnd_1156793 < baseStart_1156793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156808 : List Nat := [2, 1, 3, 1, 2, 2, 1, 10]
def baseStart_1156808 : Nat := 118140960795 + 1156808 * 2 ^ 59
def prefixEnd_1156808 : Nat := 4983230072969 + 3 ^ 40 * 1156808 * 2
def baseEnd_1156808 : Nat := 43999891034549275339255

theorem tailTrace_1156808 : CollatzResearch.WordTrace tailWord_1156808 prefixEnd_1156808 43999891034549275339255 := by
  unfold tailWord_1156808
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096126996544828961195539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28128169328726438614927385 21096126996544828961195539)
  ·
    refine ⟨31644190494817243441793309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21096126996544828961195539 31644190494817243441793309)
    ·
      refine ⟨11866571435556466290672491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31644190494817243441793309 11866571435556466290672491)
      ·
        refine ⟨17799857153334699436008737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11866571435556466290672491 17799857153334699436008737)
        ·
          refine ⟨13349892865001024577006553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17799857153334699436008737 13349892865001024577006553)
          ·
            refine ⟨10012419648750768432754915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13349892865001024577006553 10012419648750768432754915)
            ·
              refine ⟨15018629473126152649132373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10012419648750768432754915 15018629473126152649132373)
              ·
                refine ⟨43999891034549275339255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15018629473126152649132373 43999891034549275339255)
                ·
                  rfl

theorem cell22_1156808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_1156808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156808 prefixEnd_1156808 := by exact prefixLift 1156808
  have htrace : WordTrace (prefixWord ++ tailWord_1156808) baseStart_1156808 baseEnd_1156808 := by
    simpa [prefixWord, tailWord_1156808, baseEnd_1156808] using wordTrace_append hprefix tailTrace_1156808
  have hstable : (prefixWord ++ tailWord_1156808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156808).length < 2 ^ (prefixWord ++ tailWord_1156808).sum := by decide
  have hdescent : baseEnd_1156808 < baseStart_1156808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156812 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1156812 : Nat := 118140960795 + 1156812 * 2 ^ 59
def prefixEnd_1156812 : Nat := 4983230072969 + 3 ^ 40 * 1156812 * 2
def baseEnd_1156812 : Nat := 396000388592688800953283

theorem tailTrace_1156812 : CollatzResearch.WordTrace tailWord_1156812 prefixEnd_1156812 396000388592688800953283 := by
  unfold tailWord_1156812
  simp only [CollatzResearch.WordTrace]
  refine ⟨21096199942537583302768345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28128266590050111070357793 21096199942537583302768345)
  ·
    refine ⟨15822149956903187477076259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21096199942537583302768345 15822149956903187477076259)
    ·
      refine ⟨23733224935354781215614389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15822149956903187477076259 23733224935354781215614389)
      ·
        refine ⟨2224989837689510738963849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23733224935354781215614389 2224989837689510738963849)
        ·
          refine ⟨1668742378267133054222887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224989837689510738963849 1668742378267133054222887)
          ·
            refine ⟨2503113567400699581334331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668742378267133054222887 2503113567400699581334331)
            ·
              refine ⟨3754670351101049372001497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503113567400699581334331 3754670351101049372001497)
              ·
                refine ⟨2816002763325787029001123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3754670351101049372001497 2816002763325787029001123)
                ·
                  refine ⟨4224004144988680543501685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816002763325787029001123 4224004144988680543501685)
                  ·
                    refine ⟨396000388592688800953283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4224004144988680543501685 396000388592688800953283)
                    ·
                      rfl

theorem cell22_1156812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1156812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156812 prefixEnd_1156812 := by exact prefixLift 1156812
  have htrace : WordTrace (prefixWord ++ tailWord_1156812) baseStart_1156812 baseEnd_1156812 := by
    simpa [prefixWord, tailWord_1156812, baseEnd_1156812] using wordTrace_append hprefix tailTrace_1156812
  have hstable : (prefixWord ++ tailWord_1156812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156812).length < 2 ^ (prefixWord ++ tailWord_1156812).sum := by decide
  have hdescent : baseEnd_1156812 < baseStart_1156812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156874 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_1156874 : Nat := 118140960795 + 1156874 * 2 ^ 59
def prefixEnd_1156874 : Nat := 4983230072969 + 3 ^ 40 * 1156874 * 2
def baseEnd_1156874 : Nat := 396021612459741305903093

theorem tailTrace_1156874 : CollatzResearch.WordTrace tailWord_1156874 prefixEnd_1156874 396021612459741305903093 := by
  unfold tailWord_1156874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10548665302712637798573419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28129774140567034129529117 10548665302712637798573419)
  ·
    refine ⟨15822997954068956697860129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10548665302712637798573419 15822997954068956697860129)
    ·
      refine ⟨11867248465551717523395097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15822997954068956697860129 11867248465551717523395097)
      ·
        refine ⟨8900436349163788142546323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11867248465551717523395097 8900436349163788142546323)
        ·
          refine ⟨13350654523745682213819485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8900436349163788142546323 13350654523745682213819485)
          ·
            refine ⟨5006495446404630830182307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13350654523745682213819485 5006495446404630830182307)
            ·
              refine ⟨7509743169606946245273461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006495446404630830182307 7509743169606946245273461)
              ·
                refine ⟨704038422150651210494387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7509743169606946245273461 704038422150651210494387)
                ·
                  refine ⟨1056057633225976815741581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704038422150651210494387 1056057633225976815741581)
                  ·
                    refine ⟨396021612459741305903093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056057633225976815741581 396021612459741305903093)
                    ·
                      rfl

theorem cell22_1156874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_1156874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156874 prefixEnd_1156874 := by exact prefixLift 1156874
  have htrace : WordTrace (prefixWord ++ tailWord_1156874) baseStart_1156874 baseEnd_1156874 := by
    simpa [prefixWord, tailWord_1156874, baseEnd_1156874] using wordTrace_append hprefix tailTrace_1156874
  have hstable : (prefixWord ++ tailWord_1156874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156874).length < 2 ^ (prefixWord ++ tailWord_1156874).sum := by decide
  have hdescent : baseEnd_1156874 < baseStart_1156874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156885 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1156885 : Nat := 118140960795 + 1156885 * 2 ^ 59
def prefixEnd_1156885 : Nat := 4983230072969 + 3 ^ 40 * 1156885 * 2
def baseEnd_1156885 : Nat := 396025377984540943878059

theorem tailTrace_1156885 : CollatzResearch.WordTrace tailWord_1156885 prefixEnd_1156885 396025377984540943878059 := by
  unfold tailWord_1156885
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195062413810700072944109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28130041609207133381962739 42195062413810700072944109)
  ·
    refine ⟨15823148405179012527354041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42195062413810700072944109 15823148405179012527354041)
    ·
      refine ⟨11867361303884259395515531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15823148405179012527354041 11867361303884259395515531)
      ·
        refine ⟨17801041955826389093273297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11867361303884259395515531 17801041955826389093273297)
        ·
          refine ⟨13350781466869791819954973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17801041955826389093273297 13350781466869791819954973)
          ·
            refine ⟨5006543050076171932483115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13350781466869791819954973 5006543050076171932483115)
            ·
              refine ⟨7509814575114257898724673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006543050076171932483115 7509814575114257898724673)
              ·
                refine ⟨5632360931335693424043505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7509814575114257898724673 5632360931335693424043505)
                ·
                  refine ⟨4224270698501770068032629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5632360931335693424043505 4224270698501770068032629)
                  ·
                    refine ⟨396025377984540943878059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4224270698501770068032629 396025377984540943878059)
                    ·
                      rfl

theorem cell22_1156885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1156885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156885 prefixEnd_1156885 := by exact prefixLift 1156885
  have htrace : WordTrace (prefixWord ++ tailWord_1156885) baseStart_1156885 baseEnd_1156885 := by
    simpa [prefixWord, tailWord_1156885, baseEnd_1156885] using wordTrace_append hprefix tailTrace_1156885
  have hstable : (prefixWord ++ tailWord_1156885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156885).length < 2 ^ (prefixWord ++ tailWord_1156885).sum := by decide
  have hdescent : baseEnd_1156885 < baseStart_1156885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156887 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 5]
def baseStart_1156887 : Nat := 118140960795 + 1156887 * 2 ^ 59
def prefixEnd_1156887 : Nat := 4983230072969 + 3 ^ 40 * 1156887 * 2
def baseEnd_1156887 : Nat := 132008687541804535109351

theorem tailTrace_1156887 : CollatzResearch.WordTrace tailWord_1156887 prefixEnd_1156887 132008687541804535109351 := by
  unfold tailWord_1156887
  simp only [CollatzResearch.WordTrace]
  refine ⟨42195135359803454414516915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28130090239868969609677943 42195135359803454414516915)
  ·
    refine ⟨63292703039705181621775373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42195135359803454414516915 63292703039705181621775373)
    ·
      refine ⟨23734763639889443108165765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63292703039705181621775373 23734763639889443108165765)
      ·
        refine ⟨4450268182479270582781081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23734763639889443108165765 4450268182479270582781081)
        ·
          refine ⟨3337701136859452937085811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4450268182479270582781081 3337701136859452937085811)
          ·
            refine ⟨5006551705289179405628717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3337701136859452937085811 5006551705289179405628717)
            ·
              refine ⟨1877456889483442277110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5006551705289179405628717 1877456889483442277110769)
              ·
                refine ⟨1408092667112581707833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1877456889483442277110769 1408092667112581707833077)
                ·
                  refine ⟨132008687541804535109351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408092667112581707833077 132008687541804535109351)
                  ·
                    rfl

theorem cell22_1156887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 5].length) (baseStart_1156887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156887 prefixEnd_1156887 := by exact prefixLift 1156887
  have htrace : WordTrace (prefixWord ++ tailWord_1156887) baseStart_1156887 baseEnd_1156887 := by
    simpa [prefixWord, tailWord_1156887, baseEnd_1156887] using wordTrace_append hprefix tailTrace_1156887
  have hstable : (prefixWord ++ tailWord_1156887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156887).length < 2 ^ (prefixWord ++ tailWord_1156887).sum := by decide
  have hdescent : baseEnd_1156887 < baseStart_1156887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156904 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_1156904 : Nat := 118140960795 + 1156904 * 2 ^ 59
def prefixEnd_1156904 : Nat := 4983230072969 + 3 ^ 40 * 1156904 * 2
def baseEnd_1156904 : Nat := 132010627357610409217667

theorem tailTrace_1156904 : CollatzResearch.WordTrace tailWord_1156904 prefixEnd_1156904 132010627357610409217667 := by
  unfold tailWord_1156904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097877700370933158942883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28130503600494577545257177 21097877700370933158942883)
  ·
    refine ⟨31646816550556399738414325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097877700370933158942883 31646816550556399738414325)
    ·
      refine ⟨2966889051614662475476343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31646816550556399738414325 2966889051614662475476343)
      ·
        refine ⟨4450333577421993713214515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2966889051614662475476343 4450333577421993713214515)
        ·
          refine ⟨6675500366132990569821773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450333577421993713214515 6675500366132990569821773)
          ·
            refine ⟨2503312637299871463683165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6675500366132990569821773 2503312637299871463683165)
            ·
              refine ⟨938742238987451798881187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2503312637299871463683165 938742238987451798881187)
              ·
                refine ⟨1408113358481177698321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938742238987451798881187 1408113358481177698321781)
                ·
                  refine ⟨132010627357610409217667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1408113358481177698321781 132010627357610409217667)
                  ·
                    rfl

theorem cell22_1156904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_1156904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156904 prefixEnd_1156904 := by exact prefixLift 1156904
  have htrace : WordTrace (prefixWord ++ tailWord_1156904) baseStart_1156904 baseEnd_1156904 := by
    simpa [prefixWord, tailWord_1156904, baseEnd_1156904] using wordTrace_append hprefix tailTrace_1156904
  have hstable : (prefixWord ++ tailWord_1156904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156904).length < 2 ^ (prefixWord ++ tailWord_1156904).sum := by decide
  have hdescent : baseEnd_1156904 < baseStart_1156904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1156960 : List Nat := [2, 1, 1, 3, 3, 2, 1, 9]
def baseStart_1156960 : Nat := 118140960795 + 1156960 * 2 ^ 59
def prefixEnd_1156960 : Nat := 4983230072969 + 3 ^ 40 * 1156960 * 2
def baseEnd_1156960 : Nat := 44005672446362860916981

theorem tailTrace_1156960 : CollatzResearch.WordTrace tailWord_1156960 prefixEnd_1156960 44005672446362860916981 := by
  unfold tailWord_1156960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21098898944269493940962167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28131865259025991921282889 21098898944269493940962167)
  ·
    refine ⟨31648348416404240911443251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21098898944269493940962167 31648348416404240911443251)
    ·
      refine ⟨47472522624606361367164877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31648348416404240911443251 47472522624606361367164877)
      ·
        refine ⟨17802195984227385512686829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47472522624606361367164877 17802195984227385512686829)
        ·
          refine ⟨6675823494085269567257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17802195984227385512686829 6675823494085269567257561)
          ·
            refine ⟨5006867620563952175443171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6675823494085269567257561 5006867620563952175443171)
            ·
              refine ⟨7510301430845928263164757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5006867620563952175443171 7510301430845928263164757)
              ·
                refine ⟨44005672446362860916981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7510301430845928263164757 44005672446362860916981)
                ·
                  rfl

theorem cell22_1156960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_1156960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1156960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1156960 prefixEnd_1156960 := by exact prefixLift 1156960
  have htrace : WordTrace (prefixWord ++ tailWord_1156960) baseStart_1156960 baseEnd_1156960 := by
    simpa [prefixWord, tailWord_1156960, baseEnd_1156960] using wordTrace_append hprefix tailTrace_1156960
  have hstable : (prefixWord ++ tailWord_1156960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1156960).length < 2 ^ (prefixWord ++ tailWord_1156960).sum := by decide
  have hdescent : baseEnd_1156960 < baseStart_1156960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1156960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157026 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1157026 : Nat := 118140960795 + 1157026 * 2 ^ 59
def prefixEnd_1157026 : Nat := 4983230072969 + 3 ^ 40 * 1157026 * 2
def baseEnd_1157026 : Nat := 396073645166063576102627

theorem tailTrace_1157026 : CollatzResearch.WordTrace tailWord_1157026 prefixEnd_1157026 396073645166063576102627 := by
  unfold tailWord_1157026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10550051276574970288456733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28133470070866587435884621 10550051276574970288456733)
  ·
    refine ⟨3956269228715613858171275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10550051276574970288456733 3956269228715613858171275)
    ·
      refine ⟨5934403843073420787256913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3956269228715613858171275 5934403843073420787256913)
      ·
        refine ⟨4450802882305065590442685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5934403843073420787256913 4450802882305065590442685)
        ·
          refine ⟨1669051080864399596416007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4450802882305065590442685 1669051080864399596416007)
          ·
            refine ⟨2503576621296599394624011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669051080864399596416007 2503576621296599394624011)
            ·
              refine ⟨3755364931944899091936017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503576621296599394624011 3755364931944899091936017)
              ·
                refine ⟨2816523698958674318952013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3755364931944899091936017 2816523698958674318952013)
                ·
                  refine ⟨1056196387109502869607005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2816523698958674318952013 1056196387109502869607005)
                  ·
                    refine ⟨396073645166063576102627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056196387109502869607005 396073645166063576102627)
                    ·
                      rfl

theorem cell22_1157026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1157026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157026 prefixEnd_1157026 := by exact prefixLift 1157026
  have htrace : WordTrace (prefixWord ++ tailWord_1157026) baseStart_1157026 baseEnd_1157026 := by
    simpa [prefixWord, tailWord_1157026, baseEnd_1157026] using wordTrace_append hprefix tailTrace_1157026
  have hstable : (prefixWord ++ tailWord_1157026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157026).length < 2 ^ (prefixWord ++ tailWord_1157026).sum := by decide
  have hdescent : baseEnd_1157026 < baseStart_1157026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157067 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 6]
def baseStart_1157067 : Nat := 118140960795 + 1157067 * 2 ^ 59
def prefixEnd_1157067 : Nat := 4983230072969 + 3 ^ 40 * 1157067 * 2
def baseEnd_1157067 : Nat := 132029226767984378609167

theorem tailTrace_1157067 : CollatzResearch.WordTrace tailWord_1157067 prefixEnd_1157067 132029226767984378609167 := by
  unfold tailWord_1157067
  simp only [CollatzResearch.WordTrace]
  refine ⟨42201700499151345156069455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28134466999434230104046303 42201700499151345156069455)
  ·
    refine ⟨63302550748727017734104183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42201700499151345156069455 63302550748727017734104183)
    ·
      refine ⟨94953826123090526601156275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63302550748727017734104183 94953826123090526601156275)
      ·
        refine ⟨142430739184635789901734413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94953826123090526601156275 142430739184635789901734413)
        ·
          refine ⟨53411527194238421213150405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142430739184635789901734413 53411527194238421213150405)
          ·
            refine ⟨10014661348919703977465701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53411527194238421213150405 10014661348919703977465701)
            ·
              refine ⟨1877749002922444495774819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10014661348919703977465701 1877749002922444495774819)
              ·
                refine ⟨2816623504383666743662229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877749002922444495774819 2816623504383666743662229)
                ·
                  refine ⟨132029226767984378609167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2816623504383666743662229 132029226767984378609167)
                  ·
                    rfl

theorem cell22_1157067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_1157067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157067 prefixEnd_1157067 := by exact prefixLift 1157067
  have htrace : WordTrace (prefixWord ++ tailWord_1157067) baseStart_1157067 baseEnd_1157067 := by
    simpa [prefixWord, tailWord_1157067, baseEnd_1157067] using wordTrace_append hprefix tailTrace_1157067
  have hstable : (prefixWord ++ tailWord_1157067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157067).length < 2 ^ (prefixWord ++ tailWord_1157067).sum := by decide
  have hdescent : baseEnd_1157067 < baseStart_1157067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157144 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_1157144 : Nat := 118140960795 + 1157144 * 2 ^ 59
def prefixEnd_1157144 : Nat := 4983230072969 + 3 ^ 40 * 1157144 * 2
def baseEnd_1157144 : Nat := 396114038977550601652265

theorem tailTrace_1157144 : CollatzResearch.WordTrace tailWord_1157144 prefixEnd_1157144 396114038977550601652265 := by
  unfold tailWord_1157144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21102254459936193653311243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28136339279914924871081657 21102254459936193653311243)
  ·
    refine ⟨31653381689904290479966865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21102254459936193653311243 31653381689904290479966865)
    ·
      refine ⟨23740036267428217859975149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31653381689904290479966865 23740036267428217859975149)
      ·
        refine ⟨8902513600285581697490681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23740036267428217859975149 8902513600285581697490681)
        ·
          refine ⟨6676885200214186273118011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8902513600285581697490681 6676885200214186273118011)
          ·
            refine ⟨10015327800321279409677017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676885200214186273118011 10015327800321279409677017)
            ·
              refine ⟨7511495850240959557257763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10015327800321279409677017 7511495850240959557257763)
              ·
                refine ⟨11267243775361439335886645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7511495850240959557257763 11267243775361439335886645)
                ·
                  refine ⟨1056304103940134937739373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11267243775361439335886645 1056304103940134937739373)
                  ·
                    refine ⟨396114038977550601652265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056304103940134937739373 396114038977550601652265)
                    ·
                      rfl

theorem cell22_1157144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_1157144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157144 prefixEnd_1157144 := by exact prefixLift 1157144
  have htrace : WordTrace (prefixWord ++ tailWord_1157144) baseStart_1157144 baseEnd_1157144 := by
    simpa [prefixWord, tailWord_1157144, baseEnd_1157144] using wordTrace_append hprefix tailTrace_1157144
  have hstable : (prefixWord ++ tailWord_1157144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157144).length < 2 ^ (prefixWord ++ tailWord_1157144).sum := by decide
  have hdescent : baseEnd_1157144 < baseStart_1157144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157221 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1157221 : Nat := 118140960795 + 1157221 * 2 ^ 59
def prefixEnd_1157221 : Nat := 4983230072969 + 3 ^ 40 * 1157221 * 2
def baseEnd_1157221 : Nat := 396140397651148067477029

theorem tailTrace_1157221 : CollatzResearch.WordTrace tailWord_1157221 prefixEnd_1157221 396140397651148067477029 := by
  unfold tailWord_1157221
  simp only [CollatzResearch.WordTrace]
  refine ⟨42207317340593429457175517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28138211560395619638117011 42207317340593429457175517)
  ·
    refine ⟨15827744002722536046440819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42207317340593429457175517 15827744002722536046440819)
    ·
      refine ⟨23741616004083804069661229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15827744002722536046440819 23741616004083804069661229)
      ·
        refine ⟨8903106001531426526122961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23741616004083804069661229 8903106001531426526122961)
        ·
          refine ⟨6677329501148569894592221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8903106001531426526122961 6677329501148569894592221)
          ·
            refine ⟨2503998562930713710472083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6677329501148569894592221 2503998562930713710472083)
            ·
              refine ⟨3755997844396070565708125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503998562930713710472083 3755997844396070565708125)
              ·
                refine ⟨1408499191648526462140547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3755997844396070565708125 1408499191648526462140547)
                ·
                  refine ⟨2112748787472789693210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408499191648526462140547 2112748787472789693210821)
                  ·
                    refine ⟨396140397651148067477029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112748787472789693210821 396140397651148067477029)
                    ·
                      rfl

theorem cell22_1157221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1157221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157221 prefixEnd_1157221 := by exact prefixLift 1157221
  have htrace : WordTrace (prefixWord ++ tailWord_1157221) baseStart_1157221 baseEnd_1157221 := by
    simpa [prefixWord, tailWord_1157221, baseEnd_1157221] using wordTrace_append hprefix tailTrace_1157221
  have hstable : (prefixWord ++ tailWord_1157221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157221).length < 2 ^ (prefixWord ++ tailWord_1157221).sum := by decide
  have hdescent : baseEnd_1157221 < baseStart_1157221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157251 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 5]
def baseStart_1157251 : Nat := 118140960795 + 1157251 * 2 ^ 59
def prefixEnd_1157251 : Nat := 4983230072969 + 3 ^ 40 * 1157251 * 2
def baseEnd_1157251 : Nat := 396150667264237989226937

theorem tailTrace_1157251 : CollatzResearch.WordTrace tailWord_1157251 prefixEnd_1157251 396150667264237989226937 := by
  unfold tailWord_1157251
  simp only [CollatzResearch.WordTrace]
  refine ⟨42208411530484744580767607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28138941020323163053845071 42208411530484744580767607)
  ·
    refine ⟨63312617295727116871151411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42208411530484744580767607 63312617295727116871151411)
    ·
      refine ⟨94968925943590675306727117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63312617295727116871151411 94968925943590675306727117)
      ·
        refine ⟨35613347228846503240022669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94968925943590675306727117 35613347228846503240022669)
        ·
          refine ⟨13355005210817438715008501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35613347228846503240022669 13355005210817438715008501)
          ·
            refine ⟨1252031738514134879532047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13355005210817438715008501 1252031738514134879532047)
            ·
              refine ⟨1878047607771202319298071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252031738514134879532047 1878047607771202319298071)
              ·
                refine ⟨2817071411656803478947107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878047607771202319298071 2817071411656803478947107)
                ·
                  refine ⟨4225607117485205218420661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817071411656803478947107 4225607117485205218420661)
                  ·
                    refine ⟨396150667264237989226937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4225607117485205218420661 396150667264237989226937)
                    ·
                      rfl

theorem cell22_1157251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].length) (baseStart_1157251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157251 prefixEnd_1157251 := by exact prefixLift 1157251
  have htrace : WordTrace (prefixWord ++ tailWord_1157251) baseStart_1157251 baseEnd_1157251 := by
    simpa [prefixWord, tailWord_1157251, baseEnd_1157251] using wordTrace_append hprefix tailTrace_1157251
  have hstable : (prefixWord ++ tailWord_1157251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157251).length < 2 ^ (prefixWord ++ tailWord_1157251).sum := by decide
  have hdescent : baseEnd_1157251 < baseStart_1157251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157266 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1157266 : Nat := 118140960795 + 1157266 * 2 ^ 59
def prefixEnd_1157266 : Nat := 4983230072969 + 3 ^ 40 * 1157266 * 2
def baseEnd_1157266 : Nat := 396155802070782950101891

theorem tailTrace_1157266 : CollatzResearch.WordTrace tailWord_1157266 prefixEnd_1157266 396155802070782950101891 := by
  unfold tailWord_1157266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10552239656357600535640913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28139305750286934761709101 10552239656357600535640913)
  ·
    refine ⟨7914179742268200401730685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10552239656357600535640913 7914179742268200401730685)
    ·
      refine ⟨2967817403350575150649007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7914179742268200401730685 2967817403350575150649007)
      ·
        refine ⟨4451726105025862725973511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967817403350575150649007 4451726105025862725973511)
        ·
          refine ⟨6677589157538794088960267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4451726105025862725973511 6677589157538794088960267)
          ·
            refine ⟨10016383736308191133440401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6677589157538794088960267 10016383736308191133440401)
            ·
              refine ⟨7512287802231143350080301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016383736308191133440401 7512287802231143350080301)
              ·
                refine ⟨2817107925836678756280113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7512287802231143350080301 2817107925836678756280113)
                ·
                  refine ⟨2112830944377509067210085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2817107925836678756280113 2112830944377509067210085)
                  ·
                    refine ⟨396155802070782950101891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112830944377509067210085 396155802070782950101891)
                    ·
                      rfl

theorem cell22_1157266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1157266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157266 prefixEnd_1157266 := by exact prefixLift 1157266
  have htrace : WordTrace (prefixWord ++ tailWord_1157266) baseStart_1157266 baseEnd_1157266 := by
    simpa [prefixWord, tailWord_1157266, baseEnd_1157266] using wordTrace_append hprefix tailTrace_1157266
  have hstable : (prefixWord ++ tailWord_1157266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157266).length < 2 ^ (prefixWord ++ tailWord_1157266).sum := by decide
  have hdescent : baseEnd_1157266 < baseStart_1157266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_1157339 : Nat := 118140960795 + 1157339 * 2 ^ 59
def prefixEnd_1157339 : Nat := 4983230072969 + 3 ^ 40 * 1157339 * 2
def baseEnd_1157339 : Nat := 396180791462635093026667

theorem tailTrace_1157339 : CollatzResearch.WordTrace tailWord_1157339 prefixEnd_1157339 396180791462635093026667 := by
  unfold tailWord_1157339
  simp only [CollatzResearch.WordTrace]
  refine ⟨42211621154165935609971071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28141080769443957073314047 42211621154165935609971071)
  ·
    refine ⟨63317431731248903414956607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42211621154165935609971071 63317431731248903414956607)
    ·
      refine ⟨94976147596873355122434911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63317431731248903414956607 94976147596873355122434911)
      ·
        refine ⟨142464221395310032683652367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94976147596873355122434911 142464221395310032683652367)
        ·
          refine ⟨213696332092965049025478551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142464221395310032683652367 213696332092965049025478551)
          ·
            refine ⟨320544498139447573538217827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213696332092965049025478551 320544498139447573538217827)
            ·
              refine ⟨480816747209171360307326741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320544498139447573538217827 480816747209171360307326741)
              ·
                refine ⟨22538285025429907514405941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 480816747209171360307326741 22538285025429907514405941)
                ·
                  refine ⟨2112964221134053829475557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22538285025429907514405941 2112964221134053829475557)
                  ·
                    refine ⟨396180791462635093026667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2112964221134053829475557 396180791462635093026667)
                    ·
                      rfl

theorem cell22_1157339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_1157339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157339 prefixEnd_1157339 := by exact prefixLift 1157339
  have htrace : WordTrace (prefixWord ++ tailWord_1157339) baseStart_1157339 baseEnd_1157339 := by
    simpa [prefixWord, tailWord_1157339, baseEnd_1157339] using wordTrace_append hprefix tailTrace_1157339
  have hstable : (prefixWord ++ tailWord_1157339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157339).length < 2 ^ (prefixWord ++ tailWord_1157339).sum := by decide
  have hdescent : baseEnd_1157339 < baseStart_1157339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157347 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 1, 3]
def baseStart_1157347 : Nat := 118140960795 + 1157347 * 2 ^ 59
def prefixEnd_1157347 : Nat := 4983230072969 + 3 ^ 40 * 1157347 * 2
def baseEnd_1157347 : Nat := 396183530026125738826643

theorem tailTrace_1157347 : CollatzResearch.WordTrace tailWord_1157347 prefixEnd_1157347 396183530026125738826643 := by
  unfold tailWord_1157347
  simp only [CollatzResearch.WordTrace]
  refine ⟨42211912938136952976262295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28141275292091301984174863 42211912938136952976262295)
  ·
    refine ⟨63317869407205429464393443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42211912938136952976262295 63317869407205429464393443)
    ·
      refine ⟨94976804110808144196590165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63317869407205429464393443 94976804110808144196590165)
      ·
        refine ⟨1113009423173532939803791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 94976804110808144196590165 1113009423173532939803791)
        ·
          refine ⟨1669514134760299409705687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113009423173532939803791 1669514134760299409705687)
          ·
            refine ⟨2504271202140449114558531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669514134760299409705687 2504271202140449114558531)
            ·
              refine ⟨3756406803210673671837797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504271202140449114558531 3756406803210673671837797)
              ·
                refine ⟨704326275602001313469587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3756406803210673671837797 704326275602001313469587)
                ·
                  refine ⟨1056489413403001970204381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704326275602001313469587 1056489413403001970204381)
                  ·
                    refine ⟨396183530026125738826643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056489413403001970204381 396183530026125738826643)
                    ·
                      rfl

theorem cell22_1157347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 3].length) (baseStart_1157347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157347 prefixEnd_1157347 := by exact prefixLift 1157347
  have htrace : WordTrace (prefixWord ++ tailWord_1157347) baseStart_1157347 baseEnd_1157347 := by
    simpa [prefixWord, tailWord_1157347, baseEnd_1157347] using wordTrace_append hprefix tailTrace_1157347
  have hstable : (prefixWord ++ tailWord_1157347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157347).length < 2 ^ (prefixWord ++ tailWord_1157347).sum := by decide
  have hdescent : baseEnd_1157347 < baseStart_1157347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157386 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1157386 : Nat := 118140960795 + 1157386 * 2 ^ 59
def prefixEnd_1157386 : Nat := 4983230072969 + 3 ^ 40 * 1157386 * 2
def baseEnd_1157386 : Nat := 396196880523142637101523

theorem tailTrace_1157386 : CollatzResearch.WordTrace tailWord_1157386 prefixEnd_1157386 396196880523142637101523 := by
  unfold tailWord_1157386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553333846248915659233003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28142223589997108424621341 10553333846248915659233003)
  ·
    refine ⟨15830000769373373488849505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10553333846248915659233003 15830000769373373488849505)
    ·
      refine ⟨11872500577030030116637129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15830000769373373488849505 11872500577030030116637129)
      ·
        refine ⟨8904375432772522587477847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11872500577030030116637129 8904375432772522587477847)
        ·
          refine ⟨13356563149158783881216771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904375432772522587477847 13356563149158783881216771)
          ·
            refine ⟨20034844723738175821825157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356563149158783881216771 20034844723738175821825157)
            ·
              refine ⟨3756533385700907966592217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20034844723738175821825157 3756533385700907966592217)
              ·
                refine ⟨2817400039275680974944163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3756533385700907966592217 2817400039275680974944163)
                ·
                  refine ⟨4226100058913521462416245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817400039275680974944163 4226100058913521462416245)
                  ·
                    refine ⟨396196880523142637101523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4226100058913521462416245 396196880523142637101523)
                    ·
                      rfl

theorem cell22_1157386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1157386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157386 prefixEnd_1157386 := by exact prefixLift 1157386
  have htrace : WordTrace (prefixWord ++ tailWord_1157386) baseStart_1157386 baseEnd_1157386 := by
    simpa [prefixWord, tailWord_1157386, baseEnd_1157386] using wordTrace_append hprefix tailTrace_1157386
  have hstable : (prefixWord ++ tailWord_1157386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157386).length < 2 ^ (prefixWord ++ tailWord_1157386).sum := by decide
  have hdescent : baseEnd_1157386 < baseStart_1157386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157388 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_1157388 : Nat := 118140960795 + 1157388 * 2 ^ 59
def prefixEnd_1157388 : Nat := 4983230072969 + 3 ^ 40 * 1157388 * 2
def baseEnd_1157388 : Nat := 132065855054671766183839

theorem tailTrace_1157388 : CollatzResearch.WordTrace tailWord_1157388 prefixEnd_1157388 132065855054671766183839 := by
  unfold tailWord_1157388
  simp only [CollatzResearch.WordTrace]
  refine ⟨21106704165494208489252409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28142272220658944652336545 21106704165494208489252409)
  ·
    refine ⟨15830028124120656366939307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21106704165494208489252409 15830028124120656366939307)
    ·
      refine ⟨23745042186180984550408961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15830028124120656366939307 23745042186180984550408961)
      ·
        refine ⟨17808781639635738412806721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23745042186180984550408961 17808781639635738412806721)
        ·
          refine ⟨13356586229726803809605041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17808781639635738412806721 13356586229726803809605041)
          ·
            refine ⟨10017439672295102857203781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13356586229726803809605041 10017439672295102857203781)
            ·
              refine ⟨1878269938555331785725709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10017439672295102857203781 1878269938555331785725709)
              ·
                refine ⟨704351226958249419647141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878269938555331785725709 704351226958249419647141)
                ·
                  refine ⟨132065855054671766183839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704351226958249419647141 132065855054671766183839)
                  ·
                    rfl

theorem cell22_1157388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_1157388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157388 prefixEnd_1157388 := by exact prefixLift 1157388
  have htrace : WordTrace (prefixWord ++ tailWord_1157388) baseStart_1157388 baseEnd_1157388 := by
    simpa [prefixWord, tailWord_1157388, baseEnd_1157388] using wordTrace_append hprefix tailTrace_1157388
  have hstable : (prefixWord ++ tailWord_1157388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157388).length < 2 ^ (prefixWord ++ tailWord_1157388).sum := by decide
  have hdescent : baseEnd_1157388 < baseStart_1157388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157403 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 2, 3]
def baseStart_1157403 : Nat := 118140960795 + 1157403 * 2 ^ 59
def prefixEnd_1157403 : Nat := 4983230072969 + 3 ^ 40 * 1157403 * 2
def baseEnd_1157403 : Nat := 396202699970560259426471

theorem tailTrace_1157403 : CollatzResearch.WordTrace tailWord_1157403 prefixEnd_1157403 396202699970560259426471 := by
  unfold tailWord_1157403
  simp only [CollatzResearch.WordTrace]
  refine ⟨42213955425934074540300863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28142636950622716360200575 42213955425934074540300863)
  ·
    refine ⟨63320933138901111810451295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42213955425934074540300863 63320933138901111810451295)
    ·
      refine ⟨94981399708351667715676943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63320933138901111810451295 94981399708351667715676943)
      ·
        refine ⟨142472099562527501573515415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94981399708351667715676943 142472099562527501573515415)
        ·
          refine ⟨213708149343791252360273123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142472099562527501573515415 213708149343791252360273123)
          ·
            refine ⟨320562224015686878540409685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213708149343791252360273123 320562224015686878540409685)
            ·
              refine ⟨1878294281341915303947713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 320562224015686878540409685 1878294281341915303947713)
              ·
                refine ⟨1408720711006436477960785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878294281341915303947713 1408720711006436477960785)
                ·
                  refine ⟨1056540533254827358470589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408720711006436477960785 1056540533254827358470589)
                  ·
                    refine ⟨396202699970560259426471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056540533254827358470589 396202699970560259426471)
                    ·
                      rfl

theorem cell22_1157403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].length) (baseStart_1157403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157403 prefixEnd_1157403 := by exact prefixLift 1157403
  have htrace : WordTrace (prefixWord ++ tailWord_1157403) baseStart_1157403 baseEnd_1157403 := by
    simpa [prefixWord, tailWord_1157403, baseEnd_1157403] using wordTrace_append hprefix tailTrace_1157403
  have hstable : (prefixWord ++ tailWord_1157403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157403).length < 2 ^ (prefixWord ++ tailWord_1157403).sum := by decide
  have hdescent : baseEnd_1157403 < baseStart_1157403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157433 : List Nat := [1, 2, 1, 6, 1, 1, 4, 6]
def baseStart_1157433 : Nat := 118140960795 + 1157433 * 2 ^ 59
def prefixEnd_1157433 : Nat := 4983230072969 + 3 ^ 40 * 1157433 * 2
def baseEnd_1157433 : Nat := 44023663287072242352931

theorem tailTrace_1157433 : CollatzResearch.WordTrace tailWord_1157433 prefixEnd_1157433 44023663287072242352931 := by
  unfold tailWord_1157433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42215049615825389663892953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28143366410550259775928635 42215049615825389663892953)
  ·
    refine ⟨31661287211869042247919715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42215049615825389663892953 31661287211869042247919715)
    ·
      refine ⟨47491930817803563371879573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31661287211869042247919715 47491930817803563371879573)
      ·
        refine ⟨2226184257084542033056855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47491930817803563371879573 2226184257084542033056855)
        ·
          refine ⟨3339276385626813049585283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226184257084542033056855 3339276385626813049585283)
          ·
            refine ⟨5008914578440219574377925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339276385626813049585283 5008914578440219574377925)
            ·
              refine ⟨939171483457541170195861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5008914578440219574377925 939171483457541170195861)
              ·
                refine ⟨44023663287072242352931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 939171483457541170195861 44023663287072242352931)
                ·
                  rfl

theorem cell22_1157433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 6].length) (baseStart_1157433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157433 prefixEnd_1157433 := by exact prefixLift 1157433
  have htrace : WordTrace (prefixWord ++ tailWord_1157433) baseStart_1157433 baseEnd_1157433 := by
    simpa [prefixWord, tailWord_1157433, baseEnd_1157433] using wordTrace_append hprefix tailTrace_1157433
  have hstable : (prefixWord ++ tailWord_1157433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157433).length < 2 ^ (prefixWord ++ tailWord_1157433).sum := by decide
  have hdescent : baseEnd_1157433 < baseStart_1157433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157476 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1157476 : Nat := 118140960795 + 1157476 * 2 ^ 59
def prefixEnd_1157476 : Nat := 4983230072969 + 3 ^ 40 * 1157476 * 2
def baseEnd_1157476 : Nat := 396227689362412402351247

theorem tailTrace_1157476 : CollatzResearch.WordTrace tailWord_1157476 prefixEnd_1157476 396227689362412402351247 := by
  unfold tailWord_1157476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21108308977334804003854141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28144411969779738671805521 21108308977334804003854141)
  ·
    refine ⟨7915615866500551501445303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21108308977334804003854141 7915615866500551501445303)
    ·
      refine ⟨11873423799750827252167955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7915615866500551501445303 11873423799750827252167955)
      ·
        refine ⟨17810135699626240878251933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11873423799750827252167955 17810135699626240878251933)
        ·
          refine ⟨6678800887359840329344475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17810135699626240878251933 6678800887359840329344475)
          ·
            refine ⟨10018201331039760494016713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6678800887359840329344475 10018201331039760494016713)
            ·
              refine ⟨7513650998279820370512535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10018201331039760494016713 7513650998279820370512535)
              ·
                refine ⟨11270476497419730555768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513650998279820370512535 11270476497419730555768803)
                ·
                  refine ⟨16905714746129595833653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11270476497419730555768803 16905714746129595833653205)
                  ·
                    refine ⟨396227689362412402351247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16905714746129595833653205 396227689362412402351247)
                    ·
                      rfl

theorem cell22_1157476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1157476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157476 prefixEnd_1157476 := by exact prefixLift 1157476
  have htrace : WordTrace (prefixWord ++ tailWord_1157476) baseStart_1157476 baseEnd_1157476 := by
    simpa [prefixWord, tailWord_1157476, baseEnd_1157476] using wordTrace_append hprefix tailTrace_1157476
  have hstable : (prefixWord ++ tailWord_1157476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157476).length < 2 ^ (prefixWord ++ tailWord_1157476).sum := by decide
  have hdescent : baseEnd_1157476 < baseStart_1157476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157491 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_1157491 : Nat := 118140960795 + 1157491 * 2 ^ 59
def prefixEnd_1157491 : Nat := 4983230072969 + 3 ^ 40 * 1157491 * 2
def baseEnd_1157491 : Nat := 396232824168957363226201

theorem tailTrace_1157491 : CollatzResearch.WordTrace tailWord_1157491 prefixEnd_1157491 396232824168957363226201 := by
  unfold tailWord_1157491
  simp only [CollatzResearch.WordTrace]
  refine ⟨42217165049615265569504327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28144776699743510379669551 42217165049615265569504327)
  ·
    refine ⟨63325747574422898354256491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42217165049615265569504327 63325747574422898354256491)
    ·
      refine ⟨94988621361634347531384737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63325747574422898354256491 94988621361634347531384737)
      ·
        refine ⟨71241466021225760648538553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94988621361634347531384737 71241466021225760648538553)
        ·
          refine ⟨53431099515919320486403915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71241466021225760648538553 53431099515919320486403915)
          ·
            refine ⟨80146649273878980729605873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53431099515919320486403915 80146649273878980729605873)
            ·
              refine ⟨60109986955409235547204405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80146649273878980729605873 60109986955409235547204405)
              ·
                refine ⟨5635311277069615832550413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60109986955409235547204405 5635311277069615832550413)
                ·
                  refine ⟨2113241728901105937206405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5635311277069615832550413 2113241728901105937206405)
                  ·
                    refine ⟨396232824168957363226201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113241728901105937206405 396232824168957363226201)
                    ·
                      rfl

theorem cell22_1157491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_1157491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157491 prefixEnd_1157491 := by exact prefixLift 1157491
  have htrace : WordTrace (prefixWord ++ tailWord_1157491) baseStart_1157491 baseEnd_1157491 := by
    simpa [prefixWord, tailWord_1157491, baseEnd_1157491] using wordTrace_append hprefix tailTrace_1157491
  have hstable : (prefixWord ++ tailWord_1157491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157491).length < 2 ^ (prefixWord ++ tailWord_1157491).sum := by decide
  have hdescent : baseEnd_1157491 < baseStart_1157491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157553 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1157553 : Nat := 118140960795 + 1157553 * 2 ^ 59
def prefixEnd_1157553 : Nat := 4983230072969 + 3 ^ 40 * 1157553 * 2
def baseEnd_1157553 : Nat := 396254048036009868176011

theorem tailTrace_1157553 : CollatzResearch.WordTrace tailWord_1157553 prefixEnd_1157553 396254048036009868176011 := by
  unfold tailWord_1157553
  simp only [CollatzResearch.WordTrace]
  refine ⟨42219426375390650158261313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28146284250260433438840875 42219426375390650158261313)
  ·
    refine ⟨31664569781542987618695985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42219426375390650158261313 31664569781542987618695985)
    ·
      refine ⟨23748427336157240714021989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31664569781542987618695985 23748427336157240714021989)
      ·
        refine ⟨4452830125529482633879123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23748427336157240714021989 4452830125529482633879123)
        ·
          refine ⟨6679245188294223950818685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4452830125529482633879123 6679245188294223950818685)
          ·
            refine ⟨2504716945610333981557007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6679245188294223950818685 2504716945610333981557007)
            ·
              refine ⟨3757075418415500972335511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504716945610333981557007 3757075418415500972335511)
              ·
                refine ⟨5635613127623251458503267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757075418415500972335511 5635613127623251458503267)
                ·
                  refine ⟨8453419691434877187754901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5635613127623251458503267 8453419691434877187754901)
                  ·
                    refine ⟨396254048036009868176011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8453419691434877187754901 396254048036009868176011)
                    ·
                      rfl

theorem cell22_1157553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1157553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157553 prefixEnd_1157553 := by exact prefixLift 1157553
  have htrace : WordTrace (prefixWord ++ tailWord_1157553) baseStart_1157553 baseEnd_1157553 := by
    simpa [prefixWord, tailWord_1157553, baseEnd_1157553] using wordTrace_append hprefix tailTrace_1157553
  have hstable : (prefixWord ++ tailWord_1157553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157553).length < 2 ^ (prefixWord ++ tailWord_1157553).sum := by decide
  have hdescent : baseEnd_1157553 < baseStart_1157553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157557 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 4]
def baseStart_1157557 : Nat := 118140960795 + 1157557 * 2 ^ 59
def prefixEnd_1157557 : Nat := 4983230072969 + 3 ^ 40 * 1157557 * 2
def baseEnd_1157557 : Nat := 132085139105918397025333

theorem tailTrace_1157557 : CollatzResearch.WordTrace tailWord_1157557 prefixEnd_1157557 132085139105918397025333 := by
  unfold tailWord_1157557
  simp only [CollatzResearch.WordTrace]
  refine ⟨42219572267376158841406925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28146381511584105894271283 42219572267376158841406925)
  ·
    refine ⟨15832339600266059565527597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42219572267376158841406925 15832339600266059565527597)
    ·
      refine ⟨5937127350099772337072849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15832339600266059565527597 5937127350099772337072849)
      ·
        refine ⟨4452845512574829252804637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5937127350099772337072849 4452845512574829252804637)
        ·
          refine ⟨1669817067215560969801739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4452845512574829252804637 1669817067215560969801739)
          ·
            refine ⟨2504725600823341454702609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669817067215560969801739 2504725600823341454702609)
            ·
              refine ⟨1878544200617506091026957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504725600823341454702609 1878544200617506091026957)
              ·
                refine ⟨704454075231564784135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878544200617506091026957 704454075231564784135109)
                ·
                  refine ⟨132085139105918397025333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704454075231564784135109 132085139105918397025333)
                  ·
                    rfl

theorem cell22_1157557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_1157557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157557 prefixEnd_1157557 := by exact prefixLift 1157557
  have htrace : WordTrace (prefixWord ++ tailWord_1157557) baseStart_1157557 baseEnd_1157557 := by
    simpa [prefixWord, tailWord_1157557, baseEnd_1157557] using wordTrace_append hprefix tailTrace_1157557
  have hstable : (prefixWord ++ tailWord_1157557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157557).length < 2 ^ (prefixWord ++ tailWord_1157557).sum := by decide
  have hdescent : baseEnd_1157557 < baseStart_1157557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157572 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1157572 : Nat := 118140960795 + 1157572 * 2 ^ 59
def prefixEnd_1157572 : Nat := 4983230072969 + 3 ^ 40 * 1157572 * 2
def baseEnd_1157572 : Nat := 396260552124300151950953

theorem tailTrace_1157572 : CollatzResearch.WordTrace tailWord_1157572 prefixEnd_1157572 396260552124300151950953 := by
  unfold tailWord_1157572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21110059681160908201601485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28146746241547877602135313 21110059681160908201601485)
  ·
    refine ⟨7916272380435340575600557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21110059681160908201601485 7916272380435340575600557)
    ·
      refine ⟨2968602142663252715850209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7916272380435340575600557 2968602142663252715850209)
      ·
        refine ⟨2226451606997439536887657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2968602142663252715850209 2226451606997439536887657)
        ·
          refine ⟨1669838705248079652665743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2226451606997439536887657 1669838705248079652665743)
          ·
            refine ⟨2504758057872119478998615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669838705248079652665743 2504758057872119478998615)
            ·
              refine ⟨3757137086808179218497923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504758057872119478998615 3757137086808179218497923)
              ·
                refine ⟨5635705630212268827746885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757137086808179218497923 5635705630212268827746885)
                ·
                  refine ⟨1056694805664800405202541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5635705630212268827746885 1056694805664800405202541)
                  ·
                    refine ⟨396260552124300151950953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056694805664800405202541 396260552124300151950953)
                    ·
                      rfl

theorem cell22_1157572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1157572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157572 prefixEnd_1157572 := by exact prefixLift 1157572
  have htrace : WordTrace (prefixWord ++ tailWord_1157572) baseStart_1157572 baseEnd_1157572 := by
    simpa [prefixWord, tailWord_1157572, baseEnd_1157572] using wordTrace_append hprefix tailTrace_1157572
  have hstable : (prefixWord ++ tailWord_1157572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157572).length < 2 ^ (prefixWord ++ tailWord_1157572).sum := by decide
  have hdescent : baseEnd_1157572 < baseStart_1157572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157602 : List Nat := [3, 3, 3, 2, 1, 1, 1, 8]
def baseStart_1157602 : Nat := 118140960795 + 1157602 * 2 ^ 59
def prefixEnd_1157602 : Nat := 4983230072969 + 3 ^ 40 * 1157602 * 2
def baseEnd_1157602 : Nat := 44030091304154452633429

theorem tailTrace_1157602 : CollatzResearch.WordTrace tailWord_1157602 prefixEnd_1157602 44030091304154452633429 := by
  unfold tailWord_1157602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555303388053282881698765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28147475701475421017863373 10555303388053282881698765)
  ·
    refine ⟨3958238770519981080637037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10555303388053282881698765 3958238770519981080637037)
    ·
      refine ⟨1484339538944992905238889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3958238770519981080637037 1484339538944992905238889)
      ·
        refine ⟨1113254654208744678929167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484339538944992905238889 1113254654208744678929167)
        ·
          refine ⟨1669881981313117018393751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113254654208744678929167 1669881981313117018393751)
          ·
            refine ⟨2504822971969675527590627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669881981313117018393751 2504822971969675527590627)
            ·
              refine ⟨3757234457954513291385941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504822971969675527590627 3757234457954513291385941)
              ·
                refine ⟨44030091304154452633429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3757234457954513291385941 44030091304154452633429)
                ·
                  rfl

theorem cell22_1157602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_1157602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157602 prefixEnd_1157602 := by exact prefixLift 1157602
  have htrace : WordTrace (prefixWord ++ tailWord_1157602) baseStart_1157602 baseEnd_1157602 := by
    simpa [prefixWord, tailWord_1157602, baseEnd_1157602] using wordTrace_append hprefix tailTrace_1157602
  have hstable : (prefixWord ++ tailWord_1157602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157602).length < 2 ^ (prefixWord ++ tailWord_1157602).sum := by decide
  have hdescent : baseEnd_1157602 < baseStart_1157602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157658 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_1157658 : Nat := 118140960795 + 1157658 * 2 ^ 59
def prefixEnd_1157658 : Nat := 4983230072969 + 3 ^ 40 * 1157658 * 2
def baseEnd_1157658 : Nat := 132096663893941531433563

theorem tailTrace_1157658 : CollatzResearch.WordTrace tailWord_1157658 prefixEnd_1157658 132096663893941531433563 := by
  unfold tailWord_1157658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10555814010002563272708407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28148837360006835393889085 10555814010002563272708407)
  ·
    refine ⟨15833721015003844909062611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10555814010002563272708407 15833721015003844909062611)
    ·
      refine ⟨23750581522505767363593917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15833721015003844909062611 23750581522505767363593917)
      ·
        refine ⟨8906468070939662761347719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23750581522505767363593917 8906468070939662761347719)
        ·
          refine ⟨13359702106409494142021579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8906468070939662761347719 13359702106409494142021579)
          ·
            refine ⟨20039553159614241213032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13359702106409494142021579 20039553159614241213032369)
            ·
              refine ⟨15029664869710680909774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20039553159614241213032369 15029664869710680909774277)
              ·
                refine ⟨2818062163070752670582677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15029664869710680909774277 2818062163070752670582677)
                ·
                  refine ⟨132096663893941531433563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2818062163070752670582677 132096663893941531433563)
                  ·
                    rfl

theorem cell22_1157658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_1157658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157658 prefixEnd_1157658 := by exact prefixLift 1157658
  have htrace : WordTrace (prefixWord ++ tailWord_1157658) baseStart_1157658 baseEnd_1157658 := by
    simpa [prefixWord, tailWord_1157658, baseEnd_1157658] using wordTrace_append hprefix tailTrace_1157658
  have hstable : (prefixWord ++ tailWord_1157658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157658).length < 2 ^ (prefixWord ++ tailWord_1157658).sum := by decide
  have hdescent : baseEnd_1157658 < baseStart_1157658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157660 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1157660 : Nat := 118140960795 + 1157660 * 2 ^ 59
def prefixEnd_1157660 : Nat := 4983230072969 + 3 ^ 40 * 1157660 * 2
def baseEnd_1157660 : Nat := 396290676322697255750683

theorem tailTrace_1157660 : CollatzResearch.WordTrace tailWord_1157660 prefixEnd_1157660 396290676322697255750683 := by
  unfold tailWord_1157660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21111664493001503716203217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28148885990668671621604289 21111664493001503716203217)
  ·
    refine ⟨15833748369751127787152413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21111664493001503716203217 15833748369751127787152413)
    ·
      refine ⟨5937655638656672920182155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15833748369751127787152413 5937655638656672920182155)
      ·
        refine ⟨8906483457985009380273233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5937655638656672920182155 8906483457985009380273233)
        ·
          refine ⟨6679862593488757035204925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8906483457985009380273233 6679862593488757035204925)
          ·
            refine ⟨2504948472558283888201847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6679862593488757035204925 2504948472558283888201847)
            ·
              refine ⟨3757422708837425832302771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2504948472558283888201847 3757422708837425832302771)
              ·
                refine ⟨5636134063256138748454157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757422708837425832302771 5636134063256138748454157)
                ·
                  refine ⟨2113550273721052030670309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5636134063256138748454157 2113550273721052030670309)
                  ·
                    refine ⟨396290676322697255750683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113550273721052030670309 396290676322697255750683)
                    ·
                      rfl

theorem cell22_1157660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1157660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157660 prefixEnd_1157660 := by exact prefixLift 1157660
  have htrace : WordTrace (prefixWord ++ tailWord_1157660) baseStart_1157660 baseEnd_1157660 := by
    simpa [prefixWord, tailWord_1157660, baseEnd_1157660] using wordTrace_append hprefix tailTrace_1157660
  have hstable : (prefixWord ++ tailWord_1157660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157660).length < 2 ^ (prefixWord ++ tailWord_1157660).sum := by decide
  have hdescent : baseEnd_1157660 < baseStart_1157660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157692 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_1157692 : Nat := 118140960795 + 1157692 * 2 ^ 59
def prefixEnd_1157692 : Nat := 4983230072969 + 3 ^ 40 * 1157692 * 2
def baseEnd_1157692 : Nat := 132100543525553279650195

theorem tailTrace_1157692 : CollatzResearch.WordTrace tailWord_1157692 prefixEnd_1157692 132100543525553279650195 := by
  unfold tailWord_1157692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21112248060943538448785665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28149664081258051265047553 21112248060943538448785665)
  ·
    refine ⟨15834186045707653836589249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21112248060943538448785665 15834186045707653836589249)
    ·
      refine ⟨11875639534280740377441937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15834186045707653836589249 11875639534280740377441937)
      ·
        refine ⟨8906729650710555283081453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11875639534280740377441937 8906729650710555283081453)
        ·
          refine ⟨3340023619016458231155545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8906729650710555283081453 3340023619016458231155545)
          ·
            refine ⟨2505017714262343673366659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3340023619016458231155545 2505017714262343673366659)
            ·
              refine ⟨3757526571393515510049989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505017714262343673366659 3757526571393515510049989)
              ·
                refine ⟨704536232136284158134373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3757526571393515510049989 704536232136284158134373)
                ·
                  refine ⟨132100543525553279650195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704536232136284158134373 132100543525553279650195)
                  ·
                    rfl

theorem cell22_1157692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_1157692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157692 prefixEnd_1157692 := by exact prefixLift 1157692
  have htrace : WordTrace (prefixWord ++ tailWord_1157692) baseStart_1157692 baseEnd_1157692 := by
    simpa [prefixWord, tailWord_1157692, baseEnd_1157692] using wordTrace_append hprefix tailTrace_1157692
  have hstable : (prefixWord ++ tailWord_1157692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157692).length < 2 ^ (prefixWord ++ tailWord_1157692).sum := by decide
  have hdescent : baseEnd_1157692 < baseStart_1157692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157735 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1157735 : Nat := 118140960795 + 1157735 * 2 ^ 59
def prefixEnd_1157735 : Nat := 4983230072969 + 3 ^ 40 * 1157735 * 2
def baseEnd_1157735 : Nat := 396316350355422060125453

theorem tailTrace_1157735 : CollatzResearch.WordTrace tailWord_1157735 prefixEnd_1157735 396316350355422060125453 := by
  unfold tailWord_1157735
  simp only [CollatzResearch.WordTrace]
  refine ⟨42226064460731295241386659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28150709640487530160924439 42226064460731295241386659)
  ·
    refine ⟨63339096691096942862079989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42226064460731295241386659 63339096691096942862079989)
    ·
      refine ⟨5938040314790338393319999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63339096691096942862079989 5938040314790338393319999)
      ·
        refine ⟨8907060472185507589979999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5938040314790338393319999 8907060472185507589979999)
        ·
          refine ⟨13360590708278261384969999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907060472185507589979999 13360590708278261384969999)
          ·
            refine ⟨20040886062417392077454999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13360590708278261384969999 20040886062417392077454999)
            ·
              refine ⟨30061329093626088116182499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20040886062417392077454999 30061329093626088116182499)
              ·
                refine ⟨45091993640439132174273749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30061329093626088116182499 45091993640439132174273749)
                ·
                  refine ⟨1056843600947792160334541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45091993640439132174273749 1056843600947792160334541)
                  ·
                    refine ⟨396316350355422060125453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056843600947792160334541 396316350355422060125453)
                    ·
                      rfl

theorem cell22_1157735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1157735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157735 prefixEnd_1157735 := by exact prefixLift 1157735
  have htrace : WordTrace (prefixWord ++ tailWord_1157735) baseStart_1157735 baseEnd_1157735 := by
    simpa [prefixWord, tailWord_1157735, baseEnd_1157735] using wordTrace_append hprefix tailTrace_1157735
  have hstable : (prefixWord ++ tailWord_1157735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157735).length < 2 ^ (prefixWord ++ tailWord_1157735).sum := by decide
  have hdescent : baseEnd_1157735 < baseStart_1157735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157857 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1157857 : Nat := 118140960795 + 1157857 * 2 ^ 59
def prefixEnd_1157857 : Nat := 4983230072969 + 3 ^ 40 * 1157857 * 2
def baseEnd_1157857 : Nat := 396358113448654408575079

theorem tailTrace_1157857 : CollatzResearch.WordTrace tailWord_1157857 prefixEnd_1157857 396358113448654408575079 := by
  unfold tailWord_1157857
  simp only [CollatzResearch.WordTrace]
  refine ⟨42230514166289310077327825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28153676110859540051551883 42230514166289310077327825)
  ·
    refine ⟨31672885624716982557995869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42230514166289310077327825 31672885624716982557995869)
    ·
      refine ⟨11877332109268868459248451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31672885624716982557995869 11877332109268868459248451)
      ·
        refine ⟨17815998163903302688872677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11877332109268868459248451 17815998163903302688872677)
        ·
          refine ⟨3340499655731869254163627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17815998163903302688872677 3340499655731869254163627)
          ·
            refine ⟨5010749483597803881245441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340499655731869254163627 5010749483597803881245441)
            ·
              refine ⟨3758062112698352910934081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5010749483597803881245441 3758062112698352910934081)
              ·
                refine ⟨2818546584523764683200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3758062112698352910934081 2818546584523764683200561)
                ·
                  refine ⟨2113909938392823512400421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2818546584523764683200561 2113909938392823512400421)
                  ·
                    refine ⟨396358113448654408575079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113909938392823512400421 396358113448654408575079)
                    ·
                      rfl

theorem cell22_1157857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1157857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157857 prefixEnd_1157857 := by exact prefixLift 1157857
  have htrace : WordTrace (prefixWord ++ tailWord_1157857) baseStart_1157857 baseEnd_1157857 := by
    simpa [prefixWord, tailWord_1157857, baseEnd_1157857] using wordTrace_append hprefix tailTrace_1157857
  have hstable : (prefixWord ++ tailWord_1157857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157857).length < 2 ^ (prefixWord ++ tailWord_1157857).sum := by decide
  have hdescent : baseEnd_1157857 < baseStart_1157857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157859 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 2, 3]
def baseStart_1157859 : Nat := 118140960795 + 1157859 * 2 ^ 59
def prefixEnd_1157859 : Nat := 4983230072969 + 3 ^ 40 * 1157859 * 2
def baseEnd_1157859 : Nat := 396358798089527070025073

theorem tailTrace_1157859 : CollatzResearch.WordTrace tailWord_1157859 prefixEnd_1157859 396358798089527070025073 := by
  unfold tailWord_1157859
  simp only [CollatzResearch.WordTrace]
  refine ⟨42230587112282064418900631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28153724741521376279267087 42230587112282064418900631)
  ·
    refine ⟨63345880668423096628350947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42230587112282064418900631 63345880668423096628350947)
    ·
      refine ⟨95018821002634644942526421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63345880668423096628350947 95018821002634644942526421)
      ·
        refine ⟨2227003617249249490840463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 95018821002634644942526421 2227003617249249490840463)
        ·
          refine ⟨3340505425873874236260695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227003617249249490840463 3340505425873874236260695)
          ·
            refine ⟨5010758138810811354391043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340505425873874236260695 5010758138810811354391043)
            ·
              refine ⟨7516137208216217031586565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010758138810811354391043 7516137208216217031586565)
              ·
                refine ⟨1409275726540540693422481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7516137208216217031586565 1409275726540540693422481)
                ·
                  refine ⟨1056956794905405520066861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409275726540540693422481 1056956794905405520066861)
                  ·
                    refine ⟨396358798089527070025073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056956794905405520066861 396358798089527070025073)
                    ·
                      rfl

theorem cell22_1157859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].length) (baseStart_1157859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157859 prefixEnd_1157859 := by exact prefixLift 1157859
  have htrace : WordTrace (prefixWord ++ tailWord_1157859) baseStart_1157859 baseEnd_1157859 := by
    simpa [prefixWord, tailWord_1157859, baseEnd_1157859] using wordTrace_append hprefix tailTrace_1157859
  have hstable : (prefixWord ++ tailWord_1157859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157859).length < 2 ^ (prefixWord ++ tailWord_1157859).sum := by decide
  have hdescent : baseEnd_1157859 < baseStart_1157859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157861 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 4]
def baseStart_1157861 : Nat := 118140960795 + 1157861 * 2 ^ 59
def prefixEnd_1157861 : Nat := 4983230072969 + 3 ^ 40 * 1157861 * 2
def baseEnd_1157861 : Nat := 132119827576799910491689

theorem tailTrace_1157861 : CollatzResearch.WordTrace tailWord_1157861 prefixEnd_1157861 132119827576799910491689 := by
  unfold tailWord_1157861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42230660058274818760473437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28153773372183212506982291 42230660058274818760473437)
  ·
    refine ⟨15836497521853057035177539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42230660058274818760473437 15836497521853057035177539)
    ·
      refine ⟨23754746282779585552766309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15836497521853057035177539 23754746282779585552766309)
      ·
        refine ⟨4454014928021172291143683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23754746282779585552766309 4454014928021172291143683)
        ·
          refine ⟨6681022392031758436715525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454014928021172291143683 6681022392031758436715525)
          ·
            refine ⟨1252691698505954706884161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6681022392031758436715525 1252691698505954706884161)
            ·
              refine ⟨939518773879466030163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252691698505954706884161 939518773879466030163121)
              ·
                refine ⟨704639080409599522622341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939518773879466030163121 704639080409599522622341)
                ·
                  refine ⟨132119827576799910491689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704639080409599522622341 132119827576799910491689)
                  ·
                    rfl

theorem cell22_1157861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_1157861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157861 prefixEnd_1157861 := by exact prefixLift 1157861
  have htrace : WordTrace (prefixWord ++ tailWord_1157861) baseStart_1157861 baseEnd_1157861 := by
    simpa [prefixWord, tailWord_1157861, baseEnd_1157861] using wordTrace_append hprefix tailTrace_1157861
  have hstable : (prefixWord ++ tailWord_1157861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157861).length < 2 ^ (prefixWord ++ tailWord_1157861).sum := by decide
  have hdescent : baseEnd_1157861 < baseStart_1157861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157885 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1157885 : Nat := 118140960795 + 1157885 * 2 ^ 59
def prefixEnd_1157885 : Nat := 4983230072969 + 3 ^ 40 * 1157885 * 2
def baseEnd_1157885 : Nat := 396367698420871668874993

theorem tailTrace_1157885 : CollatzResearch.WordTrace tailWord_1157885 prefixEnd_1157885 396367698420871668874993 := by
  unfold tailWord_1157885
  simp only [CollatzResearch.WordTrace]
  refine ⟨42231535410187870859347109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28154356940125247239564739 42231535410187870859347109)
  ·
    refine ⟨7918412889410225786127583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42231535410187870859347109 7918412889410225786127583)
    ·
      refine ⟨11877619334115338679191375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918412889410225786127583 11877619334115338679191375)
      ·
        refine ⟨17816429001173008018787063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11877619334115338679191375 17816429001173008018787063)
        ·
          refine ⟨26724643501759512028180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17816429001173008018787063 26724643501759512028180595)
          ·
            refine ⟨40086965252639268042270893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26724643501759512028180595 40086965252639268042270893)
            ·
              refine ⟨15032611969739725515851585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40086965252639268042270893 15032611969739725515851585)
              ·
                refine ⟨11274458977304794136888689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15032611969739725515851585 11274458977304794136888689)
                ·
                  refine ⟨8455844232978595602666517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11274458977304794136888689 8455844232978595602666517)
                  ·
                    refine ⟨396367698420871668874993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8455844232978595602666517 396367698420871668874993)
                    ·
                      rfl

theorem cell22_1157885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1157885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157885 prefixEnd_1157885 := by exact prefixLift 1157885
  have htrace : WordTrace (prefixWord ++ tailWord_1157885) baseStart_1157885 baseEnd_1157885 := by
    simpa [prefixWord, tailWord_1157885, baseEnd_1157885] using wordTrace_append hprefix tailTrace_1157885
  have hstable : (prefixWord ++ tailWord_1157885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157885).length < 2 ^ (prefixWord ++ tailWord_1157885).sum := by decide
  have hdescent : baseEnd_1157885 < baseStart_1157885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157900 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1157900 : Nat := 118140960795 + 1157900 * 2 ^ 59
def prefixEnd_1157900 : Nat := 4983230072969 + 3 ^ 40 * 1157900 * 2
def baseEnd_1157900 : Nat := 132124277742472209916649

theorem tailTrace_1157900 : CollatzResearch.WordTrace tailWord_1157900 prefixEnd_1157900 132124277742472209916649 := by
  unfold tailWord_1157900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116041252566764210571577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28154721670089018947428769 21116041252566764210571577)
  ·
    refine ⟨15837030939425073157928683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21116041252566764210571577 15837030939425073157928683)
    ·
      refine ⟨23755546409137609736893025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15837030939425073157928683 23755546409137609736893025)
      ·
        refine ⟨17816659806853207302669769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23755546409137609736893025 17816659806853207302669769)
        ·
          refine ⟨13362494855139905477002327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17816659806853207302669769 13362494855139905477002327)
          ·
            refine ⟨20043742282709858215503491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13362494855139905477002327 20043742282709858215503491)
            ·
              refine ⟨30065613424064787323255237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20043742282709858215503491 30065613424064787323255237)
              ·
                refine ⟨5637302517012147623110357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30065613424064787323255237 5637302517012147623110357)
                ·
                  refine ⟨132124277742472209916649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5637302517012147623110357 132124277742472209916649)
                  ·
                    rfl

theorem cell22_1157900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1157900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157900 prefixEnd_1157900 := by exact prefixLift 1157900
  have htrace : WordTrace (prefixWord ++ tailWord_1157900) baseStart_1157900 baseEnd_1157900 := by
    simpa [prefixWord, tailWord_1157900, baseEnd_1157900] using wordTrace_append hprefix tailTrace_1157900
  have hstable : (prefixWord ++ tailWord_1157900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157900).length < 2 ^ (prefixWord ++ tailWord_1157900).sum := by decide
  have hdescent : baseEnd_1157900 < baseStart_1157900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157964 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1157964 : Nat := 118140960795 + 1157964 * 2 ^ 59
def prefixEnd_1157964 : Nat := 4983230072969 + 3 ^ 40 * 1157964 * 2
def baseEnd_1157964 : Nat := 396394741735341796149751

theorem tailTrace_1157964 : CollatzResearch.WordTrace tailWord_1157964 prefixEnd_1157964 396394741735341796149751 := by
  unfold tailWord_1157964
  simp only [CollatzResearch.WordTrace]
  refine ⟨21117208388450833675736473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28156277851267778234315297 21117208388450833675736473)
  ·
    refine ⟨15837906291338125256802355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21117208388450833675736473 15837906291338125256802355)
    ·
      refine ⟨23756859437007187885203533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15837906291338125256802355 23756859437007187885203533)
      ·
        refine ⟨8908822288877695456951325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23756859437007187885203533 8908822288877695456951325)
        ·
          refine ⟨3340808358329135796356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8908822288877695456951325 3340808358329135796356747)
          ·
            refine ⟨5011212537493703694535121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340808358329135796356747 5011212537493703694535121)
            ·
              refine ⟨3758409403120277770901341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011212537493703694535121 3758409403120277770901341)
              ·
                refine ⟨1409403526170104164088003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3758409403120277770901341 1409403526170104164088003)
                ·
                  refine ⟨2114105289255156246132005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409403526170104164088003 2114105289255156246132005)
                  ·
                    refine ⟨396394741735341796149751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114105289255156246132005 396394741735341796149751)
                    ·
                      rfl

theorem cell22_1157964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1157964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157964 prefixEnd_1157964 := by exact prefixLift 1157964
  have htrace : WordTrace (prefixWord ++ tailWord_1157964) baseStart_1157964 baseEnd_1157964 := by
    simpa [prefixWord, tailWord_1157964, baseEnd_1157964] using wordTrace_append hprefix tailTrace_1157964
  have hstable : (prefixWord ++ tailWord_1157964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157964).length < 2 ^ (prefixWord ++ tailWord_1157964).sum := by decide
  have hdescent : baseEnd_1157964 < baseStart_1157964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1157998 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1157998 : Nat := 118140960795 + 1157998 * 2 ^ 59
def prefixEnd_1157998 : Nat := 4983230072969 + 3 ^ 40 * 1157998 * 2
def baseEnd_1157998 : Nat := 396406380630177040799647

theorem tailTrace_1157998 : CollatzResearch.WordTrace tailWord_1157998 prefixEnd_1157998 396406380630177040799647 := by
  unfold tailWord_1157998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279457107347311394776331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28157104572518994105473765 5279457107347311394776331)
  ·
    refine ⟨7919185661020967092164497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279457107347311394776331 7919185661020967092164497)
    ·
      refine ⟨5939389245765725319123373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7919185661020967092164497 5939389245765725319123373)
      ·
        refine ⟨2227270967162146994671265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5939389245765725319123373 2227270967162146994671265)
        ·
          refine ⟨1670453225371610246003449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2227270967162146994671265 1670453225371610246003449)
          ·
            refine ⟨1252839919028707684502587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1670453225371610246003449 1252839919028707684502587)
            ·
              refine ⟨1879259878543061526753881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252839919028707684502587 1879259878543061526753881)
              ·
                refine ⟨1409444908907296145065411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879259878543061526753881 1409444908907296145065411)
                ·
                  refine ⟨2114167363360944217598117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409444908907296145065411 2114167363360944217598117)
                  ·
                    refine ⟨396406380630177040799647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114167363360944217598117 396406380630177040799647)
                    ·
                      rfl

theorem cell22_1157998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1157998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1157998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1157998 prefixEnd_1157998 := by exact prefixLift 1157998
  have htrace : WordTrace (prefixWord ++ tailWord_1157998) baseStart_1157998 baseEnd_1157998 := by
    simpa [prefixWord, tailWord_1157998, baseEnd_1157998] using wordTrace_append hprefix tailTrace_1157998
  have hstable : (prefixWord ++ tailWord_1157998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1157998).length < 2 ^ (prefixWord ++ tailWord_1157998).sum := by decide
  have hdescent : baseEnd_1157998 < baseStart_1157998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1157998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158009 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_1158009 : Nat := 118140960795 + 1158009 * 2 ^ 59
def prefixEnd_1158009 : Nat := 4983230072969 + 3 ^ 40 * 1158009 * 2
def baseEnd_1158009 : Nat := 396410146154976678774613

theorem tailTrace_1158009 : CollatzResearch.WordTrace tailWord_1158009 prefixEnd_1158009 396410146154976678774613 := by
  unfold tailWord_1158009
  simp only [CollatzResearch.WordTrace]
  refine ⟨42236058061738640036861081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28157372041159093357907387 42236058061738640036861081)
  ·
    refine ⟨31677043546303980027645811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42236058061738640036861081 31677043546303980027645811)
    ·
      refine ⟨47515565319455970041468717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31677043546303980027645811 47515565319455970041468717)
      ·
        refine ⟨17818336994795988765550769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47515565319455970041468717 17818336994795988765550769)
        ·
          refine ⟨13363752746096991574163077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17818336994795988765550769 13363752746096991574163077)
          ·
            refine ⟨2505703639893185920155577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13363752746096991574163077 2505703639893185920155577)
            ·
              refine ⟨1879277729919889440116683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505703639893185920155577 1879277729919889440116683)
              ·
                refine ⟨2818916594879834160175025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879277729919889440116683 2818916594879834160175025)
                ·
                  refine ⟨2114187446159875620131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2818916594879834160175025 2114187446159875620131269)
                  ·
                    refine ⟨396410146154976678774613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114187446159875620131269 396410146154976678774613)
                    ·
                      rfl

theorem cell22_1158009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_1158009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158009 prefixEnd_1158009 := by exact prefixLift 1158009
  have htrace : WordTrace (prefixWord ++ tailWord_1158009) baseStart_1158009 baseEnd_1158009 := by
    simpa [prefixWord, tailWord_1158009, baseEnd_1158009] using wordTrace_append hprefix tailTrace_1158009
  have hstable : (prefixWord ++ tailWord_1158009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158009).length < 2 ^ (prefixWord ++ tailWord_1158009).sum := by decide
  have hdescent : baseEnd_1158009 < baseStart_1158009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158037 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1158037 : Nat := 118140960795 + 1158037 * 2 ^ 59
def prefixEnd_1158037 : Nat := 4983230072969 + 3 ^ 40 * 1158037 * 2
def baseEnd_1158037 : Nat := 396419731127193939074527

theorem tailTrace_1158037 : CollatzResearch.WordTrace tailWord_1158037 prefixEnd_1158037 396419731127193939074527 := by
  unfold tailWord_1158037
  simp only [CollatzResearch.WordTrace]
  refine ⟨42237079305637200818880365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28158052870424800545920243 42237079305637200818880365)
  ·
    refine ⟨15838904739613950307080137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42237079305637200818880365 15838904739613950307080137)
    ·
      refine ⟨11879178554710462730310103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15838904739613950307080137 11879178554710462730310103)
      ·
        refine ⟨17818767832065694095465155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879178554710462730310103 17818767832065694095465155)
        ·
          refine ⟨26728151748098541143197733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17818767832065694095465155 26728151748098541143197733)
          ·
            refine ⟨5011528452768476464349575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26728151748098541143197733 5011528452768476464349575)
            ·
              refine ⟨7517292679152714696524363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011528452768476464349575 7517292679152714696524363)
              ·
                refine ⟨11275939018729072044786545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517292679152714696524363 11275939018729072044786545)
                ·
                  refine ⟨8456954264046804033589909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11275939018729072044786545 8456954264046804033589909)
                  ·
                    refine ⟨396419731127193939074527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8456954264046804033589909 396419731127193939074527)
                    ·
                      rfl

theorem cell22_1158037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1158037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158037 prefixEnd_1158037 := by exact prefixLift 1158037
  have htrace : WordTrace (prefixWord ++ tailWord_1158037) baseStart_1158037 baseEnd_1158037 := by
    simpa [prefixWord, tailWord_1158037, baseEnd_1158037] using wordTrace_append hprefix tailTrace_1158037
  have hstable : (prefixWord ++ tailWord_1158037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158037).length < 2 ^ (prefixWord ++ tailWord_1158037).sum := by decide
  have hdescent : baseEnd_1158037 < baseStart_1158037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158039 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 3, 3]
def baseStart_1158039 : Nat := 118140960795 + 1158039 * 2 ^ 59
def prefixEnd_1158039 : Nat := 4983230072969 + 3 ^ 40 * 1158039 * 2
def baseEnd_1158039 : Nat := 396420415768066600524521

theorem tailTrace_1158039 : CollatzResearch.WordTrace tailWord_1158039 prefixEnd_1158039 396420415768066600524521 := by
  unfold tailWord_1158039
  simp only [CollatzResearch.WordTrace]
  refine ⟨42237152251629955160453171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28158101501086636773635447 42237152251629955160453171)
  ·
    refine ⟨63355728377444932740679757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42237152251629955160453171 63355728377444932740679757)
    ·
      refine ⟨23758398141541849777754909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63355728377444932740679757 23758398141541849777754909)
      ·
        refine ⟨8909399303078193666658091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23758398141541849777754909 8909399303078193666658091)
        ·
          refine ⟨13364098954617290499987137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8909399303078193666658091 13364098954617290499987137)
          ·
            refine ⟨10023074215962967874990353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13364098954617290499987137 10023074215962967874990353)
            ·
              refine ⟨7517305661972225906242765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023074215962967874990353 7517305661972225906242765)
              ·
                refine ⟨2818989623239584714841037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7517305661972225906242765 2818989623239584714841037)
                ·
                  refine ⟨1057121108714844268065389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2818989623239584714841037 1057121108714844268065389)
                  ·
                    refine ⟨396420415768066600524521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057121108714844268065389 396420415768066600524521)
                    ·
                      rfl

theorem cell22_1158039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_1158039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158039 prefixEnd_1158039 := by exact prefixLift 1158039
  have htrace : WordTrace (prefixWord ++ tailWord_1158039) baseStart_1158039 baseEnd_1158039 := by
    simpa [prefixWord, tailWord_1158039, baseEnd_1158039] using wordTrace_append hprefix tailTrace_1158039
  have hstable : (prefixWord ++ tailWord_1158039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158039).length < 2 ^ (prefixWord ++ tailWord_1158039).sum := by decide
  have hdescent : baseEnd_1158039 < baseStart_1158039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158073 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_1158073 : Nat := 118140960795 + 1158073 * 2 ^ 59
def prefixEnd_1158073 : Nat := 4983230072969 + 3 ^ 40 * 1158073 * 2
def baseEnd_1158073 : Nat := 396432054662901845174417

theorem tailTrace_1158073 : CollatzResearch.WordTrace tailWord_1158073 prefixEnd_1158073 396432054662901845174417 := by
  unfold tailWord_1158073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42238392333506778967190873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28158928222337852644793915 42238392333506778967190873)
  ·
    refine ⟨31678794250130084225393155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42238392333506778967190873 31678794250130084225393155)
    ·
      refine ⟨47518191375195126338089733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31678794250130084225393155 47518191375195126338089733)
      ·
        refine ⟨8909660882849086188391825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47518191375195126338089733 8909660882849086188391825)
        ·
          refine ⟨6682245662136814641293869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8909660882849086188391825 6682245662136814641293869)
          ·
            refine ⟨2505842123301305490485201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6682245662136814641293869 2505842123301305490485201)
            ·
              refine ⟨1879381592475979117863901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2505842123301305490485201 1879381592475979117863901)
              ·
                refine ⟨704768097178492169198963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879381592475979117863901 704768097178492169198963)
                ·
                  refine ⟨1057152145767738253798445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704768097178492169198963 1057152145767738253798445)
                  ·
                    refine ⟨396432054662901845174417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057152145767738253798445 396432054662901845174417)
                    ·
                      rfl

theorem cell22_1158073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_1158073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158073 prefixEnd_1158073 := by exact prefixLift 1158073
  have htrace : WordTrace (prefixWord ++ tailWord_1158073) baseStart_1158073 baseEnd_1158073 := by
    simpa [prefixWord, tailWord_1158073, baseEnd_1158073] using wordTrace_append hprefix tailTrace_1158073
  have hstable : (prefixWord ++ tailWord_1158073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158073).length < 2 ^ (prefixWord ++ tailWord_1158073).sum := by decide
  have hdescent : baseEnd_1158073 < baseStart_1158073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158206 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1158206 : Nat := 118140960795 + 1158206 * 2 ^ 59
def prefixEnd_1158206 : Nat := 4983230072969 + 3 ^ 40 * 1158206 * 2
def baseEnd_1158206 : Nat := 396477583280933831599009

theorem tailTrace_1158206 : CollatzResearch.WordTrace tailWord_1158206 prefixEnd_1158206 396477583280933831599009 := by
  unfold tailWord_1158206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280405405253117835222809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28162162161349961787854981 5280405405253117835222809)
  ·
    refine ⟨3960304053939838376417107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280405405253117835222809 3960304053939838376417107)
    ·
      refine ⟨5940456080909757564625661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3960304053939838376417107 5940456080909757564625661)
      ·
        refine ⟨2227671030341159086734623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5940456080909757564625661 2227671030341159086734623)
        ·
          refine ⟨3341506545511738630101935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227671030341159086734623 3341506545511738630101935)
          ·
            refine ⟨5012259818267607945152903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341506545511738630101935 5012259818267607945152903)
            ·
              refine ⟨7518389727401411917729355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012259818267607945152903 7518389727401411917729355)
              ·
                refine ⟨11277584591102117876594033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7518389727401411917729355 11277584591102117876594033)
                ·
                  refine ⟨8458188443326588407445525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11277584591102117876594033 8458188443326588407445525)
                  ·
                    refine ⟨396477583280933831599009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8458188443326588407445525 396477583280933831599009)
                    ·
                      rfl

theorem cell22_1158206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1158206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158206 prefixEnd_1158206 := by exact prefixLift 1158206
  have htrace : WordTrace (prefixWord ++ tailWord_1158206) baseStart_1158206 baseEnd_1158206 := by
    simpa [prefixWord, tailWord_1158206, baseEnd_1158206] using wordTrace_append hprefix tailTrace_1158206
  have hstable : (prefixWord ++ tailWord_1158206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158206).length < 2 ^ (prefixWord ++ tailWord_1158206).sum := by decide
  have hdescent : baseEnd_1158206 < baseStart_1158206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158208 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_1158208 : Nat := 118140960795 + 1158208 * 2 ^ 59
def prefixEnd_1158208 : Nat := 4983230072969 + 3 ^ 40 * 1158208 * 2
def baseEnd_1158208 : Nat := 396478267921806493049003

theorem tailTrace_1158208 : CollatzResearch.WordTrace tailWord_1158208 prefixEnd_1158208 396478267921806493049003 := by
  unfold tailWord_1158208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21121658094008848511677639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28162210792011798015570185 21121658094008848511677639)
  ·
    refine ⟨31682487141013272767516459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21121658094008848511677639 31682487141013272767516459)
    ·
      refine ⟨47523730711519909151274689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31682487141013272767516459 47523730711519909151274689)
      ·
        refine ⟨35642798033639931863456017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47523730711519909151274689 35642798033639931863456017)
        ·
          refine ⟨26732098525229948897592013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35642798033639931863456017 26732098525229948897592013)
          ·
            refine ⟨10024536946961230836597005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26732098525229948897592013 10024536946961230836597005)
            ·
              refine ⟨3759201355110461563723877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10024536946961230836597005 3759201355110461563723877)
              ·
                refine ⟨704850254083211543198227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3759201355110461563723877 704850254083211543198227)
                ·
                  refine ⟨1057275381124817314797341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704850254083211543198227 1057275381124817314797341)
                  ·
                    refine ⟨396478267921806493049003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057275381124817314797341 396478267921806493049003)
                    ·
                      rfl

theorem cell22_1158208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_1158208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158208 prefixEnd_1158208 := by exact prefixLift 1158208
  have htrace : WordTrace (prefixWord ++ tailWord_1158208) baseStart_1158208 baseEnd_1158208 := by
    simpa [prefixWord, tailWord_1158208, baseEnd_1158208] using wordTrace_append hprefix tailTrace_1158208
  have hstable : (prefixWord ++ tailWord_1158208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158208).length < 2 ^ (prefixWord ++ tailWord_1158208).sum := by decide
  have hdescent : baseEnd_1158208 < baseStart_1158208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158242 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1158242 : Nat := 118140960795 + 1158242 * 2 ^ 59
def prefixEnd_1158242 : Nat := 4983230072969 + 3 ^ 40 * 1158242 * 2
def baseEnd_1158242 : Nat := 396489906816641737698899

theorem tailTrace_1158242 : CollatzResearch.WordTrace tailWord_1158242 prefixEnd_1158242 396489906816641737698899 := by
  unfold tailWord_1158242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561139067473630207523245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28163037513263013886728653 10561139067473630207523245)
  ·
    refine ⟨3960427150302611327821217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10561139067473630207523245 3960427150302611327821217)
    ·
      refine ⟨2970320362726958495865913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960427150302611327821217 2970320362726958495865913)
      ·
        refine ⟨2227740272045218871899435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970320362726958495865913 2227740272045218871899435)
        ·
          refine ⟨3341610408067828307849153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227740272045218871899435 3341610408067828307849153)
          ·
            refine ⟨2506207806050871230886865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3341610408067828307849153 2506207806050871230886865)
            ·
              refine ⟨1879655854538153423165149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506207806050871230886865 1879655854538153423165149)
              ·
                refine ⟨704870945451807533686931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879655854538153423165149 704870945451807533686931)
                ·
                  refine ⟨1057306418177711300530397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704870945451807533686931 1057306418177711300530397)
                  ·
                    refine ⟨396489906816641737698899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057306418177711300530397 396489906816641737698899)
                    ·
                      rfl

theorem cell22_1158242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1158242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158242 prefixEnd_1158242 := by exact prefixLift 1158242
  have htrace : WordTrace (prefixWord ++ tailWord_1158242) baseStart_1158242 baseEnd_1158242 := by
    simpa [prefixWord, tailWord_1158242, baseEnd_1158242] using wordTrace_append hprefix tailTrace_1158242
  have hstable : (prefixWord ++ tailWord_1158242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158242).length < 2 ^ (prefixWord ++ tailWord_1158242).sum := by decide
  have hdescent : baseEnd_1158242 < baseStart_1158242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158264 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1158264 : Nat := 118140960795 + 1158264 * 2 ^ 59
def prefixEnd_1158264 : Nat := 4983230072969 + 3 ^ 40 * 1158264 * 2
def baseEnd_1158264 : Nat := 396497437866241013648831

theorem tailTrace_1158264 : CollatzResearch.WordTrace tailWord_1158264 prefixEnd_1158264 396497437866241013648831 := by
  unfold tailWord_1158264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122679337907409293696923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28163572450543212391595897 21122679337907409293696923)
  ·
    refine ⟨31684019006861113940545385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21122679337907409293696923 31684019006861113940545385)
    ·
      refine ⟨23763014255145835455409039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31684019006861113940545385 23763014255145835455409039)
      ·
        refine ⟨35644521382718753183113559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23763014255145835455409039 35644521382718753183113559)
        ·
          refine ⟨53466782074078129774670339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35644521382718753183113559 53466782074078129774670339)
          ·
            refine ⟨80200173111117194662005509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53466782074078129774670339 80200173111117194662005509)
            ·
              refine ⟨15037532458334473999126033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80200173111117194662005509 15037532458334473999126033)
              ·
                refine ⟨11278149343750855499344525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15037532458334473999126033 11278149343750855499344525)
                ·
                  refine ⟨4229306003906570812254197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11278149343750855499344525 4229306003906570812254197)
                  ·
                    refine ⟨396497437866241013648831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4229306003906570812254197 396497437866241013648831)
                    ·
                      rfl

theorem cell22_1158264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1158264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158264 prefixEnd_1158264 := by exact prefixLift 1158264
  have htrace : WordTrace (prefixWord ++ tailWord_1158264) baseStart_1158264 baseEnd_1158264 := by
    simpa [prefixWord, tailWord_1158264, baseEnd_1158264] using wordTrace_append hprefix tailTrace_1158264
  have hstable : (prefixWord ++ tailWord_1158264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158264).length < 2 ^ (prefixWord ++ tailWord_1158264).sum := by decide
  have hdescent : baseEnd_1158264 < baseStart_1158264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158281 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_1158281 : Nat := 118140960795 + 1158281 * 2 ^ 59
def prefixEnd_1158281 : Nat := 4983230072969 + 3 ^ 40 * 1158281 * 2
def baseEnd_1158281 : Nat := 396503257313658635973779

theorem tailTrace_1158281 : CollatzResearch.WordTrace tailWord_1158281 prefixEnd_1158281 396503257313658635973779 := by
  unfold tailWord_1158281
  simp only [CollatzResearch.WordTrace]
  refine ⟨42245978716753230490762697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28163985811168820327175131 42245978716753230490762697)
  ·
    refine ⟨31684484037564922868072023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42245978716753230490762697 31684484037564922868072023)
    ·
      refine ⟨47526726056347384302108035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31684484037564922868072023 47526726056347384302108035)
      ·
        refine ⟨71290089084521076453162053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47526726056347384302108035 71290089084521076453162053)
        ·
          refine ⟨13366891703347701834967885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71290089084521076453162053 13366891703347701834967885)
          ·
            refine ⟨5012584388755388188112957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13366891703347701834967885 5012584388755388188112957)
            ·
              refine ⟨1879719145783270570542359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5012584388755388188112957 1879719145783270570542359)
              ·
                refine ⟨2819578718674905855813539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879719145783270570542359 2819578718674905855813539)
                ·
                  refine ⟨4229368078012358783720309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819578718674905855813539 4229368078012358783720309)
                  ·
                    refine ⟨396503257313658635973779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4229368078012358783720309 396503257313658635973779)
                    ·
                      rfl

theorem cell22_1158281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_1158281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158281 prefixEnd_1158281 := by exact prefixLift 1158281
  have htrace : WordTrace (prefixWord ++ tailWord_1158281) baseStart_1158281 baseEnd_1158281 := by
    simpa [prefixWord, tailWord_1158281, baseEnd_1158281] using wordTrace_append hprefix tailTrace_1158281
  have hstable : (prefixWord ++ tailWord_1158281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158281).length < 2 ^ (prefixWord ++ tailWord_1158281).sum := by decide
  have hdescent : baseEnd_1158281 < baseStart_1158281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158296 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1158296 : Nat := 118140960795 + 1158296 * 2 ^ 59
def prefixEnd_1158296 : Nat := 4983230072969 + 3 ^ 40 * 1158296 * 2
def baseEnd_1158296 : Nat := 396508392120203596848733

theorem tailTrace_1158296 : CollatzResearch.WordTrace tailWord_1158296 prefixEnd_1158296 396508392120203596848733 := by
  unfold tailWord_1158296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123262905849444026279371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28164350541132592035039161 21123262905849444026279371)
  ·
    refine ⟨31684894358774166039419057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21123262905849444026279371 31684894358774166039419057)
    ·
      refine ⟨23763670769080624529564293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31684894358774166039419057 23763670769080624529564293)
      ·
        refine ⟨4455688269202617099293305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23763670769080624529564293 4455688269202617099293305)
        ·
          refine ⟨3341766201901962824469979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455688269202617099293305 3341766201901962824469979)
          ·
            refine ⟨5012649302852944236704969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341766201901962824469979 5012649302852944236704969)
            ·
              refine ⟨3759486977139708177528727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012649302852944236704969 3759486977139708177528727)
              ·
                refine ⟨5639230465709562266293091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759486977139708177528727 5639230465709562266293091)
                ·
                  refine ⟨8458845698564343399439637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639230465709562266293091 8458845698564343399439637)
                  ·
                    refine ⟨396508392120203596848733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8458845698564343399439637 396508392120203596848733)
                    ·
                      rfl

theorem cell22_1158296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1158296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158296 prefixEnd_1158296 := by exact prefixLift 1158296
  have htrace : WordTrace (prefixWord ++ tailWord_1158296) baseStart_1158296 baseEnd_1158296 := by
    simpa [prefixWord, tailWord_1158296, baseEnd_1158296] using wordTrace_append hprefix tailTrace_1158296
  have hstable : (prefixWord ++ tailWord_1158296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158296).length < 2 ^ (prefixWord ++ tailWord_1158296).sum := by decide
  have hdescent : baseEnd_1158296 < baseStart_1158296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158298 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_1158298 : Nat := 118140960795 + 1158298 * 2 ^ 59
def prefixEnd_1158298 : Nat := 4983230072969 + 3 ^ 40 * 1158298 * 2
def baseEnd_1158298 : Nat := 396509076761076258298727

theorem tailTrace_1158298 : CollatzResearch.WordTrace tailWord_1158298 prefixEnd_1158298 396509076761076258298727 := by
  unfold tailWord_1158298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561649689422910598532887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28164399171794428262754365 10561649689422910598532887)
  ·
    refine ⟨15842474534134365897799331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10561649689422910598532887 15842474534134365897799331)
    ·
      refine ⟨23763711801201548846698997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15842474534134365897799331 23763711801201548846698997)
      ·
        refine ⟨2227847981362645204378031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23763711801201548846698997 2227847981362645204378031)
        ·
          refine ⟨3341771972043967806567047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227847981362645204378031 3341771972043967806567047)
          ·
            refine ⟨5012657958065951709850571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341771972043967806567047 5012657958065951709850571)
            ·
              refine ⟨7518986937098927564775857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012657958065951709850571 7518986937098927564775857)
              ·
                refine ⟨5639240202824195673581893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7518986937098927564775857 5639240202824195673581893)
                ·
                  refine ⟨1057357538029536688796605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5639240202824195673581893 1057357538029536688796605)
                  ·
                    refine ⟨396509076761076258298727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057357538029536688796605 396509076761076258298727)
                    ·
                      rfl

theorem cell22_1158298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_1158298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158298 prefixEnd_1158298 := by exact prefixLift 1158298
  have htrace : WordTrace (prefixWord ++ tailWord_1158298) baseStart_1158298 baseEnd_1158298 := by
    simpa [prefixWord, tailWord_1158298, baseEnd_1158298] using wordTrace_append hprefix tailTrace_1158298
  have hstable : (prefixWord ++ tailWord_1158298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158298).length < 2 ^ (prefixWord ++ tailWord_1158298).sum := by decide
  have hdescent : baseEnd_1158298 < baseStart_1158298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158300 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_1158300 : Nat := 118140960795 + 1158300 * 2 ^ 59
def prefixEnd_1158300 : Nat := 4983230072969 + 3 ^ 40 * 1158300 * 2
def baseEnd_1158300 : Nat := 132169920467316306582907

theorem tailTrace_1158300 : CollatzResearch.WordTrace tailWord_1158300 prefixEnd_1158300 132169920467316306582907 := by
  unfold tailWord_1158300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123335851842198367852177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28164447802456264490469569 21123335851842198367852177)
  ·
    refine ⟨15842501888881648775889133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21123335851842198367852177 15842501888881648775889133)
    ·
      refine ⟨5940938208330618290958425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15842501888881648775889133 5940938208330618290958425)
      ·
        refine ⟨4455703656247963718218819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5940938208330618290958425 4455703656247963718218819)
        ·
          refine ⟨6683555484371945577328229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455703656247963718218819 6683555484371945577328229)
          ·
            refine ⟨1253166653319739795749043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6683555484371945577328229 1253166653319739795749043)
            ·
              refine ⟨1879749979979609693623565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253166653319739795749043 1879749979979609693623565)
              ·
                refine ⟨704906242492353635108837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879749979979609693623565 704906242492353635108837)
                ·
                  refine ⟨132169920467316306582907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704906242492353635108837 132169920467316306582907)
                  ·
                    rfl

theorem cell22_1158300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_1158300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158300 prefixEnd_1158300 := by exact prefixLift 1158300
  have htrace : WordTrace (prefixWord ++ tailWord_1158300) baseStart_1158300 baseEnd_1158300 := by
    simpa [prefixWord, tailWord_1158300, baseEnd_1158300] using wordTrace_append hprefix tailTrace_1158300
  have hstable : (prefixWord ++ tailWord_1158300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158300).length < 2 ^ (prefixWord ++ tailWord_1158300).sum := by decide
  have hdescent : baseEnd_1158300 < baseStart_1158300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158311 : List Nat := [1, 1, 6, 2, 1, 1, 10]
def baseStart_1158311 : Nat := 118140960795 + 1158311 * 2 ^ 59
def prefixEnd_1158311 : Nat := 4983230072969 + 3 ^ 40 * 1158311 * 2
def baseEnd_1158311 : Nat := 14685686182472168804581

theorem tailTrace_1158311 : CollatzResearch.WordTrace tailWord_1158311 prefixEnd_1158311 14685686182472168804581 := by
  unfold tailWord_1158311
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247072906644545614354787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28164715271096363742903191 42247072906644545614354787)
  ·
    refine ⟨63370609359966818421532181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42247072906644545614354787 63370609359966818421532181)
    ·
      refine ⟨2970497313748444613509321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63370609359966818421532181 2970497313748444613509321)
      ·
        refine ⟨2227872985311333460131991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970497313748444613509321 2227872985311333460131991)
        ·
          refine ⟨3341809477967000190197987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227872985311333460131991 3341809477967000190197987)
          ·
            refine ⟨5012714216950500285296981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341809477967000190197987 5012714216950500285296981)
            ·
              refine ⟨14685686182472168804581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5012714216950500285296981 14685686182472168804581)
              ·
                rfl

theorem cell22_1158311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 10].length) (baseStart_1158311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158311 prefixEnd_1158311 := by exact prefixLift 1158311
  have htrace : WordTrace (prefixWord ++ tailWord_1158311) baseStart_1158311 baseEnd_1158311 := by
    simpa [prefixWord, tailWord_1158311, baseEnd_1158311] using wordTrace_append hprefix tailTrace_1158311
  have hstable : (prefixWord ++ tailWord_1158311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158311).length < 2 ^ (prefixWord ++ tailWord_1158311).sum := by decide
  have hdescent : baseEnd_1158311 < baseStart_1158311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158317 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 4]
def baseStart_1158317 : Nat := 118140960795 + 1158317 * 2 ^ 59
def prefixEnd_1158317 : Nat := 4983230072969 + 3 ^ 40 * 1158317 * 2
def baseEnd_1158317 : Nat := 132171860283122180691223

theorem tailTrace_1158317 : CollatzResearch.WordTrace tailWord_1158317 prefixEnd_1158317 132171860283122180691223 := by
  unfold tailWord_1158317
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247291744622808639073205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28164861163081872426048803 42247291744622808639073205)
  ·
    refine ⟨3960683601058388309913113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42247291744622808639073205 3960683601058388309913113)
    ·
      refine ⟨2970512700793791232434835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960683601058388309913113 2970512700793791232434835)
      ·
        refine ⟨4455769051190686848652253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970512700793791232434835 4455769051190686848652253)
        ·
          refine ⟨1670913394196507568244595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4455769051190686848652253 1670913394196507568244595)
          ·
            refine ⟨2506370091294761352366893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670913394196507568244595 2506370091294761352366893)
            ·
              refine ⟨939888784235535507137585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506370091294761352366893 939888784235535507137585)
              ·
                refine ⟨704916588176651630353189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939888784235535507137585 704916588176651630353189)
                ·
                  refine ⟨132171860283122180691223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 704916588176651630353189 132171860283122180691223)
                  ·
                    rfl

theorem cell22_1158317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_1158317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158317 prefixEnd_1158317 := by exact prefixLift 1158317
  have htrace : WordTrace (prefixWord ++ tailWord_1158317) baseStart_1158317 baseEnd_1158317 := by
    simpa [prefixWord, tailWord_1158317, baseEnd_1158317] using wordTrace_append hprefix tailTrace_1158317
  have hstable : (prefixWord ++ tailWord_1158317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158317).length < 2 ^ (prefixWord ++ tailWord_1158317).sum := by decide
  have hdescent : baseEnd_1158317 < baseStart_1158317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158332 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_1158332 : Nat := 118140960795 + 1158332 * 2 ^ 59
def prefixEnd_1158332 : Nat := 4983230072969 + 3 ^ 40 * 1158332 * 2
def baseEnd_1158332 : Nat := 396520715655911502948623

theorem tailTrace_1158332 : CollatzResearch.WordTrace tailWord_1158332 prefixEnd_1158332 396520715655911502948623 := by
  unfold tailWord_1158332
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123919419784233100434625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28165225893045644133912833 21123919419784233100434625)
  ·
    refine ⟨15842939564838174825325969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21123919419784233100434625 15842939564838174825325969)
    ·
      refine ⟨11882204673628631118994477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15842939564838174825325969 11882204673628631118994477)
      ·
        refine ⟨4455826752610736669622929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11882204673628631118994477 4455826752610736669622929)
        ·
          refine ⟨3341870064458052502217197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4455826752610736669622929 3341870064458052502217197)
          ·
            refine ⟨1253201274171769688331449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341870064458052502217197 1253201274171769688331449)
            ·
              refine ⟨939900955628827266248587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253201274171769688331449 939900955628827266248587)
              ·
                refine ⟨1409851433443240899372881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939900955628827266248587 1409851433443240899372881)
                ·
                  refine ⟨1057388575082430674529661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409851433443240899372881 1057388575082430674529661)
                  ·
                    refine ⟨396520715655911502948623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057388575082430674529661 396520715655911502948623)
                    ·
                      rfl

theorem cell22_1158332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_1158332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158332 prefixEnd_1158332 := by exact prefixLift 1158332
  have htrace : WordTrace (prefixWord ++ tailWord_1158332) baseStart_1158332 baseEnd_1158332 := by
    simpa [prefixWord, tailWord_1158332, baseEnd_1158332] using wordTrace_append hprefix tailTrace_1158332
  have hstable : (prefixWord ++ tailWord_1158332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158332).length < 2 ^ (prefixWord ++ tailWord_1158332).sum := by decide
  have hdescent : baseEnd_1158332 < baseStart_1158332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158339 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 9]
def baseStart_1158339 : Nat := 118140960795 + 1158339 * 2 ^ 59
def prefixEnd_1158339 : Nat := 4983230072969 + 3 ^ 40 * 1158339 * 2
def baseEnd_1158339 : Nat := 132174370632988606007867

theorem tailTrace_1158339 : CollatzResearch.WordTrace tailWord_1158339 prefixEnd_1158339 132174370632988606007867 := by
  unfold tailWord_1158339
  simp only [CollatzResearch.WordTrace]
  refine ⟨42248094150543106396374071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28165396100362070930916047 42248094150543106396374071)
  ·
    refine ⟨63372141225814659594561107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42248094150543106396374071 63372141225814659594561107)
    ·
      refine ⟨95058211838721989391841661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63372141225814659594561107 95058211838721989391841661)
      ·
        refine ⟨35646829439520746021940623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95058211838721989391841661 35646829439520746021940623)
        ·
          refine ⟨53470244159281119032910935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35646829439520746021940623 53470244159281119032910935)
          ·
            refine ⟨80205366238921678549366403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53470244159281119032910935 80205366238921678549366403)
            ·
              refine ⟨120308049358382517824049605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80205366238921678549366403 120308049358382517824049605)
              ·
                refine ⟨22557759254696722092009301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120308049358382517824049605 22557759254696722092009301)
                ·
                  refine ⟨132174370632988606007867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22557759254696722092009301 132174370632988606007867)
                  ·
                    rfl

theorem cell22_1158339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_1158339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158339 prefixEnd_1158339 := by exact prefixLift 1158339
  have htrace : WordTrace (prefixWord ++ tailWord_1158339) baseStart_1158339 baseEnd_1158339 := by
    simpa [prefixWord, tailWord_1158339, baseEnd_1158339] using wordTrace_append hprefix tailTrace_1158339
  have hstable : (prefixWord ++ tailWord_1158339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158339).length < 2 ^ (prefixWord ++ tailWord_1158339).sum := by decide
  have hdescent : baseEnd_1158339 < baseStart_1158339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158401 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 8]
def baseStart_1158401 : Nat := 118140960795 + 1158401 * 2 ^ 59
def prefixEnd_1158401 : Nat := 4983230072969 + 3 ^ 40 * 1158401 * 2
def baseEnd_1158401 : Nat := 132181445255339440991137

theorem tailTrace_1158401 : CollatzResearch.WordTrace tailWord_1158401 prefixEnd_1158401 132181445255339440991137 := by
  unfold tailWord_1158401
  simp only [CollatzResearch.WordTrace]
  refine ⟨42250355476318490985131057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28166903650878993990087371 42250355476318490985131057)
  ·
    refine ⟨31687766607238868238848293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42250355476318490985131057 31687766607238868238848293)
    ·
      refine ⟨5941456238857287794784055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31687766607238868238848293 5941456238857287794784055)
      ·
        refine ⟨8912184358285931692176083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941456238857287794784055 8912184358285931692176083)
        ·
          refine ⟨13368276537428897538264125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912184358285931692176083 13368276537428897538264125)
          ·
            refine ⟨5013103701535836576849047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13368276537428897538264125 5013103701535836576849047)
            ·
              refine ⟨7519655552303754865273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013103701535836576849047 7519655552303754865273571)
              ·
                refine ⟨11279483328455632297910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7519655552303754865273571 11279483328455632297910357)
                ·
                  refine ⟨132181445255339440991137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11279483328455632297910357 132181445255339440991137)
                  ·
                    rfl

theorem cell22_1158401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_1158401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158401 prefixEnd_1158401 := by exact prefixLift 1158401
  have htrace : WordTrace (prefixWord ++ tailWord_1158401) baseStart_1158401 baseEnd_1158401 := by
    simpa [prefixWord, tailWord_1158401, baseEnd_1158401] using wordTrace_append hprefix tailTrace_1158401
  have hstable : (prefixWord ++ tailWord_1158401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158401).length < 2 ^ (prefixWord ++ tailWord_1158401).sum := by decide
  have hdescent : baseEnd_1158401 < baseStart_1158401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158450 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1158450 : Nat := 118140960795 + 1158450 * 2 ^ 59
def prefixEnd_1158450 : Nat := 4983230072969 + 3 ^ 40 * 1158450 * 2
def baseEnd_1158450 : Nat := 396561109467398528498261

theorem tailTrace_1158450 : CollatzResearch.WordTrace tailWord_1158450 prefixEnd_1158450 396561109467398528498261 := by
  unfold tailWord_1158450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563035663285243088416201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28168095102093981569109869 10563035663285243088416201)
  ·
    refine ⟨7922276747463932316312151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10563035663285243088416201 7922276747463932316312151)
    ·
      refine ⟨11883415121195898474468227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922276747463932316312151 11883415121195898474468227)
      ·
        refine ⟨17825122681793847711702341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883415121195898474468227 17825122681793847711702341)
        ·
          refine ⟨3342210502836346445944189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17825122681793847711702341 3342210502836346445944189)
          ·
            refine ⟨1253328938563629917229071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3342210502836346445944189 1253328938563629917229071)
            ·
              refine ⟨1879993407845444875843607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253328938563629917229071 1879993407845444875843607)
              ·
                refine ⟨2819990111768167313765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879993407845444875843607 2819990111768167313765411)
                ·
                  refine ⟨4229985167652250970648117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819990111768167313765411 4229985167652250970648117)
                  ·
                    refine ⟨396561109467398528498261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4229985167652250970648117 396561109467398528498261)
                    ·
                      rfl

theorem cell22_1158450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1158450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158450 prefixEnd_1158450 := by exact prefixLift 1158450
  have htrace : WordTrace (prefixWord ++ tailWord_1158450) baseStart_1158450 baseEnd_1158450 := by
    simpa [prefixWord, tailWord_1158450, baseEnd_1158450] using wordTrace_append hprefix tailTrace_1158450
  have hstable : (prefixWord ++ tailWord_1158450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158450).length < 2 ^ (prefixWord ++ tailWord_1158450).sum := by decide
  have hdescent : baseEnd_1158450 < baseStart_1158450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158454 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1158454 : Nat := 118140960795 + 1158454 * 2 ^ 59
def prefixEnd_1158454 : Nat := 4983230072969 + 3 ^ 40 * 1158454 * 2
def baseEnd_1158454 : Nat := 396562478749143851398249

theorem tailTrace_1158454 : CollatzResearch.WordTrace tailWord_1158454 prefixEnd_1158454 396562478749143851398249 := by
  unfold tailWord_1158454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640768034070405064800651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28168192363417654024540277 2640768034070405064800651)
  ·
    refine ⟨3961152051105607597200977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640768034070405064800651 3961152051105607597200977)
    ·
      refine ⟨2970864038329205697900733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3961152051105607597200977 2970864038329205697900733)
      ·
        refine ⟨1114074014373452136712775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2970864038329205697900733 1114074014373452136712775)
        ·
          refine ⟨1671111021560178205069163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114074014373452136712775 1671111021560178205069163)
          ·
            refine ⟨2506666532340267307603745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671111021560178205069163 2506666532340267307603745)
            ·
              refine ⟨1879999899255200480702809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506666532340267307603745 1879999899255200480702809)
              ·
                refine ⟨1409999924441400360527107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879999899255200480702809 1409999924441400360527107)
                ·
                  refine ⟨2114999886662100540790661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409999924441400360527107 2114999886662100540790661)
                  ·
                    refine ⟨396562478749143851398249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2114999886662100540790661 396562478749143851398249)
                    ·
                      rfl

theorem cell22_1158454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1158454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158454 prefixEnd_1158454 := by exact prefixLift 1158454
  have htrace : WordTrace (prefixWord ++ tailWord_1158454) baseStart_1158454 baseEnd_1158454 := by
    simpa [prefixWord, tailWord_1158454, baseEnd_1158454] using wordTrace_append hprefix tailTrace_1158454
  have hstable : (prefixWord ++ tailWord_1158454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158454).length < 2 ^ (prefixWord ++ tailWord_1158454).sum := by decide
  have hdescent : baseEnd_1158454 < baseStart_1158454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158463 : List Nat := [1, 1, 2, 2, 4, 2, 4, 6]
def baseStart_1158463 : Nat := 118140960795 + 1158463 * 2 ^ 59
def prefixEnd_1158463 : Nat := 4983230072969 + 3 ^ 40 * 1158463 * 2
def baseEnd_1158463 : Nat := 44062839959230091991469

theorem tailTrace_1158463 : CollatzResearch.WordTrace tailWord_1158463 prefixEnd_1158463 44062839959230091991469 := by
  unfold tailWord_1158463
  simp only [CollatzResearch.WordTrace]
  refine ⟨42252616802093875573888043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28168411201395917049258695 42252616802093875573888043)
  ·
    refine ⟨63378925203140813360832065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42252616802093875573888043 63378925203140813360832065)
    ·
      refine ⟨47534193902355610020624049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63378925203140813360832065 47534193902355610020624049)
      ·
        refine ⟨35650645426766707515468037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47534193902355610020624049 35650645426766707515468037)
        ·
          refine ⟨6684496017518757659150257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35650645426766707515468037 6684496017518757659150257)
          ·
            refine ⟨5013372013139068244362693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6684496017518757659150257 5013372013139068244362693)
            ·
              refine ⟨940007252463575295818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5013372013139068244362693 940007252463575295818005)
              ·
                refine ⟨44062839959230091991469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 940007252463575295818005 44062839959230091991469)
                ·
                  rfl

theorem cell22_1158463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 6].length) (baseStart_1158463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158463 prefixEnd_1158463 := by exact prefixLift 1158463
  have htrace : WordTrace (prefixWord ++ tailWord_1158463) baseStart_1158463 baseEnd_1158463 := by
    simpa [prefixWord, tailWord_1158463, baseEnd_1158463] using wordTrace_append hprefix tailTrace_1158463
  have hstable : (prefixWord ++ tailWord_1158463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158463).length < 2 ^ (prefixWord ++ tailWord_1158463).sum := by decide
  have hdescent : baseEnd_1158463 < baseStart_1158463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158486 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1158486 : Nat := 118140960795 + 1158486 * 2 ^ 59
def prefixEnd_1158486 : Nat := 4983230072969 + 3 ^ 40 * 1158486 * 2
def baseEnd_1158486 : Nat := 132191144334368811532717

theorem tailTrace_1158486 : CollatzResearch.WordTrace tailWord_1158486 prefixEnd_1158486 132191144334368811532717 := by
  unfold tailWord_1158486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640840980063159406373457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28168970454007033667983541 2640840980063159406373457)
  ·
    refine ⟨1980630735047369554780093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2640840980063159406373457 1980630735047369554780093)
    ·
      refine ⟨742736525642763583042535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1980630735047369554780093 742736525642763583042535)
      ·
        refine ⟨1114104788464145374563803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742736525642763583042535 1114104788464145374563803)
        ·
          refine ⟨1671157182696218061845705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114104788464145374563803 1671157182696218061845705)
          ·
            refine ⟨1253367887022163546384279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1671157182696218061845705 1253367887022163546384279)
            ·
              refine ⟨1880051830533245319576419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253367887022163546384279 1880051830533245319576419)
              ·
                refine ⟨2820077745799867979364629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880051830533245319576419 2820077745799867979364629)
                ·
                  refine ⟨132191144334368811532717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2820077745799867979364629 132191144334368811532717)
                  ·
                    rfl

theorem cell22_1158486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1158486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158486 prefixEnd_1158486 := by exact prefixLift 1158486
  have htrace : WordTrace (prefixWord ++ tailWord_1158486) baseStart_1158486 baseEnd_1158486 := by
    simpa [prefixWord, tailWord_1158486, baseEnd_1158486] using wordTrace_append hprefix tailTrace_1158486
  have hstable : (prefixWord ++ tailWord_1158486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158486).length < 2 ^ (prefixWord ++ tailWord_1158486).sum := by decide
  have hdescent : baseEnd_1158486 < baseStart_1158486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158542 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1158542 : Nat := 118140960795 + 1158542 * 2 ^ 59
def prefixEnd_1158542 : Nat := 4983230072969 + 3 ^ 40 * 1158542 * 2
def baseEnd_1158542 : Nat := 132197534315846985065993

theorem tailTrace_1158542 : CollatzResearch.WordTrace tailWord_1158542 prefixEnd_1158542 132197534315846985065993 := by
  unfold tailWord_1158542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281937271100959008251735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28170332112538448044009253 5281937271100959008251735)
  ·
    refine ⟨7922905906651438512377603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281937271100959008251735 7922905906651438512377603)
    ·
      refine ⟨11884358859977157768566405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922905906651438512377603 11884358859977157768566405)
      ·
        refine ⟨2228317286245717081606201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11884358859977157768566405 2228317286245717081606201)
        ·
          refine ⟨1671237964684287811204651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228317286245717081606201 1671237964684287811204651)
          ·
            refine ⟨2506856947026431716806977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671237964684287811204651 2506856947026431716806977)
            ·
              refine ⟨1880142710269823787605233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2506856947026431716806977 1880142710269823787605233)
              ·
                refine ⟨1410107032702367840703925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880142710269823787605233 1410107032702367840703925)
                ·
                  refine ⟨132197534315846985065993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410107032702367840703925 132197534315846985065993)
                  ·
                    rfl

theorem cell22_1158542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1158542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158542 prefixEnd_1158542 := by exact prefixLift 1158542
  have htrace : WordTrace (prefixWord ++ tailWord_1158542) baseStart_1158542 baseEnd_1158542 := by
    simpa [prefixWord, tailWord_1158542, baseEnd_1158542] using wordTrace_append hprefix tailTrace_1158542
  have hstable : (prefixWord ++ tailWord_1158542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158542).length < 2 ^ (prefixWord ++ tailWord_1158542).sum := by decide
  have hdescent : baseEnd_1158542 < baseStart_1158542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158546 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1158546 : Nat := 118140960795 + 1158546 * 2 ^ 59
def prefixEnd_1158546 : Nat := 4983230072969 + 3 ^ 40 * 1158546 * 2
def baseEnd_1158546 : Nat := 396593972229286278097967

theorem tailTrace_1158546 : CollatzResearch.WordTrace tailWord_1158546 prefixEnd_1158546 396593972229286278097967 := by
  unfold tailWord_1158546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10563911015198295187289873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28170429373862120499439661 10563911015198295187289873)
  ·
    refine ⟨7922933261398721390467405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10563911015198295187289873 7922933261398721390467405)
    ·
      refine ⟨2971099973024520521425277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7922933261398721390467405 2971099973024520521425277)
      ·
        refine ⟨1114162489884195195534479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2971099973024520521425277 1114162489884195195534479)
        ·
          refine ⟨1671243734826292793301719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114162489884195195534479 1671243734826292793301719)
          ·
            refine ⟨2506865602239439189952579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671243734826292793301719 2506865602239439189952579)
            ·
              refine ⟨3760298403359158784928869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506865602239439189952579 3760298403359158784928869)
              ·
                refine ⟨705055950629842272174163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3760298403359158784928869 705055950629842272174163)
                ·
                  refine ⟨1057583925944763408261245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705055950629842272174163 1057583925944763408261245)
                  ·
                    refine ⟨396593972229286278097967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057583925944763408261245 396593972229286278097967)
                    ·
                      rfl

theorem cell22_1158546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1158546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158546 prefixEnd_1158546 := by exact prefixLift 1158546
  have htrace : WordTrace (prefixWord ++ tailWord_1158546) baseStart_1158546 baseEnd_1158546 := by
    simpa [prefixWord, tailWord_1158546, baseEnd_1158546] using wordTrace_append hprefix tailTrace_1158546
  have hstable : (prefixWord ++ tailWord_1158546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158546).length < 2 ^ (prefixWord ++ tailWord_1158546).sum := by decide
  have hdescent : baseEnd_1158546 < baseStart_1158546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158583 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1158583 : Nat := 118140960795 + 1158583 * 2 ^ 59
def prefixEnd_1158583 : Nat := 4983230072969 + 3 ^ 40 * 1158583 * 2
def baseEnd_1158583 : Nat := 396606638085430514922853

theorem tailTrace_1158583 : CollatzResearch.WordTrace tailWord_1158583 prefixEnd_1158583 396606638085430514922853 := by
  unfold tailWord_1158583
  simp only [CollatzResearch.WordTrace]
  refine ⟨42256993561659136068256403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28171329041106090712170935 42256993561659136068256403)
  ·
    refine ⟨63385490342488704102384605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42256993561659136068256403 63385490342488704102384605)
    ·
      refine ⟨23769558878433264038394227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63385490342488704102384605 23769558878433264038394227)
      ·
        refine ⟨35654338317649896057591341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23769558878433264038394227 35654338317649896057591341)
        ·
          refine ⟨13370376869118711021596753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35654338317649896057591341 13370376869118711021596753)
          ·
            refine ⟨10027782651839033266197565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13370376869118711021596753 10027782651839033266197565)
            ·
              refine ⟨3760418494439637474824087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10027782651839033266197565 3760418494439637474824087)
              ·
                refine ⟨5640627741659456212236131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760418494439637474824087 5640627741659456212236131)
                ·
                  refine ⟨8460941612489184318354197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640627741659456212236131 8460941612489184318354197)
                  ·
                    refine ⟨396606638085430514922853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8460941612489184318354197 396606638085430514922853)
                    ·
                      rfl

theorem cell22_1158583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1158583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158583 prefixEnd_1158583 := by exact prefixLift 1158583
  have htrace : WordTrace (prefixWord ++ tailWord_1158583) baseStart_1158583 baseEnd_1158583 := by
    simpa [prefixWord, tailWord_1158583, baseEnd_1158583] using wordTrace_append hprefix tailTrace_1158583
  have hstable : (prefixWord ++ tailWord_1158583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158583).length < 2 ^ (prefixWord ++ tailWord_1158583).sum := by decide
  have hdescent : baseEnd_1158583 < baseStart_1158583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158602 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_1158602 : Nat := 118140960795 + 1158602 * 2 ^ 59
def prefixEnd_1158602 : Nat := 4983230072969 + 3 ^ 40 * 1158602 * 2
def baseEnd_1158602 : Nat := 396613142173720798697795

theorem tailTrace_1158602 : CollatzResearch.WordTrace tailWord_1158602 prefixEnd_1158602 396613142173720798697795 := by
  unfold tailWord_1158602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564421637147575578299515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28171791032393534875465373 10564421637147575578299515)
  ·
    refine ⟨15846632455721363367449273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10564421637147575578299515 15846632455721363367449273)
    ·
      refine ⟨11884974341791022525586955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15846632455721363367449273 11884974341791022525586955)
      ·
        refine ⟨17827461512686533788380433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884974341791022525586955 17827461512686533788380433)
        ·
          refine ⟨13370596134514900341285325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17827461512686533788380433 13370596134514900341285325)
          ·
            refine ⟨5013973550443087627981997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13370596134514900341285325 5013973550443087627981997)
            ·
              refine ⟨1880240081416157860493249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5013973550443087627981997 1880240081416157860493249)
              ·
                refine ⟨1410180061062118395369937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880240081416157860493249 1410180061062118395369937)
                ·
                  refine ⟨1057635045796588796527453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410180061062118395369937 1057635045796588796527453)
                  ·
                    refine ⟨396613142173720798697795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057635045796588796527453 396613142173720798697795)
                    ·
                      rfl

theorem cell22_1158602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_1158602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158602 prefixEnd_1158602 := by exact prefixLift 1158602
  have htrace : WordTrace (prefixWord ++ tailWord_1158602) baseStart_1158602 baseEnd_1158602 := by
    simpa [prefixWord, tailWord_1158602, baseEnd_1158602] using wordTrace_append hprefix tailTrace_1158602
  have hstable : (prefixWord ++ tailWord_1158602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158602).length < 2 ^ (prefixWord ++ tailWord_1158602).sum := by decide
  have hdescent : baseEnd_1158602 < baseStart_1158602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158628 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1158628 : Nat := 118140960795 + 1158628 * 2 ^ 59
def prefixEnd_1158628 : Nat := 4983230072969 + 3 ^ 40 * 1158628 * 2
def baseEnd_1158628 : Nat := 396622042505065397547715

theorem tailTrace_1158628 : CollatzResearch.WordTrace tailWord_1158628 prefixEnd_1158628 396622042505065397547715 := by
  unfold tailWord_1158628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129317423248054376822269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28172423230997405835763025 21129317423248054376822269)
  ·
    refine ⟨7923494033718020391308351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21129317423248054376822269 7923494033718020391308351)
    ·
      refine ⟨11885241050577030586962527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7923494033718020391308351 11885241050577030586962527)
      ·
        refine ⟨17827861575865545880443791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885241050577030586962527 17827861575865545880443791)
        ·
          refine ⟨26741792363798318820665687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827861575865545880443791 26741792363798318820665687)
          ·
            refine ⟨40112688545697478230998531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26741792363798318820665687 40112688545697478230998531)
            ·
              refine ⟨60169032818546217346497797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40112688545697478230998531 60169032818546217346497797)
              ·
                refine ⟨11281693653477415752468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60169032818546217346497797 11281693653477415752468337)
                ·
                  refine ⟨8461270240108061814351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11281693653477415752468337 8461270240108061814351253)
                  ·
                    refine ⟨396622042505065397547715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8461270240108061814351253 396622042505065397547715)
                    ·
                      rfl

theorem cell22_1158628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1158628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158628 prefixEnd_1158628 := by exact prefixLift 1158628
  have htrace : WordTrace (prefixWord ++ tailWord_1158628) baseStart_1158628 baseEnd_1158628 := by
    simpa [prefixWord, tailWord_1158628, baseEnd_1158628] using wordTrace_append hprefix tailTrace_1158628
  have hstable : (prefixWord ++ tailWord_1158628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158628).length < 2 ^ (prefixWord ++ tailWord_1158628).sum := by decide
  have hdescent : baseEnd_1158628 < baseStart_1158628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158647 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 1, 3]
def baseStart_1158647 : Nat := 118140960795 + 1158647 * 2 ^ 59
def prefixEnd_1158647 : Nat := 4983230072969 + 3 ^ 40 * 1158647 * 2
def baseEnd_1158647 : Nat := 396628546593355681322657

theorem tailTrace_1158647 : CollatzResearch.WordTrace tailWord_1158647 prefixEnd_1158647 396628546593355681322657 := by
  unfold tailWord_1158647
  simp only [CollatzResearch.WordTrace]
  refine ⟨42259327833427274998586195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28172885222284849999057463 42259327833427274998586195)
  ·
    refine ⟨63388991750140912497879293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42259327833427274998586195 63388991750140912497879293)
    ·
      refine ⟨23770871906302842186704735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63388991750140912497879293 23770871906302842186704735)
      ·
        refine ⟨35656307859454263280057103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23770871906302842186704735 35656307859454263280057103)
        ·
          refine ⟨53484461789181394920085655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35656307859454263280057103 53484461789181394920085655)
          ·
            refine ⟨80226692683772092380128483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53484461789181394920085655 80226692683772092380128483)
            ·
              refine ⟨120340039025658138570192725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80226692683772092380128483 120340039025658138570192725)
              ·
                refine ⟨705117416165965655684723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 120340039025658138570192725 705117416165965655684723)
                ·
                  refine ⟨1057676124248948483527085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705117416165965655684723 1057676124248948483527085)
                  ·
                    refine ⟨396628546593355681322657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057676124248948483527085 396628546593355681322657)
                    ·
                      rfl

theorem cell22_1158647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_1158647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158647 prefixEnd_1158647 := by exact prefixLift 1158647
  have htrace : WordTrace (prefixWord ++ tailWord_1158647) baseStart_1158647 baseEnd_1158647 := by
    simpa [prefixWord, tailWord_1158647, baseEnd_1158647] using wordTrace_append hprefix tailTrace_1158647
  have hstable : (prefixWord ++ tailWord_1158647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158647).length < 2 ^ (prefixWord ++ tailWord_1158647).sum := by decide
  have hdescent : baseEnd_1158647 < baseStart_1158647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158677 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 5]
def baseStart_1158677 : Nat := 118140960795 + 1158677 * 2 ^ 59
def prefixEnd_1158677 : Nat := 4983230072969 + 3 ^ 40 * 1158677 * 2
def baseEnd_1158677 : Nat := 132212938735481867690855

theorem tailTrace_1158677 : CollatzResearch.WordTrace tailWord_1158677 prefixEnd_1158677 132212938735481867690855 := by
  unfold tailWord_1158677
  simp only [CollatzResearch.WordTrace]
  refine ⟨42260422023318590122178285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28173614682212393414785523 42260422023318590122178285)
  ·
    refine ⟨15847658258744471295816857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42260422023318590122178285 15847658258744471295816857)
    ·
      refine ⟨11885743694058353471862643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15847658258744471295816857 11885743694058353471862643)
      ·
        refine ⟨17828615541087530207793965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885743694058353471862643 17828615541087530207793965)
        ·
          refine ⟨6685730827907823827922737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17828615541087530207793965 6685730827907823827922737)
          ·
            refine ⟨5014298120930867870942053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685730827907823827922737 5014298120930867870942053)
            ·
              refine ⟨940180897674537725801635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5014298120930867870942053 940180897674537725801635)
              ·
                refine ⟨1410271346511806588702453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940180897674537725801635 1410271346511806588702453)
                ·
                  refine ⟨132212938735481867690855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410271346511806588702453 132212938735481867690855)
                  ·
                    rfl

theorem cell22_1158677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_1158677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158677 prefixEnd_1158677 := by exact prefixLift 1158677
  have htrace : WordTrace (prefixWord ++ tailWord_1158677) baseStart_1158677 baseEnd_1158677 := by
    simpa [prefixWord, tailWord_1158677, baseEnd_1158677] using wordTrace_append hprefix tailTrace_1158677
  have hstable : (prefixWord ++ tailWord_1158677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158677).length < 2 ^ (prefixWord ++ tailWord_1158677).sum := by decide
  have hdescent : baseEnd_1158677 < baseStart_1158677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158737 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_1158737 : Nat := 118140960795 + 1158737 * 2 ^ 59
def prefixEnd_1158737 : Nat := 4983230072969 + 3 ^ 40 * 1158737 * 2
def baseEnd_1158737 : Nat := 396659355432625446572381

theorem tailTrace_1158737 : CollatzResearch.WordTrace tailWord_1158737 prefixEnd_1158737 396659355432625446572381 := by
  unfold tailWord_1158737
  simp only [CollatzResearch.WordTrace]
  refine ⟨42262610403101220369362465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28175073602067480246241643 42262610403101220369362465)
  ·
    refine ⟨31696957802325915277021849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42262610403101220369362465 31696957802325915277021849)
    ·
      refine ⟨23772718351744436457766387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31696957802325915277021849 23772718351744436457766387)
      ·
        refine ⟨35659077527616654686649581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23772718351744436457766387 35659077527616654686649581)
        ·
          refine ⟨13372154072856245507493593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35659077527616654686649581 13372154072856245507493593)
          ·
            refine ⟨10029115554642184130620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13372154072856245507493593 10029115554642184130620195)
            ·
              refine ⟨15043673331963276195930293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10029115554642184130620195 15043673331963276195930293)
              ·
                refine ⟨1410344374871557143368465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15043673331963276195930293 1410344374871557143368465)
                ·
                  refine ⟨1057758281153667857526349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410344374871557143368465 1057758281153667857526349)
                  ·
                    refine ⟨396659355432625446572381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057758281153667857526349 396659355432625446572381)
                    ·
                      rfl

theorem cell22_1158737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_1158737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158737 prefixEnd_1158737 := by exact prefixLift 1158737
  have htrace : WordTrace (prefixWord ++ tailWord_1158737) baseStart_1158737 baseEnd_1158737 := by
    simpa [prefixWord, tailWord_1158737, baseEnd_1158737] using wordTrace_append hprefix tailTrace_1158737
  have hstable : (prefixWord ++ tailWord_1158737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158737).length < 2 ^ (prefixWord ++ tailWord_1158737).sum := by decide
  have hdescent : baseEnd_1158737 < baseStart_1158737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158816 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_1158816 : Nat := 118140960795 + 1158816 * 2 ^ 59
def prefixEnd_1158816 : Nat := 4983230072969 + 3 ^ 40 * 1158816 * 2
def baseEnd_1158816 : Nat := 396686398747095573847139

theorem tailTrace_1158816 : CollatzResearch.WordTrace tailWord_1158816 prefixEnd_1158816 396686398747095573847139 := by
  unfold tailWord_1158816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132745884907508430744151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28176994513210011240992201 21132745884907508430744151)
  ·
    refine ⟨31699118827361262646116227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21132745884907508430744151 31699118827361262646116227)
    ·
      refine ⟨47548678241041893969174341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31699118827361262646116227 47548678241041893969174341)
      ·
        refine ⟨8915377170195355119220189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47548678241041893969174341 8915377170195355119220189)
        ·
          refine ⟨3343266438823258169707571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8915377170195355119220189 3343266438823258169707571)
          ·
            refine ⟨5014899658234887254561357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343266438823258169707571 5014899658234887254561357)
            ·
              refine ⟨1880587371838082720460509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5014899658234887254561357 1880587371838082720460509)
              ·
                refine ⟨705220264439281020172691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1880587371838082720460509 705220264439281020172691)
                ·
                  refine ⟨1057830396658921530259037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705220264439281020172691 1057830396658921530259037)
                  ·
                    refine ⟨396686398747095573847139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1057830396658921530259037 396686398747095573847139)
                    ·
                      rfl

theorem cell22_1158816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_1158816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158816 prefixEnd_1158816 := by exact prefixLift 1158816
  have htrace : WordTrace (prefixWord ++ tailWord_1158816) baseStart_1158816 baseEnd_1158816 := by
    simpa [prefixWord, tailWord_1158816, baseEnd_1158816] using wordTrace_append hprefix tailTrace_1158816
  have hstable : (prefixWord ++ tailWord_1158816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158816).length < 2 ^ (prefixWord ++ tailWord_1158816).sum := by decide
  have hdescent : baseEnd_1158816 < baseStart_1158816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158846 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_1158846 : Nat := 118140960795 + 1158846 * 2 ^ 59
def prefixEnd_1158846 : Nat := 4983230072969 + 3 ^ 40 * 1158846 * 2
def baseEnd_1158846 : Nat := 132232222786728498532349

theorem tailTrace_1158846 : CollatzResearch.WordTrace tailWord_1158846 prefixEnd_1158846 132232222786728498532349 := by
  unfold tailWord_1158846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5283323244963291498135049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28177723973137554656720261 5283323244963291498135049)
  ·
    refine ⟨3962492433722468623601287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5283323244963291498135049 3962492433722468623601287)
    ·
      refine ⟨5943738650583702935401931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962492433722468623601287 5943738650583702935401931)
      ·
        refine ⟨8915607975875554403102897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943738650583702935401931 8915607975875554403102897)
        ·
          refine ⟨6686705981906665802327173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8915607975875554403102897 6686705981906665802327173)
          ·
            refine ⟨1253757371607499837936345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6686705981906665802327173 1253757371607499837936345)
            ·
              refine ⟨940318028705624878452259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253757371607499837936345 940318028705624878452259)
              ·
                refine ⟨1410477043058437317678389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940318028705624878452259 1410477043058437317678389)
                ·
                  refine ⟨132232222786728498532349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410477043058437317678389 132232222786728498532349)
                  ·
                    rfl

theorem cell22_1158846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_1158846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158846 prefixEnd_1158846 := by exact prefixLift 1158846
  have htrace : WordTrace (prefixWord ++ tailWord_1158846) baseStart_1158846 baseEnd_1158846 := by
    simpa [prefixWord, tailWord_1158846, baseEnd_1158846] using wordTrace_append hprefix tailTrace_1158846
  have hstable : (prefixWord ++ tailWord_1158846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158846).length < 2 ^ (prefixWord ++ tailWord_1158846).sum := by decide
  have hdescent : baseEnd_1158846 < baseStart_1158846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1158872 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1158872 : Nat := 118140960795 + 1158872 * 2 ^ 59
def prefixEnd_1158872 : Nat := 4983230072969 + 3 ^ 40 * 1158872 * 2
def baseEnd_1158872 : Nat := 396705568691530094446967

theorem tailTrace_1158872 : CollatzResearch.WordTrace tailWord_1158872 prefixEnd_1158872 396705568691530094446967 := by
  unfold tailWord_1158872
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133767128806069212763435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28178356171741425617017913 21133767128806069212763435)
  ·
    refine ⟨31700650693209103819145153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21133767128806069212763435 31700650693209103819145153)
    ·
      refine ⟨23775488019906827864358865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31700650693209103819145153 23775488019906827864358865)
      ·
        refine ⟨17831616014930120898269149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23775488019906827864358865 17831616014930120898269149)
        ·
          refine ⟨6686856005598795336850931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17831616014930120898269149 6686856005598795336850931)
          ·
            refine ⟨10030284008398193005276397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686856005598795336850931 10030284008398193005276397)
            ·
              refine ⟨3761356503149322376978649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10030284008398193005276397 3761356503149322376978649)
              ·
                refine ⟨2821017377361991782733987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761356503149322376978649 2821017377361991782733987)
                ·
                  refine ⟨4231526066042987674100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821017377361991782733987 4231526066042987674100981)
                  ·
                    refine ⟨396705568691530094446967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4231526066042987674100981 396705568691530094446967)
                    ·
                      rfl

theorem cell22_1158872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1158872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1158872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1158872 prefixEnd_1158872 := by exact prefixLift 1158872
  have htrace : WordTrace (prefixWord ++ tailWord_1158872) baseStart_1158872 baseEnd_1158872 := by
    simpa [prefixWord, tailWord_1158872, baseEnd_1158872] using wordTrace_append hprefix tailTrace_1158872
  have hstable : (prefixWord ++ tailWord_1158872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1158872).length < 2 ^ (prefixWord ++ tailWord_1158872).sum := by decide
  have hdescent : baseEnd_1158872 < baseStart_1158872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1158872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159054 : List Nat := [4, 1, 1, 5, 11]
def baseStart_1159054 : Nat := 118140960795 + 1159054 * 2 ^ 59
def prefixEnd_1159054 : Nat := 4983230072969 + 3 ^ 40 * 1159054 * 2
def baseEnd_1159054 : Nat := 1632789592637622577763

theorem tailTrace_1159054 : CollatzResearch.WordTrace tailWord_1159054 prefixEnd_1159054 1632789592637622577763 := by
  unfold tailWord_1159054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5284271542869097938581527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28182781561968522339101477 5284271542869097938581527)
  ·
    refine ⟨7926407314303646907872291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5284271542869097938581527 7926407314303646907872291)
    ·
      refine ⟨11889610971455470361808437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7926407314303646907872291 11889610971455470361808437)
      ·
        refine ⟨1114651028573950346419541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11889610971455470361808437 1114651028573950346419541)
        ·
          refine ⟨1632789592637622577763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1114651028573950346419541 1632789592637622577763)
          ·
            rfl

theorem cell22_1159054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 11].length) (baseStart_1159054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159054 prefixEnd_1159054 := by exact prefixLift 1159054
  have htrace : WordTrace (prefixWord ++ tailWord_1159054) baseStart_1159054 baseEnd_1159054 := by
    simpa [prefixWord, tailWord_1159054, baseEnd_1159054] using wordTrace_append hprefix tailTrace_1159054
  have hstable : (prefixWord ++ tailWord_1159054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159054).length < 2 ^ (prefixWord ++ tailWord_1159054).sum := by decide
  have hdescent : baseEnd_1159054 < baseStart_1159054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159058 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1159058 : Nat := 118140960795 + 1159058 * 2 ^ 59
def prefixEnd_1159058 : Nat := 4983230072969 + 3 ^ 40 * 1159058 * 2
def baseEnd_1159058 : Nat := 396769240292687609296397

theorem tailTrace_1159058 : CollatzResearch.WordTrace tailWord_1159058 prefixEnd_1159058 396769240292687609296397 := by
  unfold tailWord_1159058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10568579558734573047949457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28182878823292194794531885 10568579558734573047949457)
  ·
    refine ⟨7926434669050929785962093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10568579558734573047949457 7926434669050929785962093)
    ·
      refine ⟨2972413000894098669735785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7926434669050929785962093 2972413000894098669735785)
      ·
        refine ⟨2229309750670574002301839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2972413000894098669735785 2229309750670574002301839)
        ·
          refine ⟨3343964626005861003452759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229309750670574002301839 3343964626005861003452759)
          ·
            refine ⟨5015946939008791505179139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343964626005861003452759 5015946939008791505179139)
            ·
              refine ⟨7523920408513187257768709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015946939008791505179139 7523920408513187257768709)
              ·
                refine ⟨1410735076596222610831633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7523920408513187257768709 1410735076596222610831633)
                ·
                  refine ⟨1058051307447166958123725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410735076596222610831633 1058051307447166958123725)
                  ·
                    refine ⟨396769240292687609296397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058051307447166958123725 396769240292687609296397)
                    ·
                      rfl

theorem cell22_1159058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1159058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159058 prefixEnd_1159058 := by exact prefixLift 1159058
  have htrace : WordTrace (prefixWord ++ tailWord_1159058) baseStart_1159058 baseEnd_1159058 := by
    simpa [prefixWord, tailWord_1159058, baseEnd_1159058] using wordTrace_append hprefix tailTrace_1159058
  have hstable : (prefixWord ++ tailWord_1159058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159058).length < 2 ^ (prefixWord ++ tailWord_1159058).sum := by decide
  have hdescent : baseEnd_1159058 < baseStart_1159058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159060 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1159060 : Nat := 118140960795 + 1159060 * 2 ^ 59
def prefixEnd_1159060 : Nat := 4983230072969 + 3 ^ 40 * 1159060 * 2
def baseEnd_1159060 : Nat := 132256641644520090248797

theorem tailTrace_1159060 : CollatzResearch.WordTrace tailWord_1159060 prefixEnd_1159060 132256641644520090248797 := by
  unfold tailWord_1159060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137195590465523266685317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28182927453954031022247089 21137195590465523266685317)
  ·
    refine ⟨3963224173212285612503497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21137195590465523266685317 3963224173212285612503497)
    ·
      refine ⟨2972418129909214209377623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3963224173212285612503497 2972418129909214209377623)
      ·
        refine ⟨4458627194863821314066435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972418129909214209377623 4458627194863821314066435)
        ·
          refine ⟨6687940792295731971099653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458627194863821314066435 6687940792295731971099653)
          ·
            refine ⟨1253988898555449744581185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6687940792295731971099653 1253988898555449744581185)
            ·
              refine ⟨940491673916587308435889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1253988898555449744581185 940491673916587308435889)
              ·
                refine ⟨705368755437440481326917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940491673916587308435889 705368755437440481326917)
                ·
                  refine ⟨132256641644520090248797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705368755437440481326917 132256641644520090248797)
                  ·
                    rfl

theorem cell22_1159060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1159060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159060 prefixEnd_1159060 := by exact prefixLift 1159060
  have htrace : WordTrace (prefixWord ++ tailWord_1159060) baseStart_1159060 baseEnd_1159060 := by
    simpa [prefixWord, tailWord_1159060, baseEnd_1159060] using wordTrace_append hprefix tailTrace_1159060
  have hstable : (prefixWord ++ tailWord_1159060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159060).length < 2 ^ (prefixWord ++ tailWord_1159060).sum := by decide
  have hdescent : baseEnd_1159060 < baseStart_1159060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159071 : List Nat := [1, 1, 2, 5, 3, 2, 1, 7]
def baseStart_1159071 : Nat := 118140960795 + 1159071 * 2 ^ 59
def prefixEnd_1159071 : Nat := 4983230072969 + 3 ^ 40 * 1159071 * 2
def baseEnd_1159071 : Nat := 44085965606484434302373

theorem tailTrace_1159071 : CollatzResearch.WordTrace tailWord_1159071 prefixEnd_1159071 44085965606484434302373 := by
  unfold tailWord_1159071
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274792383891195412021067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28183194922594130274680711 42274792383891195412021067)
  ·
    refine ⟨63412188575836793118031601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42274792383891195412021067 63412188575836793118031601)
    ·
      refine ⟨47559141431877594838523701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63412188575836793118031601 47559141431877594838523701)
      ·
        refine ⟨4458669509238524516111597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47559141431877594838523701 4458669509238524516111597)
        ·
          refine ⟨1672001065964446693541849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4458669509238524516111597 1672001065964446693541849)
          ·
            refine ⟨1254000799473335020156387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672001065964446693541849 1254000799473335020156387)
            ·
              refine ⟨1881001199210002530234581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254000799473335020156387 1881001199210002530234581)
              ·
                refine ⟨44085965606484434302373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1881001199210002530234581 44085965606484434302373)
                ·
                  rfl

theorem cell22_1159071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 7].length) (baseStart_1159071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159071 prefixEnd_1159071 := by exact prefixLift 1159071
  have htrace : WordTrace (prefixWord ++ tailWord_1159071) baseStart_1159071 baseEnd_1159071 := by
    simpa [prefixWord, tailWord_1159071, baseEnd_1159071] using wordTrace_append hprefix tailTrace_1159071
  have hstable : (prefixWord ++ tailWord_1159071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159071).length < 2 ^ (prefixWord ++ tailWord_1159071).sum := by decide
  have hdescent : baseEnd_1159071 < baseStart_1159071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159103 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 1, 3]
def baseStart_1159103 : Nat := 118140960795 + 1159103 * 2 ^ 59
def prefixEnd_1159103 : Nat := 4983230072969 + 3 ^ 40 * 1159103 * 2
def baseEnd_1159103 : Nat := 396784644712322491921259

theorem tailTrace_1159103 : CollatzResearch.WordTrace tailWord_1159103 prefixEnd_1159103 396784644712322491921259 := by
  unfold tailWord_1159103
  simp only [CollatzResearch.WordTrace]
  refine ⟨42275959519775264877185963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28183973013183509918123975 42275959519775264877185963)
  ·
    refine ⟨63413939279662897315778945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42275959519775264877185963 63413939279662897315778945)
    ·
      refine ⟨47560454459747172986834209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63413939279662897315778945 47560454459747172986834209)
      ·
        refine ⟨35670340844810379740125657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47560454459747172986834209 35670340844810379740125657)
        ·
          refine ⟨26752755633607784805094243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35670340844810379740125657 26752755633607784805094243)
          ·
            refine ⟨40129133450411677207641365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26752755633607784805094243 40129133450411677207641365)
            ·
              refine ⟨1881053130488047369108189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40129133450411677207641365 1881053130488047369108189)
              ·
                refine ⟨705394923933017763415571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881053130488047369108189 705394923933017763415571)
                ·
                  refine ⟨1058092385899526645123357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705394923933017763415571 1058092385899526645123357)
                  ·
                    refine ⟨396784644712322491921259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058092385899526645123357 396784644712322491921259)
                    ·
                      rfl

theorem cell22_1159103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_1159103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159103 prefixEnd_1159103 := by exact prefixLift 1159103
  have htrace : WordTrace (prefixWord ++ tailWord_1159103) baseStart_1159103 baseEnd_1159103 := by
    simpa [prefixWord, tailWord_1159103, baseEnd_1159103] using wordTrace_append hprefix tailTrace_1159103
  have hstable : (prefixWord ++ tailWord_1159103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159103).length < 2 ^ (prefixWord ++ tailWord_1159103).sum := by decide
  have hdescent : baseEnd_1159103 < baseStart_1159103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159114 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1159114 : Nat := 118140960795 + 1159114 * 2 ^ 59
def prefixEnd_1159114 : Nat := 4983230072969 + 3 ^ 40 * 1159114 * 2
def baseEnd_1159114 : Nat := 396788410237122129896225

theorem tailTrace_1159114 : CollatzResearch.WordTrace tailWord_1159114 prefixEnd_1159114 396788410237122129896225 := by
  unfold tailWord_1159114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10569090180683853438959099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28184240481823609170557597 10569090180683853438959099)
  ·
    refine ⟨15853635271025780158438649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10569090180683853438959099 15853635271025780158438649)
    ·
      refine ⟨11890226453269335118828987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15853635271025780158438649 11890226453269335118828987)
      ·
        refine ⟨17835339679904002678243481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11890226453269335118828987 17835339679904002678243481)
        ·
          refine ⟨13376504759928002008682611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17835339679904002678243481 13376504759928002008682611)
          ·
            refine ⟨20064757139892003013023917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13376504759928002008682611 20064757139892003013023917)
            ·
              refine ⟨7524283927459501129883969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20064757139892003013023917 7524283927459501129883969)
              ·
                refine ⟨5643212945594625847412977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7524283927459501129883969 5643212945594625847412977)
                ·
                  refine ⟨4232409709195969385559733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5643212945594625847412977 4232409709195969385559733)
                  ·
                    refine ⟨396788410237122129896225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4232409709195969385559733 396788410237122129896225)
                    ·
                      rfl

theorem cell22_1159114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1159114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159114 prefixEnd_1159114 := by exact prefixLift 1159114
  have htrace : WordTrace (prefixWord ++ tailWord_1159114) baseStart_1159114 baseEnd_1159114 := by
    simpa [prefixWord, tailWord_1159114, baseEnd_1159114] using wordTrace_append hprefix tailTrace_1159114
  have hstable : (prefixWord ++ tailWord_1159114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159114).length < 2 ^ (prefixWord ++ tailWord_1159114).sum := by decide
  have hdescent : baseEnd_1159114 < baseStart_1159114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159116 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_1159116 : Nat := 118140960795 + 1159116 * 2 ^ 59
def prefixEnd_1159116 : Nat := 4983230072969 + 3 ^ 40 * 1159116 * 2
def baseEnd_1159116 : Nat := 132263031625998263782073

theorem tailTrace_1159116 : CollatzResearch.WordTrace tailWord_1159116 prefixEnd_1159116 132263031625998263782073 := by
  unfold tailWord_1159116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21138216834364084048704601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28184289112485445398272801 21138216834364084048704601)
  ·
    refine ⟨15853662625773063036528451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21138216834364084048704601 15853662625773063036528451)
    ·
      refine ⟨23780493938659594554792677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15853662625773063036528451 23780493938659594554792677)
      ·
        refine ⟨4458842613498673979023627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23780493938659594554792677 4458842613498673979023627)
        ·
          refine ⟨6688263920248010968535441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458842613498673979023627 6688263920248010968535441)
          ·
            refine ⟨5016197940186008226401581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688263920248010968535441 5016197940186008226401581)
            ·
              refine ⟨1881074227569753084900593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016197940186008226401581 1881074227569753084900593)
              ·
                refine ⟨1410805670677314813675445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881074227569753084900593 1410805670677314813675445)
                ·
                  refine ⟨132263031625998263782073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1410805670677314813675445 132263031625998263782073)
                  ·
                    rfl

theorem cell22_1159116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_1159116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159116 prefixEnd_1159116 := by exact prefixLift 1159116
  have htrace : WordTrace (prefixWord ++ tailWord_1159116) baseStart_1159116 baseEnd_1159116 := by
    simpa [prefixWord, tailWord_1159116, baseEnd_1159116] using wordTrace_append hprefix tailTrace_1159116
  have hstable : (prefixWord ++ tailWord_1159116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159116).length < 2 ^ (prefixWord ++ tailWord_1159116).sum := by decide
  have hdescent : baseEnd_1159116 < baseStart_1159116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159176 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1159176 : Nat := 118140960795 + 1159176 * 2 ^ 59
def prefixEnd_1159176 : Nat := 4983230072969 + 3 ^ 40 * 1159176 * 2
def baseEnd_1159176 : Nat := 396809634104174634846035

theorem tailTrace_1159176 : CollatzResearch.WordTrace tailWord_1159176 prefixEnd_1159176 396809634104174634846035 := by
  unfold tailWord_1159176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21139311024255399172296691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28185748032340532229728921 21139311024255399172296691)
  ·
    refine ⟨31708966536383098758445037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21139311024255399172296691 31708966536383098758445037)
    ·
      refine ⟨11890862451143662034416889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31708966536383098758445037 11890862451143662034416889)
      ·
        refine ⟨8918146838357746525812667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11890862451143662034416889 8918146838357746525812667)
        ·
          refine ⟨13377220257536619788719001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8918146838357746525812667 13377220257536619788719001)
          ·
            refine ⟨10032915193152464841539251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13377220257536619788719001 10032915193152464841539251)
            ·
              refine ⟨15049372789728697262308877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10032915193152464841539251 15049372789728697262308877)
              ·
                refine ⟨5643514796148261473365829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15049372789728697262308877 5643514796148261473365829)
                ·
                  refine ⟨1058159024277799026256093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5643514796148261473365829 1058159024277799026256093)
                  ·
                    refine ⟨396809634104174634846035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058159024277799026256093 396809634104174634846035)
                    ·
                      rfl

theorem cell22_1159176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1159176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159176 prefixEnd_1159176 := by exact prefixLift 1159176
  have htrace : WordTrace (prefixWord ++ tailWord_1159176) baseStart_1159176 baseEnd_1159176 := by
    simpa [prefixWord, tailWord_1159176, baseEnd_1159176] using wordTrace_append hprefix tailTrace_1159176
  have hstable : (prefixWord ++ tailWord_1159176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159176).length < 2 ^ (prefixWord ++ tailWord_1159176).sum := by decide
  have hdescent : baseEnd_1159176 < baseStart_1159176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159178 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_1159178 : Nat := 118140960795 + 1159178 * 2 ^ 59
def prefixEnd_1159178 : Nat := 4983230072969 + 3 ^ 40 * 1159178 * 2
def baseEnd_1159178 : Nat := 132270106248349098765343

theorem tailTrace_1159178 : CollatzResearch.WordTrace tailWord_1159178 prefixEnd_1159178 132270106248349098765343 := by
  unfold tailWord_1159178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10569673748625888171541547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28185796663002368457444125 10569673748625888171541547)
  ·
    refine ⟨15854510622938832257312321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10569673748625888171541547 15854510622938832257312321)
    ·
      refine ⟨11890882967204124192984241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15854510622938832257312321 11890882967204124192984241)
      ·
        refine ⟨8918162225403093144738181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11890882967204124192984241 8918162225403093144738181)
        ·
          refine ⟨1672155417263079964638409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8918162225403093144738181 1672155417263079964638409)
          ·
            refine ⟨1254116562947309973478807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672155417263079964638409 1254116562947309973478807)
            ·
              refine ⟨1881174844420964960218211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254116562947309973478807 1881174844420964960218211)
              ·
                refine ⟨2821762266631447440327317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881174844420964960218211 2821762266631447440327317)
                ·
                  refine ⟨132270106248349098765343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2821762266631447440327317 132270106248349098765343)
                  ·
                    rfl

theorem cell22_1159178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_1159178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159178 prefixEnd_1159178 := by exact prefixLift 1159178
  have htrace : WordTrace (prefixWord ++ tailWord_1159178) baseStart_1159178 baseEnd_1159178 := by
    simpa [prefixWord, tailWord_1159178, baseEnd_1159178] using wordTrace_append hprefix tailTrace_1159178
  have hstable : (prefixWord ++ tailWord_1159178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159178).length < 2 ^ (prefixWord ++ tailWord_1159178).sum := by decide
  have hdescent : baseEnd_1159178 < baseStart_1159178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159328 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_1159328 : Nat := 118140960795 + 1159328 * 2 ^ 59
def prefixEnd_1159328 : Nat := 4983230072969 + 3 ^ 40 * 1159328 * 2
def baseEnd_1159328 : Nat := 396861666810496905045569

theorem tailTrace_1159328 : CollatzResearch.WordTrace tailWord_1159328 prefixEnd_1159328 396861666810496905045569 := by
  unfold tailWord_1159328
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142082971980064152063319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28189443962640085536084425 21142082971980064152063319)
  ·
    refine ⟨31713124457970096228094979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21142082971980064152063319 31713124457970096228094979)
    ·
      refine ⟨47569686686955144342142469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31713124457970096228094979 47569686686955144342142469)
      ·
        refine ⟨8919316253804089564151713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47569686686955144342142469 8919316253804089564151713)
        ·
          refine ⟨6689487190353067173113785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8919316253804089564151713 6689487190353067173113785)
          ·
            refine ⟨5017115392764800379835339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6689487190353067173113785 5017115392764800379835339)
            ·
              refine ⟨7525673089147200569753009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5017115392764800379835339 7525673089147200569753009)
              ·
                refine ⟨5644254816860400427314757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7525673089147200569753009 5644254816860400427314757)
                ·
                  refine ⟨1058297778161325080121517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5644254816860400427314757 1058297778161325080121517)
                  ·
                    refine ⟨396861666810496905045569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058297778161325080121517 396861666810496905045569)
                    ·
                      rfl

theorem cell22_1159328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_1159328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159328 prefixEnd_1159328 := by exact prefixLift 1159328
  have htrace : WordTrace (prefixWord ++ tailWord_1159328) baseStart_1159328 baseEnd_1159328 := by
    simpa [prefixWord, tailWord_1159328, baseEnd_1159328] using wordTrace_append hprefix tailTrace_1159328
  have hstable : (prefixWord ++ tailWord_1159328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159328).length < 2 ^ (prefixWord ++ tailWord_1159328).sum := by decide
  have hdescent : baseEnd_1159328 < baseStart_1159328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159386 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_1159386 : Nat := 118140960795 + 1159386 * 2 ^ 59
def prefixEnd_1159386 : Nat := 4983230072969 + 3 ^ 40 * 1159386 * 2
def baseEnd_1159386 : Nat := 132293840465268029031797

theorem tailTrace_1159386 : CollatzResearch.WordTrace tailWord_1159386 prefixEnd_1159386 132293840465268029031797 := by
  unfold tailWord_1159386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571570344437501052434503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28190854251833336139825341 10571570344437501052434503)
  ·
    refine ⟨15857355516656251578651755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10571570344437501052434503 15857355516656251578651755)
    ·
      refine ⟨23786033274984377367977633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15857355516656251578651755 23786033274984377367977633)
      ·
        refine ⟨17839524956238283025983225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23786033274984377367977633 17839524956238283025983225)
        ·
          refine ⟨13379643717178712269487419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17839524956238283025983225 13379643717178712269487419)
          ·
            refine ⟨20069465575768068404231129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13379643717178712269487419 20069465575768068404231129)
            ·
              refine ⟨15052099181826051303173347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20069465575768068404231129 15052099181826051303173347)
              ·
                refine ⟨22578148772739076954760021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15052099181826051303173347 22578148772739076954760021)
                ·
                  refine ⟨132293840465268029031797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22578148772739076954760021 132293840465268029031797)
                  ·
                    rfl

theorem cell22_1159386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_1159386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159386 prefixEnd_1159386 := by exact prefixLift 1159386
  have htrace : WordTrace (prefixWord ++ tailWord_1159386) baseStart_1159386 baseEnd_1159386 := by
    simpa [prefixWord, tailWord_1159386, baseEnd_1159386] using wordTrace_append hprefix tailTrace_1159386
  have hstable : (prefixWord ++ tailWord_1159386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159386).length < 2 ^ (prefixWord ++ tailWord_1159386).sum := by decide
  have hdescent : baseEnd_1159386 < baseStart_1159386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159401 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1159401 : Nat := 118140960795 + 1159401 * 2 ^ 59
def prefixEnd_1159401 : Nat := 4983230072969 + 3 ^ 40 * 1159401 * 2
def baseEnd_1159401 : Nat := 396886656202349047970345

theorem tailTrace_1159401 : CollatzResearch.WordTrace tailWord_1159401 prefixEnd_1159401 396886656202349047970345 := by
  unfold tailWord_1159401
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286828472695661771534057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28191218981797107847689371 42286828472695661771534057)
  ·
    refine ⟨31715121354521746328650543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42286828472695661771534057 31715121354521746328650543)
    ·
      refine ⟨47572682031782619492975815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31715121354521746328650543 47572682031782619492975815)
      ·
        refine ⟨71359023047673929239463723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47572682031782619492975815 71359023047673929239463723)
        ·
          refine ⟨107038534571510893859195585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71359023047673929239463723 107038534571510893859195585)
          ·
            refine ⟨80278900928633170394396689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107038534571510893859195585 80278900928633170394396689)
            ·
              refine ⟨60209175696474877795797517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80278900928633170394396689 60209175696474877795797517)
              ·
                refine ⟨22578440886178079173424069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60209175696474877795797517 22578440886178079173424069)
                ·
                  refine ⟨4233457666158389845017013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22578440886178079173424069 4233457666158389845017013)
                  ·
                    refine ⟨396886656202349047970345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4233457666158389845017013 396886656202349047970345)
                    ·
                      rfl

theorem cell22_1159401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1159401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159401 prefixEnd_1159401 := by exact prefixLift 1159401
  have htrace : WordTrace (prefixWord ++ tailWord_1159401) baseStart_1159401 baseEnd_1159401 := by
    simpa [prefixWord, tailWord_1159401, baseEnd_1159401] using wordTrace_append hprefix tailTrace_1159401
  have hstable : (prefixWord ++ tailWord_1159401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159401).length < 2 ^ (prefixWord ++ tailWord_1159401).sum := by decide
  have hdescent : baseEnd_1159401 < baseStart_1159401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159403 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 5]
def baseStart_1159403 : Nat := 118140960795 + 1159403 * 2 ^ 59
def prefixEnd_1159403 : Nat := 4983230072969 + 3 ^ 40 * 1159403 * 2
def baseEnd_1159403 : Nat := 132295780281073903140113

theorem tailTrace_1159403 : CollatzResearch.WordTrace tailWord_1159403 prefixEnd_1159403 132295780281073903140113 := by
  unfold tailWord_1159403
  simp only [CollatzResearch.WordTrace]
  refine ⟨42286901418688416113106863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28191267612458944075404575 42286901418688416113106863)
  ·
    refine ⟨63430352128032624169660295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42286901418688416113106863 63430352128032624169660295)
    ·
      refine ⟨95145528192048936254490443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63430352128032624169660295 95145528192048936254490443)
      ·
        refine ⟨142718292288073404381735665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95145528192048936254490443 142718292288073404381735665)
        ·
          refine ⟨107038719216055053286301749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142718292288073404381735665 107038719216055053286301749)
          ·
            refine ⟨10034879926505161245590789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107038719216055053286301749 10034879926505161245590789)
            ·
              refine ⟨1881539986219717733548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10034879926505161245590789 1881539986219717733548273)
              ·
                refine ⟨1411154989664788300161205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881539986219717733548273 1411154989664788300161205)
                ·
                  refine ⟨132295780281073903140113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411154989664788300161205 132295780281073903140113)
                  ·
                    rfl

theorem cell22_1159403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].length) (baseStart_1159403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159403 prefixEnd_1159403 := by exact prefixLift 1159403
  have htrace : WordTrace (prefixWord ++ tailWord_1159403) baseStart_1159403 baseEnd_1159403 := by
    simpa [prefixWord, tailWord_1159403, baseEnd_1159403] using wordTrace_append hprefix tailTrace_1159403
  have hstable : (prefixWord ++ tailWord_1159403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159403).length < 2 ^ (prefixWord ++ tailWord_1159403).sum := by decide
  have hdescent : baseEnd_1159403 < baseStart_1159403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159407 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 1, 3]
def baseStart_1159407 : Nat := 118140960795 + 1159407 * 2 ^ 59
def prefixEnd_1159407 : Nat := 4983230072969 + 3 ^ 40 * 1159407 * 2
def baseEnd_1159407 : Nat := 396888710124967032320327

theorem tailTrace_1159407 : CollatzResearch.WordTrace tailWord_1159407 prefixEnd_1159407 396888710124967032320327 := by
  unfold tailWord_1159407
  simp only [CollatzResearch.WordTrace]
  refine ⟨42287047310673924796252475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28191364873782616530834983 42287047310673924796252475)
  ·
    refine ⟨63430570966010887194378713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42287047310673924796252475 63430570966010887194378713)
    ·
      refine ⟨47572928224508165395784035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63430570966010887194378713 47572928224508165395784035)
      ·
        refine ⟨71359392336762248093676053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47572928224508165395784035 71359392336762248093676053)
        ·
          refine ⟨3344971515785730379391065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71359392336762248093676053 3344971515785730379391065)
          ·
            refine ⟨2508728636839297784543299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3344971515785730379391065 2508728636839297784543299)
            ·
              refine ⟨3763092955258946676814949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508728636839297784543299 3763092955258946676814949)
              ·
                refine ⟨705579929111052501902803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3763092955258946676814949 705579929111052501902803)
                ·
                  refine ⟨1058369893666578752854205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705579929111052501902803 1058369893666578752854205)
                  ·
                    refine ⟨396888710124967032320327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058369893666578752854205 396888710124967032320327)
                    ·
                      rfl

theorem cell22_1159407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_1159407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159407 prefixEnd_1159407 := by exact prefixLift 1159407
  have htrace : WordTrace (prefixWord ++ tailWord_1159407) baseStart_1159407 baseEnd_1159407 := by
    simpa [prefixWord, tailWord_1159407, baseEnd_1159407] using wordTrace_append hprefix tailTrace_1159407
  have hstable : (prefixWord ++ tailWord_1159407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159407).length < 2 ^ (prefixWord ++ tailWord_1159407).sum := by decide
  have hdescent : baseEnd_1159407 < baseStart_1159407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159418 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_1159418 : Nat := 118140960795 + 1159418 * 2 ^ 59
def prefixEnd_1159418 : Nat := 4983230072969 + 3 ^ 40 * 1159418 * 2
def baseEnd_1159418 : Nat := 396892475649766670295293

theorem tailTrace_1159418 : CollatzResearch.WordTrace tailWord_1159418 prefixEnd_1159418 396892475649766670295293 := by
  unfold tailWord_1159418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10571862128408518418725727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28191632342422715783268605 10571862128408518418725727)
  ·
    refine ⟨15857793192612777628088591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10571862128408518418725727 15857793192612777628088591)
    ·
      refine ⟨23786689788919166442132887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15857793192612777628088591 23786689788919166442132887)
      ·
        refine ⟨35680034683378749663199331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23786689788919166442132887 35680034683378749663199331)
        ·
          refine ⟨53520052025068124494798997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35680034683378749663199331 53520052025068124494798997)
          ·
            refine ⟨2508752438675068335693703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53520052025068124494798997 2508752438675068335693703)
            ·
              refine ⟨3763128658012602503540555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2508752438675068335693703 3763128658012602503540555)
              ·
                refine ⟨5644692987018903755310833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763128658012602503540555 5644692987018903755310833)
                ·
                  refine ⟨4233519740264177816483125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5644692987018903755310833 4233519740264177816483125)
                  ·
                    refine ⟨396892475649766670295293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4233519740264177816483125 396892475649766670295293)
                    ·
                      rfl

theorem cell22_1159418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_1159418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159418 prefixEnd_1159418 := by exact prefixLift 1159418
  have htrace : WordTrace (prefixWord ++ tailWord_1159418) baseStart_1159418 baseEnd_1159418 := by
    simpa [prefixWord, tailWord_1159418, baseEnd_1159418] using wordTrace_append hprefix tailTrace_1159418
  have hstable : (prefixWord ++ tailWord_1159418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159418).length < 2 ^ (prefixWord ++ tailWord_1159418).sum := by decide
  have hdescent : baseEnd_1159418 < baseStart_1159418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159433 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_1159433 : Nat := 118140960795 + 1159433 * 2 ^ 59
def prefixEnd_1159433 : Nat := 4983230072969 + 3 ^ 40 * 1159433 * 2
def baseEnd_1159433 : Nat := 396897610456311631170247

theorem tailTrace_1159433 : CollatzResearch.WordTrace tailWord_1159433 prefixEnd_1159433 396897610456311631170247 := by
  unfold tailWord_1159433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42287995608579731236698953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28191997072386487491132635 42287995608579731236698953)
  ·
    refine ⟨31715996706434798427524215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42287995608579731236698953 31715996706434798427524215)
    ·
      refine ⟨47573995059652197641286323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31715996706434798427524215 47573995059652197641286323)
      ·
        refine ⟨71360992589478296461929485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47573995059652197641286323 71360992589478296461929485)
        ·
          refine ⟨26760372221054361173223557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71360992589478296461929485 26760372221054361173223557)
          ·
            refine ⟨5017569791447692719979417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26760372221054361173223557 5017569791447692719979417)
            ·
              refine ⟨3763177343585769539984563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5017569791447692719979417 3763177343585769539984563)
              ·
                refine ⟨5644766015378654309976845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3763177343585769539984563 5644766015378654309976845)
                ·
                  refine ⟨2116787255766995366241317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5644766015378654309976845 2116787255766995366241317)
                  ·
                    refine ⟨396897610456311631170247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2116787255766995366241317 396897610456311631170247)
                    ·
                      rfl

theorem cell22_1159433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_1159433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159433 prefixEnd_1159433 := by exact prefixLift 1159433
  have htrace : WordTrace (prefixWord ++ tailWord_1159433) baseStart_1159433 baseEnd_1159433 := by
    simpa [prefixWord, tailWord_1159433, baseEnd_1159433] using wordTrace_append hprefix tailTrace_1159433
  have hstable : (prefixWord ++ tailWord_1159433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159433).length < 2 ^ (prefixWord ++ tailWord_1159433).sum := by decide
  have hdescent : baseEnd_1159433 < baseStart_1159433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159454 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1159454 : Nat := 118140960795 + 1159454 * 2 ^ 59
def prefixEnd_1159454 : Nat := 4983230072969 + 3 ^ 40 * 1159454 * 2
def baseEnd_1159454 : Nat := 132301599728491525465061

theorem tailTrace_1159454 : CollatzResearch.WordTrace tailWord_1159454 prefixEnd_1159454 132301599728491525465061 := by
  unfold tailWord_1159454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286095192687956477901677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28192507694335767882142277 5286095192687956477901677)
  ·
    refine ⟨1982285697257983679213129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5286095192687956477901677 1982285697257983679213129)
    ·
      refine ⟨1486714272943487759409847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1982285697257983679213129 1486714272943487759409847)
      ·
        refine ⟨2230071409415231639114771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486714272943487759409847 2230071409415231639114771)
        ·
          refine ⟨3345107114122847458672157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230071409415231639114771 3345107114122847458672157)
          ·
            refine ⟨1254415167796067797002059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3345107114122847458672157 1254415167796067797002059)
            ·
              refine ⟨1881622751694101695503089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254415167796067797002059 1881622751694101695503089)
              ·
                refine ⟨1411217063770576271627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881622751694101695503089 1411217063770576271627317)
                ·
                  refine ⟨132301599728491525465061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411217063770576271627317 132301599728491525465061)
                  ·
                    rfl

theorem cell22_1159454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1159454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159454 prefixEnd_1159454 := by exact prefixLift 1159454
  have htrace : WordTrace (prefixWord ++ tailWord_1159454) baseStart_1159454 baseEnd_1159454 := by
    simpa [prefixWord, tailWord_1159454, baseEnd_1159454] using wordTrace_append hprefix tailTrace_1159454
  have hstable : (prefixWord ++ tailWord_1159454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159454).length < 2 ^ (prefixWord ++ tailWord_1159454).sum := by decide
  have hdescent : baseEnd_1159454 < baseStart_1159454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159480 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_1159480 : Nat := 118140960795 + 1159480 * 2 ^ 59
def prefixEnd_1159480 : Nat := 4983230072969 + 3 ^ 40 * 1159480 * 2
def baseEnd_1159480 : Nat := 396913699516819175245103

theorem tailTrace_1159480 : CollatzResearch.WordTrace tailWord_1159480 prefixEnd_1159480 396913699516819175245103 := by
  unfold tailWord_1159480
  simp only [CollatzResearch.WordTrace]
  refine ⟨21144854919704729131829947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28193139892939638842439929 21144854919704729131829947)
  ·
    refine ⟨31717282379557093697744921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21144854919704729131829947 31717282379557093697744921)
    ·
      refine ⟨23787961784667820273308691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31717282379557093697744921 23787961784667820273308691)
      ·
        refine ⟨35681942677001730409963037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23787961784667820273308691 35681942677001730409963037)
        ·
          refine ⟨13380728503875648903736139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35681942677001730409963037 13380728503875648903736139)
          ·
            refine ⟨20071092755813473355604209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13380728503875648903736139 20071092755813473355604209)
            ·
              refine ⟨15053319566860105016703157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20071092755813473355604209 15053319566860105016703157)
              ·
                refine ⟨1411248709393134845315921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15053319566860105016703157 1411248709393134845315921)
                ·
                  refine ⟨1058436532044851133986941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411248709393134845315921 1058436532044851133986941)
                  ·
                    refine ⟨396913699516819175245103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058436532044851133986941 396913699516819175245103)
                    ·
                      rfl

theorem cell22_1159480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_1159480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159480 prefixEnd_1159480 := by exact prefixLift 1159480
  have htrace : WordTrace (prefixWord ++ tailWord_1159480) baseStart_1159480 baseEnd_1159480 := by
    simpa [prefixWord, tailWord_1159480, baseEnd_1159480] using wordTrace_append hprefix tailTrace_1159480
  have hstable : (prefixWord ++ tailWord_1159480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159480).length < 2 ^ (prefixWord ++ tailWord_1159480).sum := by decide
  have hdescent : baseEnd_1159480 < baseStart_1159480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159516 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_1159516 : Nat := 118140960795 + 1159516 * 2 ^ 59
def prefixEnd_1159516 : Nat := 4983230072969 + 3 ^ 40 * 1159516 * 2
def baseEnd_1159516 : Nat := 132308674350842360448331

theorem tailTrace_1159516 : CollatzResearch.WordTrace tailWord_1159516 prefixEnd_1159516 132308674350842360448331 := by
  unfold tailWord_1159516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21145511433639518205985201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28194015244852690941313601 21145511433639518205985201)
  ·
    refine ⟨15859133575229638654488901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21145511433639518205985201 15859133575229638654488901)
    ·
      refine ⟨2973587545355557247716669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15859133575229638654488901 2973587545355557247716669)
      ·
        refine ⟨1115095329508333967893751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2973587545355557247716669 1115095329508333967893751)
        ·
          refine ⟨1672642994262500951840627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115095329508333967893751 1672642994262500951840627)
          ·
            refine ⟨2508964491393751427760941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672642994262500951840627 2508964491393751427760941)
            ·
              refine ⟨940861684272656785410353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2508964491393751427760941 940861684272656785410353)
              ·
                refine ⟨705646263204492589057765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940861684272656785410353 705646263204492589057765)
                ·
                  refine ⟨132308674350842360448331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705646263204492589057765 132308674350842360448331)
                  ·
                    rfl

theorem cell22_1159516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_1159516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159516 prefixEnd_1159516 := by exact prefixLift 1159516
  have htrace : WordTrace (prefixWord ++ tailWord_1159516) baseStart_1159516 baseEnd_1159516 := by
    simpa [prefixWord, tailWord_1159516, baseEnd_1159516] using wordTrace_append hprefix tailTrace_1159516
  have hstable : (prefixWord ++ tailWord_1159516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159516).length < 2 ^ (prefixWord ++ tailWord_1159516).sum := by decide
  have hdescent : baseEnd_1159516 < baseStart_1159516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159523 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_1159523 : Nat := 118140960795 + 1159523 * 2 ^ 59
def prefixEnd_1159523 : Nat := 4983230072969 + 3 ^ 40 * 1159523 * 2
def baseEnd_1159523 : Nat := 396928419295581396419971

theorem tailTrace_1159523 : CollatzResearch.WordTrace tailWord_1159523 prefixEnd_1159523 396928419295581396419971 := by
  unfold tailWord_1159523
  simp only [CollatzResearch.WordTrace]
  refine ⟨42291278178253676607475223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28194185452169117738316815 42291278178253676607475223)
  ·
    refine ⟨63436917267380514911212835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42291278178253676607475223 63436917267380514911212835)
    ·
      refine ⟨95155375901070772366819253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63436917267380514911212835 95155375901070772366819253)
      ·
        refine ⟨8920816490725384909389305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95155375901070772366819253 8920816490725384909389305)
        ·
          refine ⟨6690612368044038682041979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8920816490725384909389305 6690612368044038682041979)
          ·
            refine ⟨10035918552066058023062969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6690612368044038682041979 10035918552066058023062969)
            ·
              refine ⟨7526938914049543517297227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10035918552066058023062969 7526938914049543517297227)
              ·
                refine ⟨11290408371074315275945841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7526938914049543517297227 11290408371074315275945841)
                ·
                  refine ⟨8467806278305736456959381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11290408371074315275945841 8467806278305736456959381)
                  ·
                    refine ⟨396928419295581396419971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8467806278305736456959381 396928419295581396419971)
                    ·
                      rfl

theorem cell22_1159523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_1159523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159523 prefixEnd_1159523 := by exact prefixLift 1159523
  have htrace : WordTrace (prefixWord ++ tailWord_1159523) baseStart_1159523 baseEnd_1159523 := by
    simpa [prefixWord, tailWord_1159523, baseEnd_1159523] using wordTrace_append hprefix tailTrace_1159523
  have hstable : (prefixWord ++ tailWord_1159523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159523).length < 2 ^ (prefixWord ++ tailWord_1159523).sum := by decide
  have hdescent : baseEnd_1159523 < baseStart_1159523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159576 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_1159576 : Nat := 118140960795 + 1159576 * 2 ^ 59
def prefixEnd_1159576 : Nat := 4983230072969 + 3 ^ 40 * 1159576 * 2
def baseEnd_1159576 : Nat := 396946562278706924844809

theorem tailTrace_1159576 : CollatzResearch.WordTrace tailWord_1159576 prefixEnd_1159576 396946562278706924844809 := by
  unfold tailWord_1159576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146605623530833329577291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28195474164707777772769721 21146605623530833329577291)
  ·
    refine ⟨31719908435296249994365937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21146605623530833329577291 31719908435296249994365937)
    ·
      refine ⟨23789931326472187495774453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31719908435296249994365937 23789931326472187495774453)
      ·
        refine ⟨2230306061856767577728855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23789931326472187495774453 2230306061856767577728855)
        ·
          refine ⟨3345459092785151366593283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2230306061856767577728855 3345459092785151366593283)
          ·
            refine ⟨5018188639177727049889925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345459092785151366593283 5018188639177727049889925)
            ·
              refine ⟨940910369845823821854361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5018188639177727049889925 940910369845823821854361)
              ·
                refine ⟨705682777384367866390771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940910369845823821854361 705682777384367866390771)
                ·
                  refine ⟨1058524166076551799586157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705682777384367866390771 1058524166076551799586157)
                  ·
                    refine ⟨396946562278706924844809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058524166076551799586157 396946562278706924844809)
                    ·
                      rfl

theorem cell22_1159576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_1159576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159576 prefixEnd_1159576 := by exact prefixLift 1159576
  have htrace : WordTrace (prefixWord ++ tailWord_1159576) baseStart_1159576 baseEnd_1159576 := by
    simpa [prefixWord, tailWord_1159576, baseEnd_1159576] using wordTrace_append hprefix tailTrace_1159576
  have hstable : (prefixWord ++ tailWord_1159576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159576).length < 2 ^ (prefixWord ++ tailWord_1159576).sum := by decide
  have hdescent : baseEnd_1159576 < baseStart_1159576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1159630 : Nat := 118140960795 + 1159630 * 2 ^ 59
def prefixEnd_1159630 : Nat := 4983230072969 + 3 ^ 40 * 1159630 * 2
def baseEnd_1159630 : Nat := 396965047582268783994643

theorem tailTrace_1159630 : CollatzResearch.WordTrace tailWord_1159630 prefixEnd_1159630 396965047582268783994643 := by
  unfold tailWord_1159630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286897598608254235202543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28196787192577355921080229 5286897598608254235202543)
  ·
    refine ⟨7930346397912381352803815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5286897598608254235202543 7930346397912381352803815)
    ·
      refine ⟨11895519596868572029205723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930346397912381352803815 11895519596868572029205723)
      ·
        refine ⟨17843279395302858043808585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895519596868572029205723 17843279395302858043808585)
        ·
          refine ⟨13382459546477143532856439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17843279395302858043808585 13382459546477143532856439)
          ·
            refine ⟨20073689319715715299284659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13382459546477143532856439 20073689319715715299284659)
            ·
              refine ⟨30110533979573572948926989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20073689319715715299284659 30110533979573572948926989)
              ·
                refine ⟨11291450242340089855847621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30110533979573572948926989 11291450242340089855847621)
                ·
                  refine ⟨2117146920438766847971429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11291450242340089855847621 2117146920438766847971429)
                  ·
                    refine ⟨396965047582268783994643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2117146920438766847971429 396965047582268783994643)
                    ·
                      rfl

theorem cell22_1159630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1159630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159630 prefixEnd_1159630 := by exact prefixLift 1159630
  have htrace : WordTrace (prefixWord ++ tailWord_1159630) baseStart_1159630 baseEnd_1159630 := by
    simpa [prefixWord, tailWord_1159630, baseEnd_1159630] using wordTrace_append hprefix tailTrace_1159630
  have hstable : (prefixWord ++ tailWord_1159630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159630).length < 2 ^ (prefixWord ++ tailWord_1159630).sum := by decide
  have hdescent : baseEnd_1159630 < baseStart_1159630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159634 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1159634 : Nat := 118140960795 + 1159634 * 2 ^ 59
def prefixEnd_1159634 : Nat := 4983230072969 + 3 ^ 40 * 1159634 * 2
def baseEnd_1159634 : Nat := 132322138954671368964877

theorem tailTrace_1159634 : CollatzResearch.WordTrace tailWord_1159634 prefixEnd_1159634 132322138954671368964877 := by
  unfold tailWord_1159634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10573831670212885641191489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28196884453901028376510637 10573831670212885641191489)
  ·
    refine ⟨7930373752659664230893617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10573831670212885641191489 7930373752659664230893617)
    ·
      refine ⟨5947780314494748173170213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930373752659664230893617 5947780314494748173170213)
      ·
        refine ⟨1115208808967765282469415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5947780314494748173170213 1115208808967765282469415)
        ·
          refine ⟨1672813213451647923704123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115208808967765282469415 1672813213451647923704123)
          ·
            refine ⟨2509219820177471885556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672813213451647923704123 2509219820177471885556185)
            ·
              refine ⟨1881914865133103914167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2509219820177471885556185 1881914865133103914167139)
              ·
                refine ⟨2822872297699655871250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881914865133103914167139 2822872297699655871250709)
                ·
                  refine ⟨132322138954671368964877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2822872297699655871250709 132322138954671368964877)
                  ·
                    rfl

theorem cell22_1159634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1159634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159634 prefixEnd_1159634 := by exact prefixLift 1159634
  have htrace : WordTrace (prefixWord ++ tailWord_1159634) baseStart_1159634 baseEnd_1159634 := by
    simpa [prefixWord, tailWord_1159634, baseEnd_1159634] using wordTrace_append hprefix tailTrace_1159634
  have hstable : (prefixWord ++ tailWord_1159634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159634).length < 2 ^ (prefixWord ++ tailWord_1159634).sum := by decide
  have hdescent : baseEnd_1159634 < baseStart_1159634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159645 : List Nat := [1, 4, 3, 1, 1, 1, 2, 9]
def baseStart_1159645 : Nat := 118140960795 + 1159645 * 2 ^ 59
def prefixEnd_1159645 : Nat := 4983230072969 + 3 ^ 40 * 1159645 * 2
def baseEnd_1159645 : Nat := 44107798043201527207733

theorem tailTrace_1159645 : CollatzResearch.WordTrace tailWord_1159645 prefixEnd_1159645 44107798043201527207733 := by
  unfold tailWord_1159645
  simp only [CollatzResearch.WordTrace]
  refine ⟨42295727883811691443416389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28197151922541127628944259 42295727883811691443416389)
  ·
    refine ⟨7930448978214692145640573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42295727883811691443416389 7930448978214692145640573)
    ·
      refine ⟨2973918366830509554615215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7930448978214692145640573 2973918366830509554615215)
      ·
        refine ⟨4460877550245764331922823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2973918366830509554615215 4460877550245764331922823)
        ·
          refine ⟨6691316325368646497884235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4460877550245764331922823 6691316325368646497884235)
          ·
            refine ⟨10036974488052969746826353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691316325368646497884235 10036974488052969746826353)
            ·
              refine ⟨7527730866039727310119765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10036974488052969746826353 7527730866039727310119765)
              ·
                refine ⟨44107798043201527207733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7527730866039727310119765 44107798043201527207733)
                ·
                  rfl

theorem cell22_1159645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 9].length) (baseStart_1159645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159645 prefixEnd_1159645 := by exact prefixLift 1159645
  have htrace : WordTrace (prefixWord ++ tailWord_1159645) baseStart_1159645 baseEnd_1159645 := by
    simpa [prefixWord, tailWord_1159645, baseEnd_1159645] using wordTrace_append hprefix tailTrace_1159645
  have hstable : (prefixWord ++ tailWord_1159645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159645).length < 2 ^ (prefixWord ++ tailWord_1159645).sum := by decide
  have hdescent : baseEnd_1159645 < baseStart_1159645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159649 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_1159649 : Nat := 118140960795 + 1159649 * 2 ^ 59
def prefixEnd_1159649 : Nat := 4983230072969 + 3 ^ 40 * 1159649 * 2
def baseEnd_1159649 : Nat := 396971551670559067769585

theorem tailTrace_1159649 : CollatzResearch.WordTrace tailWord_1159649 prefixEnd_1159649 396971551670559067769585 := by
  unfold tailWord_1159649
  simp only [CollatzResearch.WordTrace]
  refine ⟨42295873775797200126562001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28197249183864800084374667 42295873775797200126562001)
  ·
    refine ⟨31721905331847900094921501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42295873775797200126562001 31721905331847900094921501)
    ·
      refine ⟨11895714499442962535595563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31721905331847900094921501 11895714499442962535595563)
      ·
        refine ⟨17843571749164443803393345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895714499442962535595563 17843571749164443803393345)
        ·
          refine ⟨13382678811873332852545009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17843571749164443803393345 13382678811873332852545009)
          ·
            refine ⟨10037009108904999639408757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13382678811873332852545009 10037009108904999639408757)
            ·
              refine ⟨940969603959843716194571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10037009108904999639408757 940969603959843716194571)
              ·
                refine ⟨1411454405939765574291857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940969603959843716194571 1411454405939765574291857)
                ·
                  refine ⟨1058590804454824180718893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411454405939765574291857 1058590804454824180718893)
                  ·
                    refine ⟨396971551670559067769585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058590804454824180718893 396971551670559067769585)
                    ·
                      rfl

theorem cell22_1159649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_1159649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159649 prefixEnd_1159649 := by exact prefixLift 1159649
  have htrace : WordTrace (prefixWord ++ tailWord_1159649) baseStart_1159649 baseEnd_1159649 := by
    simpa [prefixWord, tailWord_1159649, baseEnd_1159649] using wordTrace_append hprefix tailTrace_1159649
  have hstable : (prefixWord ++ tailWord_1159649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159649).length < 2 ^ (prefixWord ++ tailWord_1159649).sum := by decide
  have hdescent : baseEnd_1159649 < baseStart_1159649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159662 : List Nat := [4, 1, 2, 1, 2, 2, 4, 6]
def baseStart_1159662 : Nat := 118140960795 + 1159662 * 2 ^ 59
def prefixEnd_1159662 : Nat := 4983230072969 + 3 ^ 40 * 1159662 * 2
def baseEnd_1159662 : Nat := 44108444648470151910505

theorem tailTrace_1159662 : CollatzResearch.WordTrace tailWord_1159662 prefixEnd_1159662 44108444648470151910505 := by
  unfold tailWord_1159662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287043490593762918348155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28197565283166735564523493 5287043490593762918348155)
  ·
    refine ⟨7930565235890644377522233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287043490593762918348155 7930565235890644377522233)
    ·
      refine ⟨5947923926917983283141675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930565235890644377522233 5947923926917983283141675)
      ·
        refine ⟨8921885890376974924712513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5947923926917983283141675 8921885890376974924712513)
        ·
          refine ⟨6691414417782731193534385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8921885890376974924712513 6691414417782731193534385)
          ·
            refine ⟨5018560813337048395150789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6691414417782731193534385 5018560813337048395150789)
            ·
              refine ⟨940980152500696574090773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5018560813337048395150789 940980152500696574090773)
              ·
                refine ⟨44108444648470151910505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 940980152500696574090773 44108444648470151910505)
                ·
                  rfl

theorem cell22_1159662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_1159662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159662 prefixEnd_1159662 := by exact prefixLift 1159662
  have htrace : WordTrace (prefixWord ++ tailWord_1159662) baseStart_1159662 baseEnd_1159662 := by
    simpa [prefixWord, tailWord_1159662, baseEnd_1159662] using wordTrace_append hprefix tailTrace_1159662
  have hstable : (prefixWord ++ tailWord_1159662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159662).length < 2 ^ (prefixWord ++ tailWord_1159662).sum := by decide
  have hdescent : baseEnd_1159662 < baseStart_1159662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159690 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_1159690 : Nat := 118140960795 + 1159690 * 2 ^ 59
def prefixEnd_1159690 : Nat := 4983230072969 + 3 ^ 40 * 1159690 * 2
def baseEnd_1159690 : Nat := 132328528936149542498153

theorem tailTrace_1159690 : CollatzResearch.WordTrace tailWord_1159690 prefixEnd_1159690 132328528936149542498153 := by
  unfold tailWord_1159690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574342292162166032201131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28198246112432442752536349 10574342292162166032201131)
  ·
    refine ⟨15861513438243249048301697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10574342292162166032201131 15861513438243249048301697)
    ·
      refine ⟨11896135078682436786226273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15861513438243249048301697 11896135078682436786226273)
      ·
        refine ⟨8922101309011827589669705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11896135078682436786226273 8922101309011827589669705)
        ·
          refine ⟨6691575981758870692252279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8922101309011827589669705 6691575981758870692252279)
          ·
            refine ⟨10037363972638306038378419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6691575981758870692252279 10037363972638306038378419)
            ·
              refine ⟨15056045958957459057567629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10037363972638306038378419 15056045958957459057567629)
              ·
                refine ⟨5646017234609047146587861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15056045958957459057567629 5646017234609047146587861)
                ·
                  refine ⟨132328528936149542498153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5646017234609047146587861 132328528936149542498153)
                  ·
                    rfl

theorem cell22_1159690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_1159690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159690 prefixEnd_1159690 := by exact prefixLift 1159690
  have htrace : WordTrace (prefixWord ++ tailWord_1159690) baseStart_1159690 baseEnd_1159690 := by
    simpa [prefixWord, tailWord_1159690, baseEnd_1159690] using wordTrace_append hprefix tailTrace_1159690
  have hstable : (prefixWord ++ tailWord_1159690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159690).length < 2 ^ (prefixWord ++ tailWord_1159690).sum := by decide
  have hdescent : baseEnd_1159690 < baseStart_1159690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159694 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1159694 : Nat := 118140960795 + 1159694 * 2 ^ 59
def prefixEnd_1159694 : Nat := 4983230072969 + 3 ^ 40 * 1159694 * 2
def baseEnd_1159694 : Nat := 396986956090193950394447

theorem tailTrace_1159694 : CollatzResearch.WordTrace tailWord_1159694 prefixEnd_1159694 396986956090193950394447 := by
  unfold tailWord_1159694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287189382579271601493767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28198343373756115207966757 5287189382579271601493767)
  ·
    refine ⟨7930784073868907402240651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287189382579271601493767 7930784073868907402240651)
    ·
      refine ⟨11896176110803361103360977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930784073868907402240651 11896176110803361103360977)
      ·
        refine ⟨8922132083102520827520733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11896176110803361103360977 8922132083102520827520733)
        ·
          refine ⟨3345799531163445310320275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8922132083102520827520733 3345799531163445310320275)
          ·
            refine ⟨5018699296745167965480413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3345799531163445310320275 5018699296745167965480413)
            ·
              refine ⟨1882012236279437987055155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5018699296745167965480413 1882012236279437987055155)
              ·
                refine ⟨2823018354419156980582733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882012236279437987055155 2823018354419156980582733)
                ·
                  refine ⟨1058631882907183867718525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2823018354419156980582733 1058631882907183867718525)
                  ·
                    refine ⟨396986956090193950394447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058631882907183867718525 396986956090193950394447)
                    ·
                      rfl

theorem cell22_1159694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1159694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159694 prefixEnd_1159694 := by exact prefixLift 1159694
  have htrace : WordTrace (prefixWord ++ tailWord_1159694) baseStart_1159694 baseEnd_1159694 := by
    simpa [prefixWord, tailWord_1159694, baseEnd_1159694] using wordTrace_append hprefix tailTrace_1159694
  have hstable : (prefixWord ++ tailWord_1159694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159694).length < 2 ^ (prefixWord ++ tailWord_1159694).sum := by decide
  have hdescent : baseEnd_1159694 < baseStart_1159694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159767 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_1159767 : Nat := 118140960795 + 1159767 * 2 ^ 59
def prefixEnd_1159767 : Nat := 4983230072969 + 3 ^ 40 * 1159767 * 2
def baseEnd_1159767 : Nat := 397011945482046093319223

theorem tailTrace_1159767 : CollatzResearch.WordTrace tailWord_1159767 prefixEnd_1159767 397011945482046093319223 := by
  unfold tailWord_1159767
  simp only [CollatzResearch.WordTrace]
  refine ⟨42300177589369706279357555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28200118392913137519571703 42300177589369706279357555)
  ·
    refine ⟨63450266384054559419036333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42300177589369706279357555 63450266384054559419036333)
    ·
      refine ⟨23793849894020459782138625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63450266384054559419036333 23793849894020459782138625)
      ·
        refine ⟨17845387420515344836603969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23793849894020459782138625 17845387420515344836603969)
        ·
          refine ⟨13384040565386508627452977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17845387420515344836603969 13384040565386508627452977)
          ·
            refine ⟨10038030424039881470589733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13384040565386508627452977 10038030424039881470589733)
            ·
              refine ⟨1882130704507477775735575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10038030424039881470589733 1882130704507477775735575)
              ·
                refine ⟨2823196056761216663603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882130704507477775735575 2823196056761216663603363)
                ·
                  refine ⟨4234794085141824995405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823196056761216663603363 4234794085141824995405045)
                  ·
                    refine ⟨397011945482046093319223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4234794085141824995405045 397011945482046093319223)
                    ·
                      rfl

theorem cell22_1159767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_1159767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159767 prefixEnd_1159767 := by exact prefixLift 1159767
  have htrace : WordTrace (prefixWord ++ tailWord_1159767) baseStart_1159767 baseEnd_1159767 := by
    simpa [prefixWord, tailWord_1159767, baseEnd_1159767] using wordTrace_append hprefix tailTrace_1159767
  have hstable : (prefixWord ++ tailWord_1159767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159767).length < 2 ^ (prefixWord ++ tailWord_1159767).sum := by decide
  have hdescent : baseEnd_1159767 < baseStart_1159767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159801 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_1159801 : Nat := 118140960795 + 1159801 * 2 ^ 59
def prefixEnd_1159801 : Nat := 4983230072969 + 3 ^ 40 * 1159801 * 2
def baseEnd_1159801 : Nat := 397023584376881337969119

theorem tailTrace_1159801 : CollatzResearch.WordTrace tailWord_1159801 prefixEnd_1159801 397023584376881337969119 := by
  unfold tailWord_1159801
  simp only [CollatzResearch.WordTrace]
  refine ⟨42301417671246530086095257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28200945114164353390730171 42301417671246530086095257)
  ·
    refine ⟨31726063253434897564571443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42301417671246530086095257 31726063253434897564571443)
    ·
      refine ⟨47589094880152346346857165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31726063253434897564571443 47589094880152346346857165)
      ·
        refine ⟨17845910580057129880071437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47589094880152346346857165 17845910580057129880071437)
        ·
          refine ⟨6692216467521423705026789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17845910580057129880071437 6692216467521423705026789)
          ·
            refine ⟨1254790587660266944692523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6692216467521423705026789 1254790587660266944692523)
            ·
              refine ⟨1882185881490400417038785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254790587660266944692523 1882185881490400417038785)
              ·
                refine ⟨1411639411117800312779089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882185881490400417038785 1411639411117800312779089)
                ·
                  refine ⟨1058729558338350234584317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411639411117800312779089 1058729558338350234584317)
                  ·
                    refine ⟨397023584376881337969119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058729558338350234584317 397023584376881337969119)
                    ·
                      rfl

theorem cell22_1159801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_1159801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159801 prefixEnd_1159801 := by exact prefixLift 1159801
  have htrace : WordTrace (prefixWord ++ tailWord_1159801) baseStart_1159801 baseEnd_1159801 := by
    simpa [prefixWord, tailWord_1159801, baseEnd_1159801] using wordTrace_append hprefix tailTrace_1159801
  have hstable : (prefixWord ++ tailWord_1159801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159801).length < 2 ^ (prefixWord ++ tailWord_1159801).sum := by decide
  have hdescent : baseEnd_1159801 < baseStart_1159801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159818 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1159818 : Nat := 118140960795 + 1159818 * 2 ^ 59
def prefixEnd_1159818 : Nat := 4983230072969 + 3 ^ 40 * 1159818 * 2
def baseEnd_1159818 : Nat := 397029403824298960294067

theorem tailTrace_1159818 : CollatzResearch.WordTrace tailWord_1159818 prefixEnd_1159818 397029403824298960294067 := by
  unfold tailWord_1159818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10575509428046235497366027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28201358474789961326309405 10575509428046235497366027)
  ·
    refine ⟨15863264142069353246049041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10575509428046235497366027 15863264142069353246049041)
    ·
      refine ⟨11897448106552014934536781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15863264142069353246049041 11897448106552014934536781)
      ·
        refine ⟨4461543039957005600451293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11897448106552014934536781 4461543039957005600451293)
        ·
          refine ⟨1673078639983877100169235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4461543039957005600451293 1673078639983877100169235)
          ·
            refine ⟨2509617959975815650253853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673078639983877100169235 2509617959975815650253853)
            ·
              refine ⟨941106734990930868845195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2509617959975815650253853 941106734990930868845195)
              ·
                refine ⟨1411660102486396303267793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941106734990930868845195 1411660102486396303267793)
                ·
                  refine ⟨1058745076864797227450845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411660102486396303267793 1058745076864797227450845)
                  ·
                    refine ⟨397029403824298960294067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058745076864797227450845 397029403824298960294067)
                    ·
                      rfl

theorem cell22_1159818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1159818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159818 prefixEnd_1159818 := by exact prefixLift 1159818
  have htrace : WordTrace (prefixWord ++ tailWord_1159818) baseStart_1159818 baseEnd_1159818 := by
    simpa [prefixWord, tailWord_1159818, baseEnd_1159818] using wordTrace_append hprefix tailTrace_1159818
  have hstable : (prefixWord ++ tailWord_1159818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159818).length < 2 ^ (prefixWord ++ tailWord_1159818).sum := by decide
  have hdescent : baseEnd_1159818 < baseStart_1159818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159863 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 3, 3]
def baseStart_1159863 : Nat := 118140960795 + 1159863 * 2 ^ 59
def prefixEnd_1159863 : Nat := 4983230072969 + 3 ^ 40 * 1159863 * 2
def baseEnd_1159863 : Nat := 397044808243933842918929

theorem tailTrace_1159863 : CollatzResearch.WordTrace tailWord_1159863 prefixEnd_1159863 397044808243933842918929 := by
  unfold tailWord_1159863
  simp only [CollatzResearch.WordTrace]
  refine ⟨42303678997021914674852243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28202452664681276449901495 42303678997021914674852243)
  ·
    refine ⟨63455518495532872012278365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42303678997021914674852243 63455518495532872012278365)
    ·
      refine ⟨23795819435824827004604387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63455518495532872012278365 23795819435824827004604387)
      ·
        refine ⟨35693729153737240506906581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23795819435824827004604387 35693729153737240506906581)
        ·
          refine ⟨836571777040716574380623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35693729153737240506906581 836571777040716574380623)
          ·
            refine ⟨1254857665561074861570935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836571777040716574380623 1254857665561074861570935)
            ·
              refine ⟨1882286498341612292356403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254857665561074861570935 1882286498341612292356403)
              ·
                refine ⟨2823429747512418438534605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882286498341612292356403 2823429747512418438534605)
                ·
                  refine ⟨1058786155317156914450477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2823429747512418438534605 1058786155317156914450477)
                  ·
                    refine ⟨397044808243933842918929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058786155317156914450477 397044808243933842918929)
                    ·
                      rfl

theorem cell22_1159863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_1159863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159863 prefixEnd_1159863 := by exact prefixLift 1159863
  have htrace : WordTrace (prefixWord ++ tailWord_1159863) baseStart_1159863 baseEnd_1159863 := by
    simpa [prefixWord, tailWord_1159863, baseEnd_1159863] using wordTrace_append hprefix tailTrace_1159863
  have hstable : (prefixWord ++ tailWord_1159863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159863).length < 2 ^ (prefixWord ++ tailWord_1159863).sum := by decide
  have hdescent : baseEnd_1159863 < baseStart_1159863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159876 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1159876 : Nat := 118140960795 + 1159876 * 2 ^ 59
def prefixEnd_1159876 : Nat := 4983230072969 + 3 ^ 40 * 1159876 * 2
def baseEnd_1159876 : Nat := 132349752803202047447963

theorem tailTrace_1159876 : CollatzResearch.WordTrace tailWord_1159876 prefixEnd_1159876 132349752803202047447963 := by
  unfold tailWord_1159876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152076572987408947537741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28202768763983211930050321 21152076572987408947537741)
  ·
    refine ⟨7932028714870278355326653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21152076572987408947537741 7932028714870278355326653)
    ·
      refine ⟨2974510768076354383247495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7932028714870278355326653 2974510768076354383247495)
      ·
        refine ⟨4461766152114531574871243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974510768076354383247495 4461766152114531574871243)
        ·
          refine ⟨6692649228171797362306865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461766152114531574871243 6692649228171797362306865)
          ·
            refine ⟨5019486921128848021730149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6692649228171797362306865 5019486921128848021730149)
            ·
              refine ⟨941153797711659004074403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5019486921128848021730149 941153797711659004074403)
              ·
                refine ⟨1411730696567488506111605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941153797711659004074403 1411730696567488506111605)
                ·
                  refine ⟨132349752803202047447963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1411730696567488506111605 132349752803202047447963)
                  ·
                    rfl

theorem cell22_1159876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1159876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159876 prefixEnd_1159876 := by exact prefixLift 1159876
  have htrace : WordTrace (prefixWord ++ tailWord_1159876) baseStart_1159876 baseEnd_1159876 := by
    simpa [prefixWord, tailWord_1159876, baseEnd_1159876] using wordTrace_append hprefix tailTrace_1159876
  have hstable : (prefixWord ++ tailWord_1159876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159876).length < 2 ^ (prefixWord ++ tailWord_1159876).sum := by decide
  have hdescent : baseEnd_1159876 < baseStart_1159876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159904 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_1159904 : Nat := 118140960795 + 1159904 * 2 ^ 59
def prefixEnd_1159904 : Nat := 4983230072969 + 3 ^ 40 * 1159904 * 2
def baseEnd_1159904 : Nat := 132352947793941134214601

theorem tailTrace_1159904 : CollatzResearch.WordTrace tailWord_1159904 prefixEnd_1159904 132352947793941134214601 := by
  unfold tailWord_1159904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152587194936689338547383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28203449593248919118063177 21152587194936689338547383)
  ·
    refine ⟨31728880792405034007821075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21152587194936689338547383 31728880792405034007821075)
    ·
      refine ⟨47593321188607551011731613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31728880792405034007821075 47593321188607551011731613)
      ·
        refine ⟨17847495445727831629399355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47593321188607551011731613 17847495445727831629399355)
        ·
          refine ⟨26771243168591747444099033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17847495445727831629399355 26771243168591747444099033)
          ·
            refine ⟨20078432376443810583074275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26771243168591747444099033 20078432376443810583074275)
            ·
              refine ⟨30117648564665715874611413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20078432376443810583074275 30117648564665715874611413)
              ·
                refine ⟨705882388234352715811205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30117648564665715874611413 705882388234352715811205)
                ·
                  refine ⟨132352947793941134214601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 705882388234352715811205 132352947793941134214601)
                  ·
                    rfl

theorem cell22_1159904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_1159904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159904 prefixEnd_1159904 := by exact prefixLift 1159904
  have htrace : WordTrace (prefixWord ++ tailWord_1159904) baseStart_1159904 baseEnd_1159904 := by
    simpa [prefixWord, tailWord_1159904, baseEnd_1159904] using wordTrace_append hprefix tailTrace_1159904
  have hstable : (prefixWord ++ tailWord_1159904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159904).length < 2 ^ (prefixWord ++ tailWord_1159904).sum := by decide
  have hdescent : baseEnd_1159904 < baseStart_1159904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1159977 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 7]
def baseStart_1159977 : Nat := 118140960795 + 1159977 * 2 ^ 59
def prefixEnd_1159977 : Nat := 4983230072969 + 3 ^ 40 * 1159977 * 2
def baseEnd_1159977 : Nat := 132361277591225181856193

theorem tailTrace_1159977 : CollatzResearch.WordTrace tailWord_1159977 prefixEnd_1159977 132361277591225181856193 := by
  unfold tailWord_1159977
  simp only [CollatzResearch.WordTrace]
  refine ⟨42307836918608912144502185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28205224612405941429668123 42307836918608912144502185)
  ·
    refine ⟨31730877688956684108376639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42307836918608912144502185 31730877688956684108376639)
    ·
      refine ⟨47596316533435026162564959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31730877688956684108376639 47596316533435026162564959)
      ·
        refine ⟨71394474800152539243847439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47596316533435026162564959 71394474800152539243847439)
        ·
          refine ⟨107091712200228808865771159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71394474800152539243847439 107091712200228808865771159)
          ·
            refine ⟨160637568300343213298656739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107091712200228808865771159 160637568300343213298656739)
            ·
              refine ⟨240956352450514819947985109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160637568300343213298656739 240956352450514819947985109)
              ·
                refine ⟨5647414510558941092530901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 240956352450514819947985109 5647414510558941092530901)
                ·
                  refine ⟨132361277591225181856193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5647414510558941092530901 132361277591225181856193)
                  ·
                    rfl

theorem cell22_1159977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_1159977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1159977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1159977 prefixEnd_1159977 := by exact prefixLift 1159977
  have htrace : WordTrace (prefixWord ++ tailWord_1159977) baseStart_1159977 baseEnd_1159977 := by
    simpa [prefixWord, tailWord_1159977, baseEnd_1159977] using wordTrace_append hprefix tailTrace_1159977
  have hstable : (prefixWord ++ tailWord_1159977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1159977).length < 2 ^ (prefixWord ++ tailWord_1159977).sum := by decide
  have hdescent : baseEnd_1159977 < baseStart_1159977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1159977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160071 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1160071 : Nat := 118140960795 + 1160071 * 2 ^ 59
def prefixEnd_1160071 : Nat := 4983230072969 + 3 ^ 40 * 1160071 * 2
def baseEnd_1160071 : Nat := 397116010894690633718291

theorem tailTrace_1160071 : CollatzResearch.WordTrace tailWord_1160071 prefixEnd_1160071 397116010894690633718291 := by
  unfold tailWord_1160071
  simp only [CollatzResearch.WordTrace]
  refine ⟨42311265380268366198424067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28207510253512244132282711 42311265380268366198424067)
  ·
    refine ⟨63466898070402549297636101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42311265380268366198424067 63466898070402549297636101)
    ·
      refine ⟨11900043388200477993306769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63466898070402549297636101 11900043388200477993306769)
      ·
        refine ⟨8925032541150358494980077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11900043388200477993306769 8925032541150358494980077)
        ·
          refine ⟨3346887202931384435617529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8925032541150358494980077 3346887202931384435617529)
          ·
            refine ⟨2510165402198538326713147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3346887202931384435617529 2510165402198538326713147)
            ·
              refine ⟨3765248103297807490069721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510165402198538326713147 3765248103297807490069721)
              ·
                refine ⟨2823936077473355617552291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765248103297807490069721 2823936077473355617552291)
                ·
                  refine ⟨4235904116210033426328437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2823936077473355617552291 4235904116210033426328437)
                  ·
                    refine ⟨397116010894690633718291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4235904116210033426328437 397116010894690633718291)
                    ·
                      rfl

theorem cell22_1160071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1160071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160071 prefixEnd_1160071 := by exact prefixLift 1160071
  have htrace : WordTrace (prefixWord ++ tailWord_1160071) baseStart_1160071 baseEnd_1160071 := by
    simpa [prefixWord, tailWord_1160071, baseEnd_1160071] using wordTrace_append hprefix tailTrace_1160071
  have hstable : (prefixWord ++ tailWord_1160071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160071).length < 2 ^ (prefixWord ++ tailWord_1160071).sum := by decide
  have hdescent : baseEnd_1160071 < baseStart_1160071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160150 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1160150 : Nat := 118140960795 + 1160150 * 2 ^ 59
def prefixEnd_1160150 : Nat := 4983230072969 + 3 ^ 40 * 1160150 * 2
def baseEnd_1160150 : Nat := 397143054209160760993049

theorem tailTrace_1160150 : CollatzResearch.WordTrace tailWord_1160150 prefixEnd_1160150 397143054209160760993049 := by
  unfold tailWord_1160150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644634171686385168159369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28209431164654775127033269 2644634171686385168159369)
  ·
    refine ⟨1983475628764788876119527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2644634171686385168159369 1983475628764788876119527)
    ·
      refine ⟨2975213443147183314179291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983475628764788876119527 2975213443147183314179291)
      ·
        refine ⟨4462820164720774971268937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975213443147183314179291 4462820164720774971268937)
        ·
          refine ⟨3347115123540581228451703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4462820164720774971268937 3347115123540581228451703)
          ·
            refine ⟨5020672685310871842677555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347115123540581228451703 5020672685310871842677555)
            ·
              refine ⟨7531009027966307764016333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5020672685310871842677555 7531009027966307764016333)
              ·
                refine ⟨2824128385487365411506125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7531009027966307764016333 2824128385487365411506125)
                ·
                  refine ⟨1059048144557762029314797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2824128385487365411506125 1059048144557762029314797)
                  ·
                    refine ⟨397143054209160760993049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059048144557762029314797 397143054209160760993049)
                    ·
                      rfl

theorem cell22_1160150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1160150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160150 prefixEnd_1160150 := by exact prefixLift 1160150
  have htrace : WordTrace (prefixWord ++ tailWord_1160150) baseStart_1160150 baseEnd_1160150 := by
    simpa [prefixWord, tailWord_1160150, baseEnd_1160150] using wordTrace_append hprefix tailTrace_1160150
  have hstable : (prefixWord ++ tailWord_1160150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160150).length < 2 ^ (prefixWord ++ tailWord_1160150).sum := by decide
  have hdescent : baseEnd_1160150 < baseStart_1160150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160163 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 5]
def baseStart_1160163 : Nat := 118140960795 + 1160163 * 2 ^ 59
def prefixEnd_1160163 : Nat := 4983230072969 + 3 ^ 40 * 1160163 * 2
def baseEnd_1160163 : Nat := 132382501458277686806003

theorem tailTrace_1160163 : CollatzResearch.WordTrace tailWord_1160163 prefixEnd_1160163 132382501458277686806003 := by
  unfold tailWord_1160163
  simp only [CollatzResearch.WordTrace]
  refine ⟨42314620895935065910773143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28209747263956710607182095 42314620895935065910773143)
  ·
    refine ⟨63471931343902598866159715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42314620895935065910773143 63471931343902598866159715)
    ·
      refine ⟨95207897015853898299239573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63471931343902598866159715 95207897015853898299239573)
      ·
        refine ⟨4462870172618151482776855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95207897015853898299239573 4462870172618151482776855)
        ·
          refine ⟨6694305258927227224165283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4462870172618151482776855 6694305258927227224165283)
          ·
            refine ⟨10041457888390840836247925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6694305258927227224165283 10041457888390840836247925)
            ·
              refine ⟨941386677036641328398243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10041457888390840836247925 941386677036641328398243)
              ·
                refine ⟨1412080015554961992597365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941386677036641328398243 1412080015554961992597365)
                ·
                  refine ⟨132382501458277686806003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412080015554961992597365 132382501458277686806003)
                  ·
                    rfl

theorem cell22_1160163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 5].length) (baseStart_1160163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160163 prefixEnd_1160163 := by exact prefixLift 1160163
  have htrace : WordTrace (prefixWord ++ tailWord_1160163) baseStart_1160163 baseEnd_1160163 := by
    simpa [prefixWord, tailWord_1160163, baseEnd_1160163] using wordTrace_append hprefix tailTrace_1160163
  have hstable : (prefixWord ++ tailWord_1160163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160163).length < 2 ^ (prefixWord ++ tailWord_1160163).sum := by decide
  have hdescent : baseEnd_1160163 < baseStart_1160163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160193 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1160193 : Nat := 118140960795 + 1160193 * 2 ^ 59
def prefixEnd_1160193 : Nat := 4983230072969 + 3 ^ 40 * 1160193 * 2
def baseEnd_1160193 : Nat := 397157773987922982167917

theorem tailTrace_1160193 : CollatzResearch.WordTrace tailWord_1160193 prefixEnd_1160193 397157773987922982167917 := by
  unfold tailWord_1160193
  simp only [CollatzResearch.WordTrace]
  refine ⟨42315715085826381034365233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28210476723884254022910155 42315715085826381034365233)
  ·
    refine ⟨31736786314369785775773925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42315715085826381034365233 31736786314369785775773925)
    ·
      refine ⟨5950647433944334832957611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31736786314369785775773925 5950647433944334832957611)
      ·
        refine ⟨8925971150916502249436417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5950647433944334832957611 8925971150916502249436417)
        ·
          refine ⟨6694478363187376687077313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8925971150916502249436417 6694478363187376687077313)
          ·
            refine ⟨5020858772390532515307985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6694478363187376687077313 5020858772390532515307985)
            ·
              refine ⟨3765644079292899386480989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5020858772390532515307985 3765644079292899386480989)
              ·
                refine ⟨1412116529734837269930371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3765644079292899386480989 1412116529734837269930371)
                ·
                  refine ⟨2118174794602255904895557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412116529734837269930371 2118174794602255904895557)
                  ·
                    refine ⟨397157773987922982167917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2118174794602255904895557 397157773987922982167917)
                    ·
                      rfl

theorem cell22_1160193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1160193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160193 prefixEnd_1160193 := by exact prefixLift 1160193
  have htrace : WordTrace (prefixWord ++ tailWord_1160193) baseStart_1160193 baseEnd_1160193 := by
    simpa [prefixWord, tailWord_1160193, baseEnd_1160193] using wordTrace_append hprefix tailTrace_1160193
  have hstable : (prefixWord ++ tailWord_1160193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160193).length < 2 ^ (prefixWord ++ tailWord_1160193).sum := by decide
  have hdescent : baseEnd_1160193 < baseStart_1160193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160257 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1160257 : Nat := 118140960795 + 1160257 * 2 ^ 59
def prefixEnd_1160257 : Nat := 4983230072969 + 3 ^ 40 * 1160257 * 2
def baseEnd_1160257 : Nat := 397179682495848148567721

theorem tailTrace_1160257 : CollatzResearch.WordTrace tailWord_1160257 prefixEnd_1160257 397179682495848148567721 := by
  unfold tailWord_1160257
  simp only [CollatzResearch.WordTrace]
  refine ⟨42318049357594519964695025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28212032905063013309796683 42318049357594519964695025)
  ·
    refine ⟨31738537018195889973521269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42318049357594519964695025 31738537018195889973521269)
    ·
      refine ⟨2975487845455864685017619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31738537018195889973521269 2975487845455864685017619)
      ·
        refine ⟨4463231768183797027526429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2975487845455864685017619 4463231768183797027526429)
        ·
          refine ⟨1673711913068923885322411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4463231768183797027526429 1673711913068923885322411)
          ·
            refine ⟨2510567869603385827983617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673711913068923885322411 2510567869603385827983617)
            ·
              refine ⟨1882925902202539370987713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510567869603385827983617 1882925902202539370987713)
              ·
                refine ⟨1412194426651904528240785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882925902202539370987713 1412194426651904528240785)
                ·
                  refine ⟨1059145819988928396180589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412194426651904528240785 1059145819988928396180589)
                  ·
                    refine ⟨397179682495848148567721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059145819988928396180589 397179682495848148567721)
                    ·
                      rfl

theorem cell22_1160257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1160257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160257 prefixEnd_1160257 := by exact prefixLift 1160257
  have htrace : WordTrace (prefixWord ++ tailWord_1160257) baseStart_1160257 baseEnd_1160257 := by
    simpa [prefixWord, tailWord_1160257, baseEnd_1160257] using wordTrace_append hprefix tailTrace_1160257
  have hstable : (prefixWord ++ tailWord_1160257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160257).length < 2 ^ (prefixWord ++ tailWord_1160257).sum := by decide
  have hdescent : baseEnd_1160257 < baseStart_1160257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160266 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1160266 : Nat := 118140960795 + 1160266 * 2 ^ 59
def prefixEnd_1160266 : Nat := 4983230072969 + 3 ^ 40 * 1160266 * 2
def baseEnd_1160266 : Nat := 397182763379775125092693

theorem tailTrace_1160266 : CollatzResearch.WordTrace tailWord_1160266 prefixEnd_1160266 397182763379775125092693 := by
  unfold tailWord_1160266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10579594403640478625443163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28212251743041276334515101 10579594403640478625443163)
  ·
    refine ⟨15869391605460717938164745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10579594403640478625443163 15869391605460717938164745)
    ·
      refine ⟨11902043704095538453623559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15869391605460717938164745 11902043704095538453623559)
      ·
        refine ⟨17853065556143307680435339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11902043704095538453623559 17853065556143307680435339)
        ·
          refine ⟨26779598334214961520653009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17853065556143307680435339 26779598334214961520653009)
          ·
            refine ⟨20084698750661221140489757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26779598334214961520653009 20084698750661221140489757)
            ·
              refine ⟨7531762031497957927683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20084698750661221140489757 7531762031497957927683659)
              ·
                refine ⟨11297643047246936891525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7531762031497957927683659 11297643047246936891525489)
                ·
                  refine ⟨8473232285435202668644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11297643047246936891525489 8473232285435202668644117)
                  ·
                    refine ⟨397182763379775125092693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8473232285435202668644117 397182763379775125092693)
                    ·
                      rfl

theorem cell22_1160266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1160266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160266 prefixEnd_1160266 := by exact prefixLift 1160266
  have htrace : WordTrace (prefixWord ++ tailWord_1160266) baseStart_1160266 baseEnd_1160266 := by
    simpa [prefixWord, tailWord_1160266, baseEnd_1160266] using wordTrace_append hprefix tailTrace_1160266
  have hstable : (prefixWord ++ tailWord_1160266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160266).length < 2 ^ (prefixWord ++ tailWord_1160266).sum := by decide
  have hdescent : baseEnd_1160266 < baseStart_1160266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160268 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_1160268 : Nat := 118140960795 + 1160268 * 2 ^ 59
def prefixEnd_1160268 : Nat := 4983230072969 + 3 ^ 40 * 1160268 * 2
def baseEnd_1160268 : Nat := 397183448020647786542687

theorem tailTrace_1160268 : CollatzResearch.WordTrace tailWord_1160268 prefixEnd_1160268 397183448020647786542687 := by
  unfold tailWord_1160268
  simp only [CollatzResearch.WordTrace]
  refine ⟨21159225280277334421672729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28212300373703112562230305 21159225280277334421672729)
  ·
    refine ⟨15869418960208000816254547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21159225280277334421672729 15869418960208000816254547)
    ·
      refine ⟨23804128440312001224381821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15869418960208000816254547 23804128440312001224381821)
      ·
        refine ⟨8926548165117000459143183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23804128440312001224381821 8926548165117000459143183)
        ·
          refine ⟨13389822247675500688714775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8926548165117000459143183 13389822247675500688714775)
          ·
            refine ⟨20084733371513251033072163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13389822247675500688714775 20084733371513251033072163)
            ·
              refine ⟨30127100057269876549608245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20084733371513251033072163 30127100057269876549608245)
              ·
                refine ⟨2824415630369050926525773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30127100057269876549608245 2824415630369050926525773)
                ·
                  refine ⟨1059155861388394097447165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2824415630369050926525773 1059155861388394097447165)
                  ·
                    refine ⟨397183448020647786542687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059155861388394097447165 397183448020647786542687)
                    ·
                      rfl

theorem cell22_1160268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_1160268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160268 prefixEnd_1160268 := by exact prefixLift 1160268
  have htrace : WordTrace (prefixWord ++ tailWord_1160268) baseStart_1160268 baseEnd_1160268 := by
    simpa [prefixWord, tailWord_1160268, baseEnd_1160268] using wordTrace_append hprefix tailTrace_1160268
  have hstable : (prefixWord ++ tailWord_1160268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160268).length < 2 ^ (prefixWord ++ tailWord_1160268).sum := by decide
  have hdescent : baseEnd_1160268 < baseStart_1160268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160302 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1160302 : Nat := 118140960795 + 1160302 * 2 ^ 59
def prefixEnd_1160302 : Nat := 4983230072969 + 3 ^ 40 * 1160302 * 2
def baseEnd_1160302 : Nat := 397195086915483031192583

theorem tailTrace_1160302 : CollatzResearch.WordTrace tailWord_1160302 prefixEnd_1160302 397195086915483031192583 := by
  unfold tailWord_1160302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5289961330303936581260395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28213127094954328433388773 5289961330303936581260395)
  ·
    refine ⟨7934941995455904871890593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5289961330303936581260395 7934941995455904871890593)
    ·
      refine ⟨5951206496591928653917945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7934941995455904871890593 5951206496591928653917945)
      ·
        refine ⟨4463404872443946490438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5951206496591928653917945 4463404872443946490438459)
        ·
          refine ⟨6695107308665919735657689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4463404872443946490438459 6695107308665919735657689)
          ·
            refine ⟨5021330481499439801743267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695107308665919735657689 5021330481499439801743267)
            ·
              refine ⟨7531995722249159702614901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021330481499439801743267 7531995722249159702614901)
              ·
                refine ⟨706124598960858722120147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7531995722249159702614901 706124598960858722120147)
                ·
                  refine ⟨1059186898441288083180221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706124598960858722120147 1059186898441288083180221)
                  ·
                    refine ⟨397195086915483031192583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059186898441288083180221 397195086915483031192583)
                    ·
                      rfl

theorem cell22_1160302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1160302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160302 prefixEnd_1160302 := by exact prefixLift 1160302
  have htrace : WordTrace (prefixWord ++ tailWord_1160302) baseStart_1160302 baseEnd_1160302 := by
    simpa [prefixWord, tailWord_1160302, baseEnd_1160302] using wordTrace_append hprefix tailTrace_1160302
  have hstable : (prefixWord ++ tailWord_1160302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160302).length < 2 ^ (prefixWord ++ tailWord_1160302).sum := by decide
  have hdescent : baseEnd_1160302 < baseStart_1160302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160343 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 6]
def baseStart_1160343 : Nat := 118140960795 + 1160343 * 2 ^ 59
def prefixEnd_1160343 : Nat := 4983230072969 + 3 ^ 40 * 1160343 * 2
def baseEnd_1160343 : Nat := 132403040684457530305819

theorem tailTrace_1160343 : CollatzResearch.WordTrace tailWord_1160343 prefixEnd_1160343 132403040684457530305819 := by
  unfold tailWord_1160343
  simp only [CollatzResearch.WordTrace]
  refine ⟨42321186035282956652325683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28214124023521971101550455 42321186035282956652325683)
  ·
    refine ⟨63481779052924434978488525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42321186035282956652325683 63481779052924434978488525)
    ·
      refine ⟨23805667144846663116933197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63481779052924434978488525 23805667144846663116933197)
      ·
        refine ⟨8927125179317498668849949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23805667144846663116933197 8927125179317498668849949)
        ·
          refine ⟨3347671942244062000818731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8927125179317498668849949 3347671942244062000818731)
          ·
            refine ⟨5021507913366093001228097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347671942244062000818731 5021507913366093001228097)
            ·
              refine ⟨3766130935024569750921073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5021507913366093001228097 3766130935024569750921073)
              ·
                refine ⟨2824598201268427313190805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3766130935024569750921073 2824598201268427313190805)
                ·
                  refine ⟨132403040684457530305819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2824598201268427313190805 132403040684457530305819)
                  ·
                    rfl

theorem cell22_1160343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_1160343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160343 prefixEnd_1160343 := by exact prefixLift 1160343
  have htrace : WordTrace (prefixWord ++ tailWord_1160343) baseStart_1160343 baseEnd_1160343 := by
    simpa [prefixWord, tailWord_1160343, baseEnd_1160343] using wordTrace_append hprefix tailTrace_1160343
  have hstable : (prefixWord ++ tailWord_1160343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160343).length < 2 ^ (prefixWord ++ tailWord_1160343).sum := by decide
  have hdescent : baseEnd_1160343 < baseStart_1160343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160362 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1160362 : Nat := 118140960795 + 1160362 * 2 ^ 59
def prefixEnd_1160362 : Nat := 4983230072969 + 3 ^ 40 * 1160362 * 2
def baseEnd_1160362 : Nat := 397215626141662874692399

theorem tailTrace_1160362 : CollatzResearch.WordTrace tailWord_1160362 prefixEnd_1160362 397215626141662874692399 := by
  unfold tailWord_1160362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10580469755553530724316835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28214586014809415264844893 10580469755553530724316835)
  ·
    refine ⟨15870704633330296086475253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10580469755553530724316835 15870704633330296086475253)
    ·
      refine ⟨1487878559374715258107055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15870704633330296086475253 1487878559374715258107055)
      ·
        refine ⟨2231817839062072887160583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487878559374715258107055 2231817839062072887160583)
        ·
          refine ⟨3347726758593109330740875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231817839062072887160583 3347726758593109330740875)
          ·
            refine ⟨5021590137889663996111313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347726758593109330740875 5021590137889663996111313)
            ·
              refine ⟨3766192603417247997083485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5021590137889663996111313 3766192603417247997083485)
              ·
                refine ⟨1412322226281467998906307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766192603417247997083485 1412322226281467998906307)
                ·
                  refine ⟨2118483339422201998359461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412322226281467998906307 2118483339422201998359461)
                  ·
                    refine ⟨397215626141662874692399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2118483339422201998359461 397215626141662874692399)
                    ·
                      rfl

theorem cell22_1160362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1160362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160362 prefixEnd_1160362 := by exact prefixLift 1160362
  have htrace : WordTrace (prefixWord ++ tailWord_1160362) baseStart_1160362 baseEnd_1160362 := by
    simpa [prefixWord, tailWord_1160362, baseEnd_1160362] using wordTrace_append hprefix tailTrace_1160362
  have hstable : (prefixWord ++ tailWord_1160362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160362).length < 2 ^ (prefixWord ++ tailWord_1160362).sum := by decide
  have hdescent : baseEnd_1160362 < baseStart_1160362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160371 : List Nat := [1, 1, 1, 2, 3, 2, 12]
def baseStart_1160371 : Nat := 118140960795 + 1160371 * 2 ^ 59
def prefixEnd_1160371 : Nat := 4983230072969 + 3 ^ 40 * 1160371 * 2
def baseEnd_1160371 : Nat := 14711803963910735230273

theorem tailTrace_1160371 : CollatzResearch.WordTrace tailWord_1160371 prefixEnd_1160371 14711803963910735230273 := by
  unfold tailWord_1160371
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322207279181517434344967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28214804852787678289563311 42322207279181517434344967)
  ·
    refine ⟨63483310918772276151517451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42322207279181517434344967 63483310918772276151517451)
    ·
      refine ⟨95224966378158414227276177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63483310918772276151517451 95224966378158414227276177)
      ·
        refine ⟨71418724783618810670457133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95224966378158414227276177 71418724783618810670457133)
        ·
          refine ⟨26782021793857054001421425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71418724783618810670457133 26782021793857054001421425)
          ·
            refine ⟨20086516345392790501066069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26782021793857054001421425 20086516345392790501066069)
            ·
              refine ⟨14711803963910735230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 20086516345392790501066069 14711803963910735230273)
              ·
                rfl

theorem cell22_1160371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 12].length) (baseStart_1160371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160371 prefixEnd_1160371 := by exact prefixLift 1160371
  have htrace : WordTrace (prefixWord ++ tailWord_1160371) baseStart_1160371 baseEnd_1160371 := by
    simpa [prefixWord, tailWord_1160371, baseEnd_1160371] using wordTrace_append hprefix tailTrace_1160371
  have hstable : (prefixWord ++ tailWord_1160371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160371).length < 2 ^ (prefixWord ++ tailWord_1160371).sum := by decide
  have hdescent : baseEnd_1160371 < baseStart_1160371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160375 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 2, 3]
def baseStart_1160375 : Nat := 118140960795 + 1160375 * 2 ^ 59
def prefixEnd_1160375 : Nat := 4983230072969 + 3 ^ 40 * 1160375 * 2
def baseEnd_1160375 : Nat := 397220076307335174117359

theorem tailTrace_1160375 : CollatzResearch.WordTrace tailWord_1160375 prefixEnd_1160375 397220076307335174117359 := by
  unfold tailWord_1160375
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322353171167026117490579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28214902114111350744993719 42322353171167026117490579)
  ·
    refine ⟨63483529756750539176235869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42322353171167026117490579 63483529756750539176235869)
    ·
      refine ⟨23806323658781452191088451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63483529756750539176235869 23806323658781452191088451)
      ·
        refine ⟨35709485488172178286632677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23806323658781452191088451 35709485488172178286632677)
        ·
          refine ⟨6695528529032283428743627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35709485488172178286632677 6695528529032283428743627)
          ·
            refine ⟨10043292793548425143115441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6695528529032283428743627 10043292793548425143115441)
            ·
              refine ⟨7532469595161318857336581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10043292793548425143115441 7532469595161318857336581)
              ·
                refine ⟨1412338049092747285750609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7532469595161318857336581 1412338049092747285750609)
                ·
                  refine ⟨1059253536819560464312957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412338049092747285750609 1059253536819560464312957)
                  ·
                    refine ⟨397220076307335174117359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059253536819560464312957 397220076307335174117359)
                    ·
                      rfl

theorem cell22_1160375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_1160375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160375 prefixEnd_1160375 := by exact prefixLift 1160375
  have htrace : WordTrace (prefixWord ++ tailWord_1160375) baseStart_1160375 baseEnd_1160375 := by
    simpa [prefixWord, tailWord_1160375, baseEnd_1160375] using wordTrace_append hprefix tailTrace_1160375
  have hstable : (prefixWord ++ tailWord_1160375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160375).length < 2 ^ (prefixWord ++ tailWord_1160375).sum := by decide
  have hdescent : baseEnd_1160375 < baseStart_1160375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160377 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 4]
def baseStart_1160377 : Nat := 118140960795 + 1160377 * 2 ^ 59
def prefixEnd_1160377 : Nat := 4983230072969 + 3 ^ 40 * 1160377 * 2
def baseEnd_1160377 : Nat := 132406920316069278522451

theorem tailTrace_1160377 : CollatzResearch.WordTrace tailWord_1160377 prefixEnd_1160377 132406920316069278522451 := by
  unfold tailWord_1160377
  simp only [CollatzResearch.WordTrace]
  refine ⟨42322426117159780459063385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28214950744773186972708923 42322426117159780459063385)
  ·
    refine ⟨31741819587869835344297539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42322426117159780459063385 31741819587869835344297539)
    ·
      refine ⟨47612729381804753016446309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31741819587869835344297539 47612729381804753016446309)
      ·
        refine ⟨8927386759088391190583683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47612729381804753016446309 8927386759088391190583683)
        ·
          refine ⟨13391080138632586785875525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927386759088391190583683 13391080138632586785875525)
          ·
            refine ⟨2510827525993610022351661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13391080138632586785875525 2510827525993610022351661)
            ·
              refine ⟨941560322247603758381873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2510827525993610022351661 941560322247603758381873)
              ·
                refine ⟨706170241685702818786405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941560322247603758381873 706170241685702818786405)
                ·
                  refine ⟨132406920316069278522451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706170241685702818786405 132406920316069278522451)
                  ·
                    rfl

theorem cell22_1160377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_1160377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160377 prefixEnd_1160377 := by exact prefixLift 1160377
  have htrace : WordTrace (prefixWord ++ tailWord_1160377) baseStart_1160377 baseEnd_1160377 := by
    simpa [prefixWord, tailWord_1160377, baseEnd_1160377] using wordTrace_append hprefix tailTrace_1160377
  have hstable : (prefixWord ++ tailWord_1160377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160377).length < 2 ^ (prefixWord ++ tailWord_1160377).sum := by decide
  have hdescent : baseEnd_1160377 < baseStart_1160377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160392 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_1160392 : Nat := 118140960795 + 1160392 * 2 ^ 59
def prefixEnd_1160392 : Nat := 4983230072969 + 3 ^ 40 * 1160392 * 2
def baseEnd_1160392 : Nat := 397225895754752796442307

theorem tailTrace_1160392 : CollatzResearch.WordTrace tailWord_1160392 prefixEnd_1160392 397225895754752796442307 := by
  unfold tailWord_1160392
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161486606052719010429715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28215315474736958680572953 21161486606052719010429715)
  ·
    refine ⟨31742229909079078515644573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21161486606052719010429715 31742229909079078515644573)
    ·
      refine ⟨11903336215904654443366715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31742229909079078515644573 11903336215904654443366715)
      ·
        refine ⟨17855004323856981665050073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11903336215904654443366715 17855004323856981665050073)
        ·
          refine ⟨13391253242892736248787555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17855004323856981665050073 13391253242892736248787555)
          ·
            refine ⟨20086879864339104373181333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13391253242892736248787555 20086879864339104373181333)
            ·
              refine ⟨941572493640895517492875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20086879864339104373181333 941572493640895517492875)
              ·
                refine ⟨1412358740461343276239313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941572493640895517492875 1412358740461343276239313)
                ·
                  refine ⟨1059269055346007457179485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1412358740461343276239313 1059269055346007457179485)
                  ·
                    refine ⟨397225895754752796442307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059269055346007457179485 397225895754752796442307)
                    ·
                      rfl

theorem cell22_1160392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_1160392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160392 prefixEnd_1160392 := by exact prefixLift 1160392
  have htrace : WordTrace (prefixWord ++ tailWord_1160392) baseStart_1160392 baseEnd_1160392 := by
    simpa [prefixWord, tailWord_1160392, baseEnd_1160392] using wordTrace_append hprefix tailTrace_1160392
  have hstable : (prefixWord ++ tailWord_1160392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160392).length < 2 ^ (prefixWord ++ tailWord_1160392).sum := by decide
  have hdescent : baseEnd_1160392 < baseStart_1160392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160602 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_1160602 : Nat := 118140960795 + 1160602 * 2 ^ 59
def prefixEnd_1160602 : Nat := 4983230072969 + 3 ^ 40 * 1160602 * 2
def baseEnd_1160602 : Nat := 132432594348794082897221

theorem tailTrace_1160602 : CollatzResearch.WordTrace tailWord_1160602 prefixEnd_1160602 132432594348794082897221 := by
  unfold tailWord_1160602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10582658135336160971501015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28220421694229762590669373 10582658135336160971501015)
  ·
    refine ⟨15873987203004241457251523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10582658135336160971501015 15873987203004241457251523)
    ·
      refine ⟨23810980804506362185877285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15873987203004241457251523 23810980804506362185877285)
      ·
        refine ⟨4464558900844942909851991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23810980804506362185877285 4464558900844942909851991)
        ·
          refine ⟨6696838351267414364777987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464558900844942909851991 6696838351267414364777987)
          ·
            refine ⟨10045257526901121547166981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6696838351267414364777987 10045257526901121547166981)
            ·
              refine ⟨1883485786293960290093809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10045257526901121547166981 1883485786293960290093809)
              ·
                refine ⟨1412614339720470217570357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1883485786293960290093809 1412614339720470217570357)
                ·
                  refine ⟨132432594348794082897221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412614339720470217570357 132432594348794082897221)
                  ·
                    rfl

theorem cell22_1160602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_1160602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160602 prefixEnd_1160602 := by exact prefixLift 1160602
  have htrace : WordTrace (prefixWord ++ tailWord_1160602) baseStart_1160602 baseEnd_1160602 := by
    simpa [prefixWord, tailWord_1160602, baseEnd_1160602] using wordTrace_append hprefix tailTrace_1160602
  have hstable : (prefixWord ++ tailWord_1160602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160602).length < 2 ^ (prefixWord ++ tailWord_1160602).sum := by decide
  have hdescent : baseEnd_1160602 < baseStart_1160602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160677 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1160677 : Nat := 118140960795 + 1160677 * 2 ^ 59
def prefixEnd_1160677 : Nat := 4983230072969 + 3 ^ 40 * 1160677 * 2
def baseEnd_1160677 : Nat := 397323457079107053066433

theorem tailTrace_1160677 : CollatzResearch.WordTrace tailWord_1160677 prefixEnd_1160677 397323457079107053066433 := by
  unfold tailWord_1160677
  simp only [CollatzResearch.WordTrace]
  refine ⟨42333368016072931694984285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28222245344048621129989523 42333368016072931694984285)
  ·
    refine ⟨15875013006027349385619107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42333368016072931694984285 15875013006027349385619107)
    ·
      refine ⟨23812519509041024078428661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15875013006027349385619107 23812519509041024078428661)
      ·
        refine ⟨2232423703972596007352687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23812519509041024078428661 2232423703972596007352687)
        ·
          refine ⟨3348635555958894011029031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232423703972596007352687 3348635555958894011029031)
          ·
            refine ⟨5022953333938341016543547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348635555958894011029031 5022953333938341016543547)
            ·
              refine ⟨7534430000907511524815321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5022953333938341016543547 7534430000907511524815321)
              ·
                refine ⟨5650822500680633643611491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7534430000907511524815321 5650822500680633643611491)
                ·
                  refine ⟨8476233751020950465417237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5650822500680633643611491 8476233751020950465417237)
                  ·
                    refine ⟨397323457079107053066433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8476233751020950465417237 397323457079107053066433)
                    ·
                      rfl

theorem cell22_1160677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1160677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160677 prefixEnd_1160677 := by exact prefixLift 1160677
  have htrace : WordTrace (prefixWord ++ tailWord_1160677) baseStart_1160677 baseEnd_1160677 := by
    simpa [prefixWord, tailWord_1160677, baseEnd_1160677] using wordTrace_append hprefix tailTrace_1160677
  have hstable : (prefixWord ++ tailWord_1160677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160677).length < 2 ^ (prefixWord ++ tailWord_1160677).sum := by decide
  have hdescent : baseEnd_1160677 < baseStart_1160677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160679 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1160679 : Nat := 118140960795 + 1160679 * 2 ^ 59
def prefixEnd_1160679 : Nat := 4983230072969 + 3 ^ 40 * 1160679 * 2
def baseEnd_1160679 : Nat := 397324141719979714516427

theorem tailTrace_1160679 : CollatzResearch.WordTrace tailWord_1160679 prefixEnd_1160679 397324141719979714516427 := by
  unfold tailWord_1160679
  simp only [CollatzResearch.WordTrace]
  refine ⟨42333440962065686036557091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28222293974710457357704727 42333440962065686036557091)
  ·
    refine ⟨63500161443098529054835637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42333440962065686036557091 63500161443098529054835637)
    ·
      refine ⟨5953140135290487098890841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63500161443098529054835637 5953140135290487098890841)
      ·
        refine ⟨4464855101467865324168131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5953140135290487098890841 4464855101467865324168131)
        ·
          refine ⟨6697282652201797986252197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4464855101467865324168131 6697282652201797986252197)
          ·
            refine ⟨1255740497287837122422287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6697282652201797986252197 1255740497287837122422287)
            ·
              refine ⟨1883610745931755683633431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255740497287837122422287 1883610745931755683633431)
              ·
                refine ⟨2825416118897633525450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883610745931755683633431 2825416118897633525450147)
                ·
                  refine ⟨4238124178346450288175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2825416118897633525450147 4238124178346450288175221)
                  ·
                    refine ⟨397324141719979714516427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4238124178346450288175221 397324141719979714516427)
                    ·
                      rfl

theorem cell22_1160679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1160679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160679 prefixEnd_1160679 := by exact prefixLift 1160679
  have htrace : WordTrace (prefixWord ++ tailWord_1160679) baseStart_1160679 baseEnd_1160679 := by
    simpa [prefixWord, tailWord_1160679, baseEnd_1160679] using wordTrace_append hprefix tailTrace_1160679
  have hstable : (prefixWord ++ tailWord_1160679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160679).length < 2 ^ (prefixWord ++ tailWord_1160679).sum := by decide
  have hdescent : baseEnd_1160679 < baseStart_1160679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160775 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 1, 3]
def baseStart_1160775 : Nat := 118140960795 + 1160775 * 2 ^ 59
def prefixEnd_1160775 : Nat := 4983230072969 + 3 ^ 40 * 1160775 * 2
def baseEnd_1160775 : Nat := 397357004481867464116133

theorem tailTrace_1160775 : CollatzResearch.WordTrace tailWord_1160775 prefixEnd_1160775 397357004481867464116133 := by
  unfold tailWord_1160775
  simp only [CollatzResearch.WordTrace]
  refine ⟨42336942369717894432051779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28224628246478596288034519 42336942369717894432051779)
  ·
    refine ⟨63505413554576841648077669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42336942369717894432051779 63505413554576841648077669)
    ·
      refine ⟨11907265041483157809014563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63505413554576841648077669 11907265041483157809014563)
      ·
        refine ⟨17860897562224736713521845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907265041483157809014563 17860897562224736713521845)
        ·
          refine ⟨1674459146458569066892673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17860897562224736713521845 1674459146458569066892673)
          ·
            refine ⟨1255844359843926800169505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674459146458569066892673 1255844359843926800169505)
            ·
              refine ⟨941883269882945100127129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255844359843926800169505 941883269882945100127129)
              ·
                refine ⟨706412452412208825095347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941883269882945100127129 706412452412208825095347)
                ·
                  refine ⟨1059618678618313237643021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706412452412208825095347 1059618678618313237643021)
                  ·
                    refine ⟨397357004481867464116133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059618678618313237643021 397357004481867464116133)
                    ·
                      rfl

theorem cell22_1160775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_1160775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160775 prefixEnd_1160775 := by exact prefixLift 1160775
  have htrace : WordTrace (prefixWord ++ tailWord_1160775) baseStart_1160775 baseEnd_1160775 := by
    simpa [prefixWord, tailWord_1160775, baseEnd_1160775] using wordTrace_append hprefix tailTrace_1160775
  have hstable : (prefixWord ++ tailWord_1160775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160775).length < 2 ^ (prefixWord ++ tailWord_1160775).sum := by decide
  have hdescent : baseEnd_1160775 < baseStart_1160775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160782 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1160782 : Nat := 118140960795 + 1160782 * 2 ^ 59
def prefixEnd_1160782 : Nat := 4983230072969 + 3 ^ 40 * 1160782 * 2
def baseEnd_1160782 : Nat := 132453133574973926397037

theorem tailTrace_1160782 : CollatzResearch.WordTrace tailWord_1160782 prefixEnd_1160782 132453133574973926397037 := by
  unfold tailWord_1160782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292149710086566828444575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28224798453795023085037733 5292149710086566828444575)
  ·
    refine ⟨7938224565129850242666863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292149710086566828444575 7938224565129850242666863)
    ·
      refine ⟨11907336847694775364000295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938224565129850242666863 11907336847694775364000295)
      ·
        refine ⟨17861005271542163046000443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11907336847694775364000295 17861005271542163046000443)
        ·
          refine ⟨26791507907313244569000665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17861005271542163046000443 26791507907313244569000665)
          ·
            refine ⟨20093630930484933426750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26791507907313244569000665 20093630930484933426750499)
            ·
              refine ⟨30140446395727400140125749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20093630930484933426750499 30140446395727400140125749)
              ·
                refine ⟨2825666849599443763136789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30140446395727400140125749 2825666849599443763136789)
                ·
                  refine ⟨132453133574973926397037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2825666849599443763136789 132453133574973926397037)
                  ·
                    rfl

theorem cell22_1160782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1160782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160782 prefixEnd_1160782 := by exact prefixLift 1160782
  have htrace : WordTrace (prefixWord ++ tailWord_1160782) baseStart_1160782 baseEnd_1160782 := by
    simpa [prefixWord, tailWord_1160782, baseEnd_1160782] using wordTrace_append hprefix tailTrace_1160782
  have hstable : (prefixWord ++ tailWord_1160782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160782).length < 2 ^ (prefixWord ++ tailWord_1160782).sum := by decide
  have hdescent : baseEnd_1160782 < baseStart_1160782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160816 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_1160816 : Nat := 118140960795 + 1160816 * 2 ^ 59
def prefixEnd_1160816 : Nat := 4983230072969 + 3 ^ 40 * 1160816 * 2
def baseEnd_1160816 : Nat := 132457013206585674613669

theorem tailTrace_1160816 : CollatzResearch.WordTrace tailWord_1160816 prefixEnd_1160816 132457013206585674613669 := by
  unfold tailWord_1160816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21169218881284679217147151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28225625175046238956196201 21169218881284679217147151)
  ·
    refine ⟨31753828321927018825720727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21169218881284679217147151 31753828321927018825720727)
    ·
      refine ⟨47630742482890528238581091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31753828321927018825720727 47630742482890528238581091)
      ·
        refine ⟨71446113724335792357871637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47630742482890528238581091 71446113724335792357871637)
        ·
          refine ⟨3349036580828240266775233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71446113724335792357871637 3349036580828240266775233)
          ·
            refine ⟨2511777435621180200081425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349036580828240266775233 2511777435621180200081425)
            ·
              refine ⟨1883833076715885150061069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511777435621180200081425 1883833076715885150061069)
              ·
                refine ⟨706437403768456931272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1883833076715885150061069 706437403768456931272901)
                ·
                  refine ⟨132457013206585674613669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706437403768456931272901 132457013206585674613669)
                  ·
                    rfl

theorem cell22_1160816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_1160816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160816 prefixEnd_1160816 := by exact prefixLift 1160816
  have htrace : WordTrace (prefixWord ++ tailWord_1160816) baseStart_1160816 baseEnd_1160816 := by
    simpa [prefixWord, tailWord_1160816, baseEnd_1160816] using wordTrace_append hprefix tailTrace_1160816
  have hstable : (prefixWord ++ tailWord_1160816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160816).length < 2 ^ (prefixWord ++ tailWord_1160816).sum := by decide
  have hdescent : baseEnd_1160816 < baseStart_1160816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160818 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_1160818 : Nat := 118140960795 + 1160818 * 2 ^ 59
def prefixEnd_1160818 : Nat := 4983230072969 + 3 ^ 40 * 1160818 * 2
def baseEnd_1160818 : Nat := 397371724260629685291001

theorem tailTrace_1160818 : CollatzResearch.WordTrace tailWord_1160818 prefixEnd_1160818 397371724260629685291001 := by
  unfold tailWord_1160818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10584627677140528193966777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28225673805708075183911405 10584627677140528193966777)
  ·
    refine ⟨7938470757855396145475083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10584627677140528193966777 7938470757855396145475083)
    ·
      refine ⟨11907706136783094218212625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7938470757855396145475083 11907706136783094218212625)
      ·
        refine ⟨8930779602587320663659469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11907706136783094218212625 8930779602587320663659469)
        ·
          refine ⟨3349042350970245248872301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8930779602587320663659469 3349042350970245248872301)
          ·
            refine ⟨1255890881613841968327113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3349042350970245248872301 1255890881613841968327113)
            ·
              refine ⟨941918161210381476245335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255890881613841968327113 941918161210381476245335)
              ·
                refine ⟨1412877241815572214368003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941918161210381476245335 1412877241815572214368003)
                ·
                  refine ⟨2119315862723358321552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412877241815572214368003 2119315862723358321552005)
                  ·
                    refine ⟨397371724260629685291001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119315862723358321552005 397371724260629685291001)
                    ·
                      rfl

theorem cell22_1160818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_1160818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160818 prefixEnd_1160818 := by exact prefixLift 1160818
  have htrace : WordTrace (prefixWord ++ tailWord_1160818) baseStart_1160818 baseEnd_1160818 := by
    simpa [prefixWord, tailWord_1160818, baseEnd_1160818] using wordTrace_append hprefix tailTrace_1160818
  have hstable : (prefixWord ++ tailWord_1160818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160818).length < 2 ^ (prefixWord ++ tailWord_1160818).sum := by decide
  have hdescent : baseEnd_1160818 < baseStart_1160818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160878 : List Nat := [4, 1, 4, 1, 3, 1, 8]
def baseStart_1160878 : Nat := 118140960795 + 1160878 * 2 ^ 59
def prefixEnd_1160878 : Nat := 4983230072969 + 3 ^ 40 * 1160878 * 2
def baseEnd_1160878 : Nat := 14718231980992945510771

theorem tailTrace_1160878 : CollatzResearch.WordTrace tailWord_1160878 prefixEnd_1160878 14718231980992945510771 := by
  unfold tailWord_1160878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292587386043092877881411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28227132725563162015367525 5292587386043092877881411)
  ·
    refine ⟨7938881079064639316822117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5292587386043092877881411 7938881079064639316822117)
    ·
      refine ⟨1488540202324619871904147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7938881079064639316822117 1488540202324619871904147)
      ·
        refine ⟨2232810303486929807856221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488540202324619871904147 2232810303486929807856221)
        ·
          refine ⟨837303863807598677946083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2232810303486929807856221 837303863807598677946083)
          ·
            refine ⟨1255955795711398016919125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837303863807598677946083 1255955795711398016919125)
            ·
              refine ⟨14718231980992945510771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1255955795711398016919125 14718231980992945510771)
              ·
                rfl

theorem cell22_1160878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 8].length) (baseStart_1160878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160878 prefixEnd_1160878 := by exact prefixLift 1160878
  have htrace : WordTrace (prefixWord ++ tailWord_1160878) baseStart_1160878 baseEnd_1160878 := by
    simpa [prefixWord, tailWord_1160878, baseEnd_1160878] using wordTrace_append hprefix tailTrace_1160878
  have hstable : (prefixWord ++ tailWord_1160878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160878).length < 2 ^ (prefixWord ++ tailWord_1160878).sum := by decide
  have hdescent : baseEnd_1160878 < baseStart_1160878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160906 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_1160906 : Nat := 118140960795 + 1160906 * 2 ^ 59
def prefixEnd_1160906 : Nat := 4983230072969 + 3 ^ 40 * 1160906 * 2
def baseEnd_1160906 : Nat := 132467282819675596363577

theorem tailTrace_1160906 : CollatzResearch.WordTrace tailWord_1160906 prefixEnd_1160906 132467282819675596363577 := by
  unfold tailWord_1160906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10585430083060825951267643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28227813554828869203380381 10585430083060825951267643)
  ·
    refine ⟨15878145124591238926901465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10585430083060825951267643 15878145124591238926901465)
    ·
      refine ⟨11908608843443429195176099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15878145124591238926901465 11908608843443429195176099)
      ·
        refine ⟨17862913265165143792764149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11908608843443429195176099 17862913265165143792764149)
        ·
          refine ⟨1674648118609232230571639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17862913265165143792764149 1674648118609232230571639)
          ·
            refine ⟨2511972177913848345857459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674648118609232230571639 2511972177913848345857459)
            ·
              refine ⟨3767958266870772518786189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511972177913848345857459 3767958266870772518786189)
              ·
                refine ⟨1412984350076539694544821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3767958266870772518786189 1412984350076539694544821)
                ·
                  refine ⟨132467282819675596363577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1412984350076539694544821 132467282819675596363577)
                  ·
                    rfl

theorem cell22_1160906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_1160906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160906 prefixEnd_1160906 := by exact prefixLift 1160906
  have htrace : WordTrace (prefixWord ++ tailWord_1160906) baseStart_1160906 baseEnd_1160906 := by
    simpa [prefixWord, tailWord_1160906, baseEnd_1160906] using wordTrace_append hprefix tailTrace_1160906
  have hstable : (prefixWord ++ tailWord_1160906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160906).length < 2 ^ (prefixWord ++ tailWord_1160906).sum := by decide
  have hdescent : baseEnd_1160906 < baseStart_1160906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160919 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1160919 : Nat := 118140960795 + 1160919 * 2 ^ 59
def prefixEnd_1160919 : Nat := 4983230072969 + 3 ^ 40 * 1160919 * 2
def baseEnd_1160919 : Nat := 397406298624699088515691

theorem tailTrace_1160919 : CollatzResearch.WordTrace tailWord_1160919 prefixEnd_1160919 397406298624699088515691 := by
  unfold tailWord_1160919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42342194481196207025293811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28228129654130804683529207 42342194481196207025293811)
  ·
    refine ⟨63513291721794310537940717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42342194481196207025293811 63513291721794310537940717)
    ·
      refine ⟨23817484395672866451727769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63513291721794310537940717 23817484395672866451727769)
      ·
        refine ⟨17863113296754649838795827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23817484395672866451727769 17863113296754649838795827)
        ·
          refine ⟨26794669945131974758193741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17863113296754649838795827 26794669945131974758193741)
          ·
            refine ⟨10048001229424490534322653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26794669945131974758193741 10048001229424490534322653)
            ·
              refine ⟨3768000461034183950370995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10048001229424490534322653 3768000461034183950370995)
              ·
                refine ⟨5652000691551275925556493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768000461034183950370995 5652000691551275925556493)
                ·
                  refine ⟨2119500259331728472083685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5652000691551275925556493 2119500259331728472083685)
                  ·
                    refine ⟨397406298624699088515691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119500259331728472083685 397406298624699088515691)
                    ·
                      rfl

theorem cell22_1160919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1160919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160919 prefixEnd_1160919 := by exact prefixLift 1160919
  have htrace : WordTrace (prefixWord ++ tailWord_1160919) baseStart_1160919 baseEnd_1160919 := by
    simpa [prefixWord, tailWord_1160919, baseEnd_1160919] using wordTrace_append hprefix tailTrace_1160919
  have hstable : (prefixWord ++ tailWord_1160919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160919).length < 2 ^ (prefixWord ++ tailWord_1160919).sum := by decide
  have hdescent : baseEnd_1160919 < baseStart_1160919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1160981 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1160981 : Nat := 118140960795 + 1160981 * 2 ^ 59
def prefixEnd_1160981 : Nat := 4983230072969 + 3 ^ 40 * 1160981 * 2
def baseEnd_1160981 : Nat := 397427522491751593465501

theorem tailTrace_1160981 : CollatzResearch.WordTrace tailWord_1160981 prefixEnd_1160981 397427522491751593465501 := by
  unfold tailWord_1160981
  simp only [CollatzResearch.WordTrace]
  refine ⟨42344455806971591614050797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28229637204647727742700531 42344455806971591614050797)
  ·
    refine ⟨15879170927614346855269049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42344455806971591614050797 15879170927614346855269049)
    ·
      refine ⟨11909378195710760141451787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15879170927614346855269049 11909378195710760141451787)
      ·
        refine ⟨17864067293566140212177681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11909378195710760141451787 17864067293566140212177681)
        ·
          refine ⟨13398050470174605159133261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17864067293566140212177681 13398050470174605159133261)
          ·
            refine ⟨5024268926315476934674973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13398050470174605159133261 5024268926315476934674973)
            ·
              refine ⟨1884100847368303850503115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5024268926315476934674973 1884100847368303850503115)
              ·
                refine ⟨2826151271052455775754673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884100847368303850503115 2826151271052455775754673)
                ·
                  refine ⟨2119613453289341831816005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826151271052455775754673 2119613453289341831816005)
                  ·
                    refine ⟨397427522491751593465501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119613453289341831816005 397427522491751593465501)
                    ·
                      rfl

theorem cell22_1160981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1160981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1160981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1160981 prefixEnd_1160981 := by exact prefixLift 1160981
  have htrace : WordTrace (prefixWord ++ tailWord_1160981) baseStart_1160981 baseEnd_1160981 := by
    simpa [prefixWord, tailWord_1160981, baseEnd_1160981] using wordTrace_append hprefix tailTrace_1160981
  have hstable : (prefixWord ++ tailWord_1160981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1160981).length < 2 ^ (prefixWord ++ tailWord_1160981).sum := by decide
  have hdescent : baseEnd_1160981 < baseStart_1160981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1160981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161000 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1161000 : Nat := 118140960795 + 1161000 * 2 ^ 59
def prefixEnd_1161000 : Nat := 4983230072969 + 3 ^ 40 * 1161000 * 2
def baseEnd_1161000 : Nat := 397434026580041877240443

theorem tailTrace_1161000 : CollatzResearch.WordTrace tailWord_1161000 prefixEnd_1161000 397434026580041877240443 := by
  unfold tailWord_1161000
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172574396951378929496227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28230099195935171905994969 21172574396951378929496227)
  ·
    refine ⟨31758861595427068394244341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172574396951378929496227 31758861595427068394244341)
    ·
      refine ⟨2977393274571287661960407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31758861595427068394244341 2977393274571287661960407)
      ·
        refine ⟨4466089911856931492940611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2977393274571287661960407 4466089911856931492940611)
        ·
          refine ⟨6699134867785397239410917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466089911856931492940611 6699134867785397239410917)
          ·
            refine ⟨1256087787709761982389547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6699134867785397239410917 1256087787709761982389547)
            ·
              refine ⟨1884131681564642973584321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256087787709761982389547 1884131681564642973584321)
              ·
                refine ⟨1413098761173482230188241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1884131681564642973584321 1413098761173482230188241)
                ·
                  refine ⟨1059824070880111672641181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413098761173482230188241 1059824070880111672641181)
                  ·
                    refine ⟨397434026580041877240443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059824070880111672641181 397434026580041877240443)
                    ·
                      rfl

theorem cell22_1161000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1161000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161000 prefixEnd_1161000 := by exact prefixLift 1161000
  have htrace : WordTrace (prefixWord ++ tailWord_1161000) baseStart_1161000 baseEnd_1161000 := by
    simpa [prefixWord, tailWord_1161000, baseEnd_1161000] using wordTrace_append hprefix tailTrace_1161000
  have hstable : (prefixWord ++ tailWord_1161000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161000).length < 2 ^ (prefixWord ++ tailWord_1161000).sum := by decide
  have hdescent : baseEnd_1161000 < baseStart_1161000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161017 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_1161017 : Nat := 118140960795 + 1161017 * 2 ^ 59
def prefixEnd_1161017 : Nat := 4983230072969 + 3 ^ 40 * 1161017 * 2
def baseEnd_1161017 : Nat := 397439846027459499565391

theorem tailTrace_1161017 : CollatzResearch.WordTrace tailWord_1161017 prefixEnd_1161017 397439846027459499565391 := by
  unfold tailWord_1161017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42345768834841169762361305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28230512556560779841574203 42345768834841169762361305)
  ·
    refine ⟨31759326626130877321770979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42345768834841169762361305 31759326626130877321770979)
    ·
      refine ⟨47638989939196315982656469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31759326626130877321770979 47638989939196315982656469)
      ·
        refine ⟨1116538826699913655843511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47638989939196315982656469 1116538826699913655843511)
        ·
          refine ⟨1674808240049870483765267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116538826699913655843511 1674808240049870483765267)
          ·
            refine ⟨2512212360074805725647901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674808240049870483765267 2512212360074805725647901)
            ·
              refine ⟨942079635028052147117963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2512212360074805725647901 942079635028052147117963)
              ·
                refine ⟨1413119452542078220676945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942079635028052147117963 1413119452542078220676945)
                ·
                  refine ⟨1059839589406558665507709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1413119452542078220676945 1059839589406558665507709)
                  ·
                    refine ⟨397439846027459499565391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059839589406558665507709 397439846027459499565391)
                    ·
                      rfl

theorem cell22_1161017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_1161017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161017 prefixEnd_1161017 := by exact prefixLift 1161017
  have htrace : WordTrace (prefixWord ++ tailWord_1161017) baseStart_1161017 baseEnd_1161017 := by
    simpa [prefixWord, tailWord_1161017, baseEnd_1161017] using wordTrace_append hprefix tailTrace_1161017
  have hstable : (prefixWord ++ tailWord_1161017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161017).length < 2 ^ (prefixWord ++ tailWord_1161017).sum := by decide
  have hdescent : baseEnd_1161017 < baseStart_1161017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161030 : List Nat := [6, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1161030 : Nat := 118140960795 + 1161030 * 2 ^ 59
def prefixEnd_1161030 : Nat := 4983230072969 + 3 ^ 40 * 1161030 * 2
def baseEnd_1161030 : Nat := 44160477354792422110039

theorem tailTrace_1161030 : CollatzResearch.WordTrace tailWord_1161030 prefixEnd_1161030 44160477354792422110039 := by
  unfold tailWord_1161030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323320093243564780705767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28230828655862715321723029 1323320093243564780705767)
  ·
    refine ⟨1984980139865347171058651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323320093243564780705767 1984980139865347171058651)
    ·
      refine ⟨2977470209798020756587977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984980139865347171058651 2977470209798020756587977)
      ·
        refine ⟨2233102657348515567440983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977470209798020756587977 2233102657348515567440983)
        ·
          refine ⟨3349653986022773351161475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233102657348515567440983 3349653986022773351161475)
          ·
            refine ⟨5024480979034160026742213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3349653986022773351161475 5024480979034160026742213)
            ·
              refine ⟨942090183568905005014165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5024480979034160026742213 942090183568905005014165)
              ·
                refine ⟨44160477354792422110039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 942090183568905005014165 44160477354792422110039)
                ·
                  rfl

theorem cell22_1161030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1161030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161030 prefixEnd_1161030 := by exact prefixLift 1161030
  have htrace : WordTrace (prefixWord ++ tailWord_1161030) baseStart_1161030 baseEnd_1161030 := by
    simpa [prefixWord, tailWord_1161030, baseEnd_1161030] using wordTrace_append hprefix tailTrace_1161030
  have hstable : (prefixWord ++ tailWord_1161030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161030).length < 2 ^ (prefixWord ++ tailWord_1161030).sum := by decide
  have hdescent : baseEnd_1161030 < baseStart_1161030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161045 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 1, 3]
def baseStart_1161045 : Nat := 118140960795 + 1161045 * 2 ^ 59
def prefixEnd_1161045 : Nat := 4983230072969 + 3 ^ 40 * 1161045 * 2
def baseEnd_1161045 : Nat := 397449430999676759865305

theorem tailTrace_1161045 : CollatzResearch.WordTrace tailWord_1161045 prefixEnd_1161045 397449430999676759865305 := by
  unfold tailWord_1161045
  simp only [CollatzResearch.WordTrace]
  refine ⟨42346790078739730544380589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28231193385826487029587059 42346790078739730544380589)
  ·
    refine ⟨15880046279527398954142721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42346790078739730544380589 15880046279527398954142721)
    ·
      refine ⟨11910034709645549215607041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15880046279527398954142721 11910034709645549215607041)
      ·
        refine ⟨8932526032234161911705281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11910034709645549215607041 8932526032234161911705281)
        ·
          refine ⟨6699394524175621433778961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8932526032234161911705281 6699394524175621433778961)
          ·
            refine ⟨5024545893131716075334221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6699394524175621433778961 5024545893131716075334221)
            ·
              refine ⟨1884204709924393528250333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5024545893131716075334221 1884204709924393528250333)
              ·
                refine ⟨706576766221647573093875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1884204709924393528250333 706576766221647573093875)
                ·
                  refine ⟨1059865149332471359640813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706576766221647573093875 1059865149332471359640813)
                  ·
                    refine ⟨397449430999676759865305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059865149332471359640813 397449430999676759865305)
                    ·
                      rfl

theorem cell22_1161045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_1161045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161045 prefixEnd_1161045 := by exact prefixLift 1161045
  have htrace : WordTrace (prefixWord ++ tailWord_1161045) baseStart_1161045 baseEnd_1161045 := by
    simpa [prefixWord, tailWord_1161045, baseEnd_1161045] using wordTrace_append hprefix tailTrace_1161045
  have hstable : (prefixWord ++ tailWord_1161045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161045).length < 2 ^ (prefixWord ++ tailWord_1161045).sum := by decide
  have hdescent : baseEnd_1161045 < baseStart_1161045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161150 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1161150 : Nat := 118140960795 + 1161150 * 2 ^ 59
def prefixEnd_1161150 : Nat := 4983230072969 + 3 ^ 40 * 1161150 * 2
def baseEnd_1161150 : Nat := 397485374645491485989983

theorem tailTrace_1161150 : CollatzResearch.WordTrace tailWord_1161150 prefixEnd_1161150 397485374645491485989983 := by
  unfold tailWord_1161150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293827467919916684619113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28233746495572888984635269 5293827467919916684619113)
  ·
    refine ⟨3970370600939937513464335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5293827467919916684619113 3970370600939937513464335)
    ·
      refine ⟨5955555901409906270196503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970370600939937513464335 5955555901409906270196503)
      ·
        refine ⟨8933333852114859405294755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955555901409906270196503 8933333852114859405294755)
        ·
          refine ⟨13400000778172289107942133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8933333852114859405294755 13400000778172289107942133)
          ·
            refine ⟨1256250072953652103869575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13400000778172289107942133 1256250072953652103869575)
            ·
              refine ⟨1884375109430478155804363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256250072953652103869575 1884375109430478155804363)
              ·
                refine ⟨2826562664145717233706545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1884375109430478155804363 2826562664145717233706545)
                ·
                  refine ⟨2119921998109287925279909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2826562664145717233706545 2119921998109287925279909)
                  ·
                    refine ⟨397485374645491485989983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2119921998109287925279909 397485374645491485989983)
                    ·
                      rfl

theorem cell22_1161150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1161150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161150 prefixEnd_1161150 := by exact prefixLift 1161150
  have htrace : WordTrace (prefixWord ++ tailWord_1161150) baseStart_1161150 baseEnd_1161150 := by
    simpa [prefixWord, tailWord_1161150, baseEnd_1161150] using wordTrace_append hprefix tailTrace_1161150
  have hstable : (prefixWord ++ tailWord_1161150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161150).length < 2 ^ (prefixWord ++ tailWord_1161150).sum := by decide
  have hdescent : baseEnd_1161150 < baseStart_1161150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161176 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_1161176 : Nat := 118140960795 + 1161176 * 2 ^ 59
def prefixEnd_1161176 : Nat := 4983230072969 + 3 ^ 40 * 1161176 * 2
def baseEnd_1161176 : Nat := 132498091658945361613301

theorem tailTrace_1161176 : CollatzResearch.WordTrace tailWord_1161176 prefixEnd_1161176 132498091658945361613301 := by
  unfold tailWord_1161176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21175784020632569958699691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28234378694176759944932921 21175784020632569958699691)
  ·
    refine ⟨31763676030948854938049537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21175784020632569958699691 31763676030948854938049537)
    ·
      refine ⟨23822757023211641203537153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31763676030948854938049537 23822757023211641203537153)
      ·
        refine ⟨17867067767408730902652865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23822757023211641203537153 17867067767408730902652865)
        ·
          refine ⟨13400300825556548176989649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17867067767408730902652865 13400300825556548176989649)
          ·
            refine ⟨10050225619167411132742237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13400300825556548176989649 10050225619167411132742237)
            ·
              refine ⟨3768834607187779174778339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10050225619167411132742237 3768834607187779174778339)
              ·
                refine ⟨5653251910781668762167509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3768834607187779174778339 5653251910781668762167509)
                ·
                  refine ⟨132498091658945361613301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5653251910781668762167509 132498091658945361613301)
                  ·
                    rfl

theorem cell22_1161176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_1161176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161176 prefixEnd_1161176 := by exact prefixLift 1161176
  have htrace : WordTrace (prefixWord ++ tailWord_1161176) baseStart_1161176 baseEnd_1161176 := by
    simpa [prefixWord, tailWord_1161176, baseEnd_1161176] using wordTrace_append hprefix tailTrace_1161176
  have hstable : (prefixWord ++ tailWord_1161176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161176).length < 2 ^ (prefixWord ++ tailWord_1161176).sum := by decide
  have hdescent : baseEnd_1161176 < baseStart_1161176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161214 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1161214 : Nat := 118140960795 + 1161214 * 2 ^ 59
def prefixEnd_1161214 : Nat := 4983230072969 + 3 ^ 40 * 1161214 * 2
def baseEnd_1161214 : Nat := 397507283153416652389787

theorem tailTrace_1161214 : CollatzResearch.WordTrace tailWord_1161214 prefixEnd_1161214 397507283153416652389787 := by
  unfold tailWord_1161214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294119251890934050910337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28235302676751648271521797 5294119251890934050910337)
  ·
    refine ⟨3970589438918200538182753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5294119251890934050910337 3970589438918200538182753)
    ·
      refine ⟨2977942079188650403637065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3970589438918200538182753 2977942079188650403637065)
      ·
        refine ⟨2233456559391487802727799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977942079188650403637065 2233456559391487802727799)
        ·
          refine ⟨3350184839087231704091699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233456559391487802727799 3350184839087231704091699)
          ·
            refine ⟨5025277258630847556137549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350184839087231704091699 5025277258630847556137549)
            ·
              refine ⟨1884478971986567833551581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5025277258630847556137549 1884478971986567833551581)
              ·
                refine ⟨706679614494962937581843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1884478971986567833551581 706679614494962937581843)
                ·
                  refine ⟨1060019421742444406372765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706679614494962937581843 1060019421742444406372765)
                  ·
                    refine ⟨397507283153416652389787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060019421742444406372765 397507283153416652389787)
                    ·
                      rfl

theorem cell22_1161214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1161214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161214 prefixEnd_1161214 := by exact prefixLift 1161214
  have htrace : WordTrace (prefixWord ++ tailWord_1161214) baseStart_1161214 baseEnd_1161214 := by
    simpa [prefixWord, tailWord_1161214, baseEnd_1161214] using wordTrace_append hprefix tailTrace_1161214
  have hstable : (prefixWord ++ tailWord_1161214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161214).length < 2 ^ (prefixWord ++ tailWord_1161214).sum := by decide
  have hdescent : baseEnd_1161214 < baseStart_1161214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161270 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1161270 : Nat := 118140960795 + 1161270 * 2 ^ 59
def prefixEnd_1161270 : Nat := 4983230072969 + 3 ^ 40 * 1161270 * 2
def baseEnd_1161270 : Nat := 397526453097851172989615

theorem tailTrace_1161270 : CollatzResearch.WordTrace tailWord_1161270 prefixEnd_1161270 397526453097851172989615 := by
  unfold tailWord_1161270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647187281432787123207579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28236664335283062647547509 2647187281432787123207579)
  ·
    refine ⟨3970780922149180684811369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2647187281432787123207579 3970780922149180684811369)
    ·
      refine ⟨2978085691611885513608527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3970780922149180684811369 2978085691611885513608527)
      ·
        refine ⟨4467128537417828270412791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978085691611885513608527 4467128537417828270412791)
        ·
          refine ⟨6700692806126742405619187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467128537417828270412791 6700692806126742405619187)
          ·
            refine ⟨10051039209190113608428781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6700692806126742405619187 10051039209190113608428781)
            ·
              refine ⟨3769139703446292603160793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10051039209190113608428781 3769139703446292603160793)
              ·
                refine ⟨2826854777584719452370595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769139703446292603160793 2826854777584719452370595)
                ·
                  refine ⟨4240282166377079178555893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2826854777584719452370595 4240282166377079178555893)
                  ·
                    refine ⟨397526453097851172989615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4240282166377079178555893 397526453097851172989615)
                    ·
                      rfl

theorem cell22_1161270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1161270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161270 prefixEnd_1161270 := by exact prefixLift 1161270
  have htrace : WordTrace (prefixWord ++ tailWord_1161270) baseStart_1161270 baseEnd_1161270 := by
    simpa [prefixWord, tailWord_1161270, baseEnd_1161270] using wordTrace_append hprefix tailTrace_1161270
  have hstable : (prefixWord ++ tailWord_1161270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161270).length < 2 ^ (prefixWord ++ tailWord_1161270).sum := by decide
  have hdescent : baseEnd_1161270 < baseStart_1161270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161345 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 7]
def baseStart_1161345 : Nat := 118140960795 + 1161345 * 2 ^ 59
def prefixEnd_1161345 : Nat := 4983230072969 + 3 ^ 40 * 1161345 * 2
def baseEnd_1161345 : Nat := 132517375710191992454795

theorem tailTrace_1161345 : CollatzResearch.WordTrace tailWord_1161345 prefixEnd_1161345 132517375710191992454795 := by
  unfold tailWord_1161345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42357731977652881780301489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28238487985101921186867659 42357731977652881780301489)
  ·
    refine ⟨31768298983239661335226117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42357731977652881780301489 31768298983239661335226117)
    ·
      refine ⟨5956556059357436500354897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31768298983239661335226117 5956556059357436500354897)
      ·
        refine ⟨4467417044518077375266173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5956556059357436500354897 4467417044518077375266173)
        ·
          refine ⟨1675281391694279015724815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4467417044518077375266173 1675281391694279015724815)
          ·
            refine ⟨2512922087541418523587223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675281391694279015724815 2512922087541418523587223)
            ·
              refine ⟨3769383131312127785380835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512922087541418523587223 3769383131312127785380835)
              ·
                refine ⟨5654074696968191678071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3769383131312127785380835 5654074696968191678071253)
                ·
                  refine ⟨132517375710191992454795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5654074696968191678071253 132517375710191992454795)
                  ·
                    rfl

theorem cell22_1161345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_1161345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161345 prefixEnd_1161345 := by exact prefixLift 1161345
  have htrace : WordTrace (prefixWord ++ tailWord_1161345) baseStart_1161345 baseEnd_1161345 := by
    simpa [prefixWord, tailWord_1161345, baseEnd_1161345] using wordTrace_append hprefix tailTrace_1161345
  have hstable : (prefixWord ++ tailWord_1161345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161345).length < 2 ^ (prefixWord ++ tailWord_1161345).sum := by decide
  have hdescent : baseEnd_1161345 < baseStart_1161345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161362 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1161362 : Nat := 118140960795 + 1161362 * 2 ^ 59
def prefixEnd_1161362 : Nat := 4983230072969 + 3 ^ 40 * 1161362 * 2
def baseEnd_1161362 : Nat := 132519315525997866563111

theorem tailTrace_1161362 : CollatzResearch.WordTrace tailWord_1161362 prefixEnd_1161362 132519315525997866563111 := by
  unfold tailWord_1161362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589588004647823420917585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28238901345727529122446893 10589588004647823420917585)
  ·
    refine ⟨7942191003485867565688189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10589588004647823420917585 7942191003485867565688189)
    ·
      refine ⟨2978321626307200337133071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7942191003485867565688189 2978321626307200337133071)
      ·
        refine ⟨4467482439460800505699607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2978321626307200337133071 4467482439460800505699607)
        ·
          refine ⟨6701223659191200758549411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467482439460800505699607 6701223659191200758549411)
          ·
            refine ⟨10051835488786801137824117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6701223659191200758549411 10051835488786801137824117)
            ·
              refine ⟨942359577073762606671011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10051835488786801137824117 942359577073762606671011)
              ·
                refine ⟨1413539365610643910006517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942359577073762606671011 1413539365610643910006517)
                ·
                  refine ⟨132519315525997866563111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413539365610643910006517 132519315525997866563111)
                  ·
                    rfl

theorem cell22_1161362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1161362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161362 prefixEnd_1161362 := by exact prefixLift 1161362
  have htrace : WordTrace (prefixWord ++ tailWord_1161362) baseStart_1161362 baseEnd_1161362 := by
    simpa [prefixWord, tailWord_1161362, baseEnd_1161362] using wordTrace_append hprefix tailTrace_1161362
  have hstable : (prefixWord ++ tailWord_1161362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161362).length < 2 ^ (prefixWord ++ tailWord_1161362).sum := by decide
  have hdescent : baseEnd_1161362 < baseStart_1161362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161383 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1161383 : Nat := 118140960795 + 1161383 * 2 ^ 59
def prefixEnd_1161383 : Nat := 4983230072969 + 3 ^ 40 * 1161383 * 2
def baseEnd_1161383 : Nat := 397565135307156544914269

theorem tailTrace_1161383 : CollatzResearch.WordTrace tailWord_1161383 prefixEnd_1161383 397565135307156544914269 := by
  unfold tailWord_1161383
  simp only [CollatzResearch.WordTrace]
  refine ⟨42359117951515214270184803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28239411967676809513456535 42359117951515214270184803)
  ·
    refine ⟨63538676927272821405277205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42359117951515214270184803 63538676927272821405277205)
    ·
      refine ⟨2978375480965913503372369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63538676927272821405277205 2978375480965913503372369)
      ·
        refine ⟨2233781610724435127529277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978375480965913503372369 2233781610724435127529277)
        ·
          refine ⟨837668104021663172823479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2233781610724435127529277 837668104021663172823479)
          ·
            refine ⟨1256502156032494759235219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837668104021663172823479 1256502156032494759235219)
            ·
              refine ⟨1884753234048742138852829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1256502156032494759235219 1884753234048742138852829)
              ·
                refine ⟨706782462768278302069811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1884753234048742138852829 706782462768278302069811)
                ·
                  refine ⟨1060173694152417453104717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706782462768278302069811 1060173694152417453104717)
                  ·
                    refine ⟨397565135307156544914269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060173694152417453104717 397565135307156544914269)
                    ·
                      rfl

theorem cell22_1161383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1161383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161383 prefixEnd_1161383 := by exact prefixLift 1161383
  have htrace : WordTrace (prefixWord ++ tailWord_1161383) baseStart_1161383 baseEnd_1161383 := by
    simpa [prefixWord, tailWord_1161383, baseEnd_1161383] using wordTrace_append hprefix tailTrace_1161383
  have hstable : (prefixWord ++ tailWord_1161383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161383).length < 2 ^ (prefixWord ++ tailWord_1161383).sum := by decide
  have hdescent : baseEnd_1161383 < baseStart_1161383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161433 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1161433 : Nat := 118140960795 + 1161433 * 2 ^ 59
def prefixEnd_1161433 : Nat := 4983230072969 + 3 ^ 40 * 1161433 * 2
def baseEnd_1161433 : Nat := 397582251328973081164115

theorem tailTrace_1161433 : CollatzResearch.WordTrace tailWord_1161433 prefixEnd_1161433 397582251328973081164115 := by
  unfold tailWord_1161433
  simp only [CollatzResearch.WordTrace]
  refine ⟨42360941601334072809504953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28240627734222715206336635 42360941601334072809504953)
  ·
    refine ⟨31770706201000554607128715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42360941601334072809504953 31770706201000554607128715)
    ·
      refine ⟨47656059301500831910693073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31770706201000554607128715 47656059301500831910693073)
      ·
        refine ⟨35742044476125623933019805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47656059301500831910693073 35742044476125623933019805)
        ·
          refine ⟨13403266678547108974882427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35742044476125623933019805 13403266678547108974882427)
          ·
            refine ⟨20104900017820663462323641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13403266678547108974882427 20104900017820663462323641)
            ·
              refine ⟨15078675013365497596742731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20104900017820663462323641 15078675013365497596742731)
              ·
                refine ⟨22618012520048246395114097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15078675013365497596742731 22618012520048246395114097)
                ·
                  refine ⟨16963509390036184796335573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22618012520048246395114097 16963509390036184796335573)
                  ·
                    refine ⟨397582251328973081164115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16963509390036184796335573 397582251328973081164115)
                    ·
                      rfl

theorem cell22_1161433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1161433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161433 prefixEnd_1161433 := by exact prefixLift 1161433
  have htrace : WordTrace (prefixWord ++ tailWord_1161433) baseStart_1161433 baseEnd_1161433 := by
    simpa [prefixWord, tailWord_1161433, baseEnd_1161433] using wordTrace_append hprefix tailTrace_1161433
  have hstable : (prefixWord ++ tailWord_1161433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161433).length < 2 ^ (prefixWord ++ tailWord_1161433).sum := by decide
  have hdescent : baseEnd_1161433 < baseStart_1161433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161437 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1161437 : Nat := 118140960795 + 1161437 * 2 ^ 59
def prefixEnd_1161437 : Nat := 4983230072969 + 3 ^ 40 * 1161437 * 2
def baseEnd_1161437 : Nat := 397583620610718404064103

theorem tailTrace_1161437 : CollatzResearch.WordTrace tailWord_1161437 prefixEnd_1161437 397583620610718404064103 := by
  unfold tailWord_1161437
  simp only [CollatzResearch.WordTrace]
  refine ⟨42361087493319581492650565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28240724995546387661767043 42361087493319581492650565)
  ·
    refine ⟨7942703904997421529871981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42361087493319581492650565 7942703904997421529871981)
    ·
      refine ⟨2978513964374033073701993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7942703904997421529871981 2978513964374033073701993)
      ·
        refine ⟨2233885473280524805276495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978513964374033073701993 2233885473280524805276495)
        ·
          refine ⟨3350828209920787207914743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233885473280524805276495 3350828209920787207914743)
          ·
            refine ⟨5026242314881180811872115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3350828209920787207914743 5026242314881180811872115)
            ·
              refine ⟨7539363472321771217808173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026242314881180811872115 7539363472321771217808173)
              ·
                refine ⟨2827261302120664206678065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7539363472321771217808173 2827261302120664206678065)
                ·
                  refine ⟨2120445976590498155008549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827261302120664206678065 2120445976590498155008549)
                  ·
                    refine ⟨397583620610718404064103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120445976590498155008549 397583620610718404064103)
                    ·
                      rfl

theorem cell22_1161437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1161437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161437 prefixEnd_1161437 := by exact prefixLift 1161437
  have htrace : WordTrace (prefixWord ++ tailWord_1161437) baseStart_1161437 baseEnd_1161437 := by
    simpa [prefixWord, tailWord_1161437, baseEnd_1161437] using wordTrace_append hprefix tailTrace_1161437
  have hstable : (prefixWord ++ tailWord_1161437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161437).length < 2 ^ (prefixWord ++ tailWord_1161437).sum := by decide
  have hdescent : baseEnd_1161437 < baseStart_1161437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161572 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1161572 : Nat := 118140960795 + 1161572 * 2 ^ 59
def prefixEnd_1161572 : Nat := 4983230072969 + 3 ^ 40 * 1161572 * 2
def baseEnd_1161572 : Nat := 397629833869623051938689

theorem tailTrace_1161572 : CollatzResearch.WordTrace tailWord_1161572 prefixEnd_1161572 397629833869623051938689 := by
  unfold tailWord_1161572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183005673915249774407485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28244007565220333032543313 21183005673915249774407485)
  ·
    refine ⟨7943627127718218665402807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21183005673915249774407485 7943627127718218665402807)
    ·
      refine ⟨11915440691577327998104211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7943627127718218665402807 11915440691577327998104211)
      ·
        refine ⟨17873161037365991997156317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11915440691577327998104211 17873161037365991997156317)
        ·
          refine ⟨6702435389012246998933619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17873161037365991997156317 6702435389012246998933619)
          ·
            refine ⟨10053653083518370498400429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702435389012246998933619 10053653083518370498400429)
            ·
              refine ⟨3770119906319388936900161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10053653083518370498400429 3770119906319388936900161)
              ·
                refine ⟨2827589929739541702675121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770119906319388936900161 2827589929739541702675121)
                ·
                  refine ⟨2120692447304656277006341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2827589929739541702675121 2120692447304656277006341)
                  ·
                    refine ⟨397629833869623051938689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120692447304656277006341 397629833869623051938689)
                    ·
                      rfl

theorem cell22_1161572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1161572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161572 prefixEnd_1161572 := by exact prefixLift 1161572
  have htrace : WordTrace (prefixWord ++ tailWord_1161572) baseStart_1161572 baseEnd_1161572 := by
    simpa [prefixWord, tailWord_1161572, baseEnd_1161572] using wordTrace_append hprefix tailTrace_1161572
  have hstable : (prefixWord ++ tailWord_1161572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161572).length < 2 ^ (prefixWord ++ tailWord_1161572).sum := by decide
  have hdescent : baseEnd_1161572 < baseStart_1161572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161576 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_1161576 : Nat := 118140960795 + 1161576 * 2 ^ 59
def prefixEnd_1161576 : Nat := 4983230072969 + 3 ^ 40 * 1161576 * 2
def baseEnd_1161576 : Nat := 132543734383789458279559

theorem tailTrace_1161576 : CollatzResearch.WordTrace tailWord_1161576 prefixEnd_1161576 132543734383789458279559 := by
  unfold tailWord_1161576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183078619908004115980291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28244104826544005487973721 21183078619908004115980291)
  ·
    refine ⟨31774617929862006173970437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21183078619908004115980291 31774617929862006173970437)
    ·
      refine ⟨5957740861849126157619457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31774617929862006173970437 5957740861849126157619457)
      ·
        refine ⟨4468305646386844618214593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5957740861849126157619457 4468305646386844618214593)
        ·
          refine ⟨3351229234790133463660945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4468305646386844618214593 3351229234790133463660945)
          ·
            refine ⟨2513421926092600097745709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351229234790133463660945 2513421926092600097745709)
            ·
              refine ⟨942533222284725036654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513421926092600097745709 942533222284725036654641)
              ·
                refine ⟨706899916713543777490981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942533222284725036654641 706899916713543777490981)
                ·
                  refine ⟨132543734383789458279559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 706899916713543777490981 132543734383789458279559)
                  ·
                    rfl

theorem cell22_1161576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_1161576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161576 prefixEnd_1161576 := by exact prefixLift 1161576
  have htrace : WordTrace (prefixWord ++ tailWord_1161576) baseStart_1161576 baseEnd_1161576 := by
    simpa [prefixWord, tailWord_1161576, baseEnd_1161576] using wordTrace_append hprefix tailTrace_1161576
  have hstable : (prefixWord ++ tailWord_1161576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161576).length < 2 ^ (prefixWord ++ tailWord_1161576).sum := by decide
  have hdescent : baseEnd_1161576 < baseStart_1161576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161632 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_1161632 : Nat := 118140960795 + 1161632 * 2 ^ 59
def prefixEnd_1161632 : Nat := 4983230072969 + 3 ^ 40 * 1161632 * 2
def baseEnd_1161632 : Nat := 132550124365267631812835

theorem tailTrace_1161632 : CollatzResearch.WordTrace tailWord_1161632 prefixEnd_1161632 132550124365267631812835 := by
  unfold tailWord_1161632
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184099863806564897999575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28245466485075419863999433 21184099863806564897999575)
  ·
    refine ⟨31776149795709847346999363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21184099863806564897999575 31776149795709847346999363)
    ·
      refine ⟨47664224693564771020499045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31776149795709847346999363 47664224693564771020499045)
      ·
        refine ⟨8937042130043394566343571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47664224693564771020499045 8937042130043394566343571)
        ·
          refine ⟨13405563195065091849515357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8937042130043394566343571 13405563195065091849515357)
          ·
            refine ⟨5027086198149409443568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13405563195065091849515357 5027086198149409443568259)
            ·
              refine ⟨7540629297224114165352389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027086198149409443568259 7540629297224114165352389)
              ·
                refine ⟨1413867993229521406003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7540629297224114165352389 1413867993229521406003573)
                ·
                  refine ⟨132550124365267631812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1413867993229521406003573 132550124365267631812835)
                  ·
                    rfl

theorem cell22_1161632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_1161632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161632 prefixEnd_1161632 := by exact prefixLift 1161632
  have htrace : WordTrace (prefixWord ++ tailWord_1161632) baseStart_1161632 baseEnd_1161632 := by
    simpa [prefixWord, tailWord_1161632, baseEnd_1161632] using wordTrace_append hprefix tailTrace_1161632
  have hstable : (prefixWord ++ tailWord_1161632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161632).length < 2 ^ (prefixWord ++ tailWord_1161632).sum := by decide
  have hdescent : baseEnd_1161632 < baseStart_1161632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161760 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_1161760 : Nat := 118140960795 + 1161760 * 2 ^ 59
def prefixEnd_1161760 : Nat := 4983230072969 + 3 ^ 40 * 1161760 * 2
def baseEnd_1161760 : Nat := 397694190111653228238113

theorem tailTrace_1161760 : CollatzResearch.WordTrace tailWord_1161760 prefixEnd_1161760 397694190111653228238113 := by
  unfold tailWord_1161760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21186434135574703828329367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28248578847432938437772489 21186434135574703828329367)
  ·
    refine ⟨31779651203362055742494051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21186434135574703828329367 31779651203362055742494051)
    ·
      refine ⟨47669476805043083613741077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31779651203362055742494051 47669476805043083613741077)
      ·
        refine ⟨2234506725236394544394113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47669476805043083613741077 2234506725236394544394113)
        ·
          refine ⟨1675880043927295908295585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2234506725236394544394113 1675880043927295908295585)
          ·
            refine ⟨1256910032945471931221689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1675880043927295908295585 1256910032945471931221689)
            ·
              refine ⟨942682524709103948416267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256910032945471931221689 942682524709103948416267)
              ·
                refine ⟨1414023787063655922624401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942682524709103948416267 1414023787063655922624401)
                ·
                  refine ⟨1060517840297741941968301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414023787063655922624401 1060517840297741941968301)
                  ·
                    refine ⟨397694190111653228238113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060517840297741941968301 397694190111653228238113)
                    ·
                      rfl

theorem cell22_1161760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_1161760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161760 prefixEnd_1161760 := by exact prefixLift 1161760
  have htrace : WordTrace (prefixWord ++ tailWord_1161760) baseStart_1161760 baseEnd_1161760 := by
    simpa [prefixWord, tailWord_1161760, baseEnd_1161760] using wordTrace_append hprefix tailTrace_1161760
  have hstable : (prefixWord ++ tailWord_1161760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161760).length < 2 ^ (prefixWord ++ tailWord_1161760).sum := by decide
  have hdescent : baseEnd_1161760 < baseStart_1161760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161805 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1161805 : Nat := 118140960795 + 1161805 * 2 ^ 59
def prefixEnd_1161805 : Nat := 4983230072969 + 3 ^ 40 * 1161805 * 2
def baseEnd_1161805 : Nat := 397709594531288110862975

theorem tailTrace_1161805 : CollatzResearch.WordTrace tailWord_1161805 prefixEnd_1161805 397709594531288110862975 := by
  unfold tailWord_1161805
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374509555986380342046869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28249673037324253561364579 42374509555986380342046869)
  ·
    refine ⟨1986305135436861578533447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42374509555986380342046869 1986305135436861578533447)
    ·
      refine ⟨2979457703155292367800171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1986305135436861578533447 2979457703155292367800171)
      ·
        refine ⟨4469186554732938551700257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979457703155292367800171 4469186554732938551700257)
        ·
          refine ⟨3351889916049703913775193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4469186554732938551700257 3351889916049703913775193)
          ·
            refine ⟨2513917437037277935331395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351889916049703913775193 2513917437037277935331395)
            ·
              refine ⟨3770876155555916902997093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513917437037277935331395 3770876155555916902997093)
              ·
                refine ⟨707039279166734419311955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3770876155555916902997093 707039279166734419311955)
                ·
                  refine ⟨1060558918750101628967933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707039279166734419311955 1060558918750101628967933)
                  ·
                    refine ⟨397709594531288110862975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060558918750101628967933 397709594531288110862975)
                    ·
                      rfl

theorem cell22_1161805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1161805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161805 prefixEnd_1161805 := by exact prefixLift 1161805
  have htrace : WordTrace (prefixWord ++ tailWord_1161805) baseStart_1161805 baseEnd_1161805 := by
    simpa [prefixWord, tailWord_1161805, baseEnd_1161805] using wordTrace_append hprefix tailTrace_1161805
  have hstable : (prefixWord ++ tailWord_1161805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161805).length < 2 ^ (prefixWord ++ tailWord_1161805).sum := by decide
  have hdescent : baseEnd_1161805 < baseStart_1161805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161822 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1161822 : Nat := 118140960795 + 1161822 * 2 ^ 59
def prefixEnd_1161822 : Nat := 4983230072969 + 3 ^ 40 * 1161822 * 2
def baseEnd_1161822 : Nat := 397715413978705733187923

theorem tailTrace_1161822 : CollatzResearch.WordTrace tailWord_1161822 prefixEnd_1161822 397715413978705733187923 := by
  unfold tailWord_1161822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5296891199615599030676965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28250086397949861496943813 5296891199615599030676965)
  ·
    refine ⟨993167099927924818251931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5296891199615599030676965 993167099927924818251931)
    ·
      refine ⟨1489750649891887227377897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993167099927924818251931 1489750649891887227377897)
      ·
        refine ⟨1117312987418915420533423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1489750649891887227377897 1117312987418915420533423)
        ·
          refine ⟨1675969481128373130800135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117312987418915420533423 1675969481128373130800135)
          ·
            refine ⟨2513954221692559696200203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675969481128373130800135 2513954221692559696200203)
            ·
              refine ⟨3770931332538839544300305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513954221692559696200203 3770931332538839544300305)
              ·
                refine ⟨2828198499404129658225229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770931332538839544300305 2828198499404129658225229)
                ·
                  refine ⟨1060574437276548621834461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2828198499404129658225229 1060574437276548621834461)
                  ·
                    refine ⟨397715413978705733187923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060574437276548621834461 397715413978705733187923)
                    ·
                      rfl

theorem cell22_1161822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1161822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161822 prefixEnd_1161822 := by exact prefixLift 1161822
  have htrace : WordTrace (prefixWord ++ tailWord_1161822) baseStart_1161822 baseEnd_1161822 := by
    simpa [prefixWord, tailWord_1161822, baseEnd_1161822] using wordTrace_append hprefix tailTrace_1161822
  have hstable : (prefixWord ++ tailWord_1161822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161822).length < 2 ^ (prefixWord ++ tailWord_1161822).sum := by decide
  have hdescent : baseEnd_1161822 < baseStart_1161822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161859 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_1161859 : Nat := 118140960795 + 1161859 * 2 ^ 59
def prefixEnd_1161859 : Nat := 4983230072969 + 3 ^ 40 * 1161859 * 2
def baseEnd_1161859 : Nat := 397728079834849970012809

theorem tailTrace_1161859 : CollatzResearch.WordTrace tailWord_1161859 prefixEnd_1161859 397728079834849970012809 := by
  unfold tailWord_1161859
  simp only [CollatzResearch.WordTrace]
  refine ⟨42376479097790747564512631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28250986065193831709675087 42376479097790747564512631)
  ·
    refine ⟨63564718646686121346768947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42376479097790747564512631 63564718646686121346768947)
    ·
      refine ⟨95347077970029182020153421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63564718646686121346768947 95347077970029182020153421)
      ·
        refine ⟨35755154238760943257557533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95347077970029182020153421 35755154238760943257557533)
        ·
          refine ⟨13408182839535353721584075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35755154238760943257557533 13408182839535353721584075)
          ·
            refine ⟨20112274259303030582376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13408182839535353721584075 20112274259303030582376113)
            ·
              refine ⟨15084205694477272936782085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20112274259303030582376113 15084205694477272936782085)
              ·
                refine ⟨2828288567714488675646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15084205694477272936782085 2828288567714488675646641)
                ·
                  refine ⟨2121216425785866506734981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828288567714488675646641 2121216425785866506734981)
                  ·
                    refine ⟨397728079834849970012809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121216425785866506734981 397728079834849970012809)
                    ·
                      rfl

theorem cell22_1161859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_1161859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161859 prefixEnd_1161859 := by exact prefixLift 1161859
  have htrace : WordTrace (prefixWord ++ tailWord_1161859) baseStart_1161859 baseEnd_1161859 := by
    simpa [prefixWord, tailWord_1161859, baseEnd_1161859] using wordTrace_append hprefix tailTrace_1161859
  have hstable : (prefixWord ++ tailWord_1161859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161859).length < 2 ^ (prefixWord ++ tailWord_1161859).sum := by decide
  have hdescent : baseEnd_1161859 < baseStart_1161859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161861 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_1161861 : Nat := 118140960795 + 1161861 * 2 ^ 59
def prefixEnd_1161861 : Nat := 4983230072969 + 3 ^ 40 * 1161861 * 2
def baseEnd_1161861 : Nat := 397728764475722631462803

theorem tailTrace_1161861 : CollatzResearch.WordTrace tailWord_1161861 prefixEnd_1161861 397728764475722631462803 := by
  unfold tailWord_1161861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42376552043783501906085437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28251034695855667937390291 42376552043783501906085437)
  ·
    refine ⟨15891207016418813214782039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42376552043783501906085437 15891207016418813214782039)
    ·
      refine ⟨23836810524628219822173059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15891207016418813214782039 23836810524628219822173059)
      ·
        refine ⟨35755215786942329733259589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23836810524628219822173059 35755215786942329733259589)
        ·
          refine ⟨6704102960051686824986173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35755215786942329733259589 6704102960051686824986173)
          ·
            refine ⟨2514038610019382559369815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6704102960051686824986173 2514038610019382559369815)
            ·
              refine ⟨3771057915029073839054723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514038610019382559369815 3771057915029073839054723)
              ·
                refine ⟨5656586872543610758582085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771057915029073839054723 5656586872543610758582085)
                ·
                  refine ⟨1060610038601927017234141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5656586872543610758582085 1060610038601927017234141)
                  ·
                    refine ⟨397728764475722631462803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060610038601927017234141 397728764475722631462803)
                    ·
                      rfl

theorem cell22_1161861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_1161861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161861 prefixEnd_1161861 := by exact prefixLift 1161861
  have htrace : WordTrace (prefixWord ++ tailWord_1161861) baseStart_1161861 baseEnd_1161861 := by
    simpa [prefixWord, tailWord_1161861, baseEnd_1161861] using wordTrace_append hprefix tailTrace_1161861
  have hstable : (prefixWord ++ tailWord_1161861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161861).length < 2 ^ (prefixWord ++ tailWord_1161861).sum := by decide
  have hdescent : baseEnd_1161861 < baseStart_1161861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161876 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1161876 : Nat := 118140960795 + 1161876 * 2 ^ 59
def prefixEnd_1161876 : Nat := 4983230072969 + 3 ^ 40 * 1161876 * 2
def baseEnd_1161876 : Nat := 397733899282267592337757

theorem tailTrace_1161876 : CollatzResearch.WordTrace tailWord_1161876 prefixEnd_1161876 397733899282267592337757 := by
  unfold tailWord_1161876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21188549569364579733940741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28251399425819439645254321 21188549569364579733940741)
  ·
    refine ⟨3972853044255858700113889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21188549569364579733940741 3972853044255858700113889)
    ·
      refine ⟨2979639783191894025085417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3972853044255858700113889 2979639783191894025085417)
      ·
        refine ⟨2234729837393920518814063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2979639783191894025085417 2234729837393920518814063)
        ·
          refine ⟨3352094756090880778221095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234729837393920518814063 3352094756090880778221095)
          ·
            refine ⟨5028142134136321167331643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352094756090880778221095 5028142134136321167331643)
            ·
              refine ⟨7542213201204481750997465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028142134136321167331643 7542213201204481750997465)
              ·
                refine ⟨5656659900903361313248099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7542213201204481750997465 5656659900903361313248099)
                ·
                  refine ⟨8484989851355041969872149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656659900903361313248099 8484989851355041969872149)
                  ·
                    refine ⟨397733899282267592337757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8484989851355041969872149 397733899282267592337757)
                    ·
                      rfl

theorem cell22_1161876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1161876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161876 prefixEnd_1161876 := by exact prefixLift 1161876
  have htrace : WordTrace (prefixWord ++ tailWord_1161876) baseStart_1161876 baseEnd_1161876 := by
    simpa [prefixWord, tailWord_1161876, baseEnd_1161876] using wordTrace_append hprefix tailTrace_1161876
  have hstable : (prefixWord ++ tailWord_1161876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161876).length < 2 ^ (prefixWord ++ tailWord_1161876).sum := by decide
  have hdescent : baseEnd_1161876 < baseStart_1161876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161910 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1161910 : Nat := 118140960795 + 1161910 * 2 ^ 59
def prefixEnd_1161910 : Nat := 4983230072969 + 3 ^ 40 * 1161910 * 2
def baseEnd_1161910 : Nat := 397745538177102836987653

theorem tailTrace_1161910 : CollatzResearch.WordTrace tailWord_1161910 prefixEnd_1161910 397745538177102836987653 := by
  unfold tailWord_1161910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648646201287873954663699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28252226147070655516412789 2648646201287873954663699)
  ·
    refine ⟨3972969301931810931995549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2648646201287873954663699 3972969301931810931995549)
    ·
      refine ⟨1489863488224429099498331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3972969301931810931995549 1489863488224429099498331)
      ·
        refine ⟨2234795232336643649247497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1489863488224429099498331 2234795232336643649247497)
        ·
          refine ⟨1676096424252482736935623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2234795232336643649247497 1676096424252482736935623)
          ·
            refine ⟨2514144636378724105403435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676096424252482736935623 2514144636378724105403435)
            ·
              refine ⟨3771216954568086158105153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514144636378724105403435 3771216954568086158105153)
              ·
                refine ⟨2828412715926064618578865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771216954568086158105153 2828412715926064618578865)
                ·
                  refine ⟨2121309536944548463934149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828412715926064618578865 2121309536944548463934149)
                  ·
                    refine ⟨397745538177102836987653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121309536944548463934149 397745538177102836987653)
                    ·
                      rfl

theorem cell22_1161910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1161910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161910 prefixEnd_1161910 := by exact prefixLift 1161910
  have htrace : WordTrace (prefixWord ++ tailWord_1161910) baseStart_1161910 baseEnd_1161910 := by
    simpa [prefixWord, tailWord_1161910, baseEnd_1161910] using wordTrace_append hprefix tailTrace_1161910
  have hstable : (prefixWord ++ tailWord_1161910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161910).length < 2 ^ (prefixWord ++ tailWord_1161910).sum := by decide
  have hdescent : baseEnd_1161910 < baseStart_1161910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161919 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 7]
def baseStart_1161919 : Nat := 118140960795 + 1161919 * 2 ^ 59
def prefixEnd_1161919 : Nat := 4983230072969 + 3 ^ 40 * 1161919 * 2
def baseEnd_1161919 : Nat := 132582873020343271170875

theorem tailTrace_1161919 : CollatzResearch.WordTrace tailWord_1161919 prefixEnd_1161919 132582873020343271170875 := by
  unfold tailWord_1161919
  simp only [CollatzResearch.WordTrace]
  refine ⟨42378667477573377811696811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28252444985048918541131207 42378667477573377811696811)
  ·
    refine ⟨63568001216360066717545217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42378667477573377811696811 63568001216360066717545217)
    ·
      refine ⟨47676000912270050038158913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63568001216360066717545217 47676000912270050038158913)
      ·
        refine ⟨35757000684202537528619185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47676000912270050038158913 35757000684202537528619185)
        ·
          refine ⟨26817750513151903146464389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35757000684202537528619185 26817750513151903146464389)
          ·
            refine ⟨5028328221215981839962073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26817750513151903146464389 5028328221215981839962073)
            ·
              refine ⟨3771246165911986379971555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5028328221215981839962073 3771246165911986379971555)
              ·
                refine ⟨5656869248867979569957333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771246165911986379971555 5656869248867979569957333)
                ·
                  refine ⟨132582873020343271170875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5656869248867979569957333 132582873020343271170875)
                  ·
                    rfl

theorem cell22_1161919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_1161919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161919 prefixEnd_1161919 := by exact prefixLift 1161919
  have htrace : WordTrace (prefixWord ++ tailWord_1161919) baseStart_1161919 baseEnd_1161919 := by
    simpa [prefixWord, tailWord_1161919, baseEnd_1161919] using wordTrace_append hprefix tailTrace_1161919
  have hstable : (prefixWord ++ tailWord_1161919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161919).length < 2 ^ (prefixWord ++ tailWord_1161919).sum := by decide
  have hdescent : baseEnd_1161919 < baseStart_1161919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1161996 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_1161996 : Nat := 118140960795 + 1161996 * 2 ^ 59
def prefixEnd_1161996 : Nat := 4983230072969 + 3 ^ 40 * 1161996 * 2
def baseEnd_1161996 : Nat := 397774977734627279337389

theorem tailTrace_1161996 : CollatzResearch.WordTrace tailWord_1161996 prefixEnd_1161996 397774977734627279337389 := by
  unfold tailWord_1161996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21190737949147209981124921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28254317265529613308166561 21190737949147209981124921)
  ·
    refine ⟨15893053461860407485843691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21190737949147209981124921 15893053461860407485843691)
    ·
      refine ⟨23839580192790611228765537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893053461860407485843691 23839580192790611228765537)
      ·
        refine ⟨17879685144592958421574153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23839580192790611228765537 17879685144592958421574153)
        ·
          refine ⟨13409763858444718816180615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17879685144592958421574153 13409763858444718816180615)
          ·
            refine ⟨20114645787667078224270923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13409763858444718816180615 20114645787667078224270923)
            ·
              refine ⟨30171968681500617336406385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20114645787667078224270923 30171968681500617336406385)
              ·
                refine ⟨22628976511125463002304789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30171968681500617336406385 22628976511125463002304789)
                ·
                  refine ⟨1060733273959006078233037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22628976511125463002304789 1060733273959006078233037)
                  ·
                    refine ⟨397774977734627279337389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060733273959006078233037 397774977734627279337389)
                    ·
                      rfl

theorem cell22_1161996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1161996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1161996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1161996 prefixEnd_1161996 := by exact prefixLift 1161996
  have htrace : WordTrace (prefixWord ++ tailWord_1161996) baseStart_1161996 baseEnd_1161996 := by
    simpa [prefixWord, tailWord_1161996, baseEnd_1161996] using wordTrace_append hprefix tailTrace_1161996
  have hstable : (prefixWord ++ tailWord_1161996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1161996).length < 2 ^ (prefixWord ++ tailWord_1161996).sum := by decide
  have hdescent : baseEnd_1161996 < baseStart_1161996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1161996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162030 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1162030 : Nat := 118140960795 + 1162030 * 2 ^ 59
def prefixEnd_1162030 : Nat := 4983230072969 + 3 ^ 40 * 1162030 * 2
def baseEnd_1162030 : Nat := 397786616629462523987285

theorem tailTrace_1162030 : CollatzResearch.WordTrace tailWord_1162030 prefixEnd_1162030 397786616629462523987285 := by
  unfold tailWord_1162030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297839497521405471123443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28255143986780829179325029 5297839497521405471123443)
  ·
    refine ⟨7946759246282108206685165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297839497521405471123443 7946759246282108206685165)
    ·
      refine ⟨2980034717355790577506937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7946759246282108206685165 2980034717355790577506937)
      ·
        refine ⟨2235026038016842933130203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2980034717355790577506937 2235026038016842933130203)
        ·
          refine ⟨3352539057025264399695305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235026038016842933130203 3352539057025264399695305)
          ·
            refine ⟨2514404292768948299771479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3352539057025264399695305 2514404292768948299771479)
            ·
              refine ⟨3771606439153422449657219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514404292768948299771479 3771606439153422449657219)
              ·
                refine ⟨5657409658730133674485829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771606439153422449657219 5657409658730133674485829)
                ·
                  refine ⟨1060764311011900063966093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5657409658730133674485829 1060764311011900063966093)
                  ·
                    refine ⟨397786616629462523987285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060764311011900063966093 397786616629462523987285)
                    ·
                      rfl

theorem cell22_1162030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1162030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162030 prefixEnd_1162030 := by exact prefixLift 1162030
  have htrace : WordTrace (prefixWord ++ tailWord_1162030) baseStart_1162030 baseEnd_1162030 := by
    simpa [prefixWord, tailWord_1162030, baseEnd_1162030] using wordTrace_append hprefix tailTrace_1162030
  have hstable : (prefixWord ++ tailWord_1162030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162030).length < 2 ^ (prefixWord ++ tailWord_1162030).sum := by decide
  have hdescent : baseEnd_1162030 < baseStart_1162030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162071 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 7]
def baseStart_1162071 : Nat := 118140960795 + 1162071 * 2 ^ 59
def prefixEnd_1162071 : Nat := 4983230072969 + 3 ^ 40 * 1162071 * 2
def baseEnd_1162071 : Nat := 132600217255784027904053

theorem tailTrace_1162071 : CollatzResearch.WordTrace tailWord_1162071 prefixEnd_1162071 132600217255784027904053 := by
  unfold tailWord_1162071
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384211373022707771230067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28256140915348471847486711 42384211373022707771230067)
  ·
    refine ⟨63576317059534061656845101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42384211373022707771230067 63576317059534061656845101)
    ·
      refine ⟨23841118897325273121316913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63576317059534061656845101 23841118897325273121316913)
      ·
        refine ⟨17880839172993954840987685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23841118897325273121316913 17880839172993954840987685)
        ·
          refine ⟨3352657344936366532685191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17880839172993954840987685 3352657344936366532685191)
          ·
            refine ⟨5028986017404549799027787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352657344936366532685191 5028986017404549799027787)
            ·
              refine ⟨7543479026106824698541681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028986017404549799027787 7543479026106824698541681)
              ·
                refine ⟨5657609269580118523906261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7543479026106824698541681 5657609269580118523906261)
                ·
                  refine ⟨132600217255784027904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5657609269580118523906261 132600217255784027904053)
                  ·
                    rfl

theorem cell22_1162071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_1162071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162071 prefixEnd_1162071 := by exact prefixLift 1162071
  have htrace : WordTrace (prefixWord ++ tailWord_1162071) baseStart_1162071 baseEnd_1162071 := by
    simpa [prefixWord, tailWord_1162071, baseEnd_1162071] using wordTrace_append hprefix tailTrace_1162071
  have hstable : (prefixWord ++ tailWord_1162071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162071).length < 2 ^ (prefixWord ++ tailWord_1162071).sum := by decide
  have hdescent : baseEnd_1162071 < baseStart_1162071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162092 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_1162092 : Nat := 118140960795 + 1162092 * 2 ^ 59
def prefixEnd_1162092 : Nat := 4983230072969 + 3 ^ 40 * 1162092 * 2
def baseEnd_1162092 : Nat := 397807840496515028937095

theorem tailTrace_1162092 : CollatzResearch.WordTrace tailWord_1162092 prefixEnd_1162092 397807840496515028937095 := by
  unfold tailWord_1162092
  simp only [CollatzResearch.WordTrace]
  refine ⟨21192488652973314178872265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28256651537297752238496353 21192488652973314178872265)
  ·
    refine ⟨15894366489729985634154199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21192488652973314178872265 15894366489729985634154199)
    ·
      refine ⟨23841549734594978451231299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15894366489729985634154199 23841549734594978451231299)
      ·
        refine ⟨35762324601892467676846949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23841549734594978451231299 35762324601892467676846949)
        ·
          refine ⟨6705435862854837689408803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35762324601892467676846949 6705435862854837689408803)
          ·
            refine ⟨10058153794282256534113205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705435862854837689408803 10058153794282256534113205)
            ·
              refine ⟨942951918213961550073113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10058153794282256534113205 942951918213961550073113)
              ·
                refine ⟨707213938660471162554835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942951918213961550073113 707213938660471162554835)
                ·
                  refine ⟨1060820907990706743832253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707213938660471162554835 1060820907990706743832253)
                  ·
                    refine ⟨397807840496515028937095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060820907990706743832253 397807840496515028937095)
                    ·
                      rfl

theorem cell22_1162092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_1162092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162092 prefixEnd_1162092 := by exact prefixLift 1162092
  have htrace : WordTrace (prefixWord ++ tailWord_1162092) baseStart_1162092 baseEnd_1162092 := by
    simpa [prefixWord, tailWord_1162092, baseEnd_1162092] using wordTrace_append hprefix tailTrace_1162092
  have hstable : (prefixWord ++ tailWord_1162092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162092).length < 2 ^ (prefixWord ++ tailWord_1162092).sum := by decide
  have hdescent : baseEnd_1162092 < baseStart_1162092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162105 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 5]
def baseStart_1162105 : Nat := 118140960795 + 1162105 * 2 ^ 59
def prefixEnd_1162105 : Nat := 4983230072969 + 3 ^ 40 * 1162105 * 2
def baseEnd_1162105 : Nat := 132604096887395776120685

theorem tailTrace_1162105 : CollatzResearch.WordTrace tailWord_1162105 prefixEnd_1162105 132604096887395776120685 := by
  unfold tailWord_1162105
  simp only [CollatzResearch.WordTrace]
  refine ⟨42385451454899531577967769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28256967636599687718645179 42385451454899531577967769)
  ·
    refine ⟨31789088591174648683475827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42385451454899531577967769 31789088591174648683475827)
    ·
      refine ⟨47683632886761973025213741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31789088591174648683475827 47683632886761973025213741)
      ·
        refine ⟨17881362332535739884455153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47683632886761973025213741 17881362332535739884455153)
        ·
          refine ⟨13411021749401804913341365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17881362332535739884455153 13411021749401804913341365)
          ·
            refine ⟨1257283289006419210625753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13411021749401804913341365 1257283289006419210625753)
            ·
              refine ⟨942962466754814407969315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257283289006419210625753 942962466754814407969315)
              ·
                refine ⟨1414443700132221611953973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942962466754814407969315 1414443700132221611953973)
                ·
                  refine ⟨132604096887395776120685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1414443700132221611953973 132604096887395776120685)
                  ·
                    rfl

theorem cell22_1162105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_1162105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162105 prefixEnd_1162105 := by exact prefixLift 1162105
  have htrace : WordTrace (prefixWord ++ tailWord_1162105) baseStart_1162105 baseEnd_1162105 := by
    simpa [prefixWord, tailWord_1162105, baseEnd_1162105] using wordTrace_append hprefix tailTrace_1162105
  have hstable : (prefixWord ++ tailWord_1162105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162105).length < 2 ^ (prefixWord ++ tailWord_1162105).sum := by decide
  have hdescent : baseEnd_1162105 < baseStart_1162105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162116 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1162116 : Nat := 118140960795 + 1162116 * 2 ^ 59
def prefixEnd_1162116 : Nat := 4983230072969 + 3 ^ 40 * 1162116 * 2
def baseEnd_1162116 : Nat := 132605352062328988779007

theorem tailTrace_1162116 : CollatzResearch.WordTrace tailWord_1162116 prefixEnd_1162116 132605352062328988779007 := by
  unfold tailWord_1162116
  simp only [CollatzResearch.WordTrace]
  refine ⟨21192926328929840228309101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28257235105239786971078801 21192926328929840228309101)
  ·
    refine ⟨7947347373348690085615913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21192926328929840228309101 7947347373348690085615913)
    ·
      refine ⟨5960510530011517564211935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7947347373348690085615913 5960510530011517564211935)
      ·
        refine ⟨8940765795017276346317903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960510530011517564211935 8940765795017276346317903)
        ·
          refine ⟨13411148692525914519476855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940765795017276346317903 13411148692525914519476855)
          ·
            refine ⟨20116723038788871779215283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13411148692525914519476855 20116723038788871779215283)
            ·
              refine ⟨30175084558183307668822925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20116723038788871779215283 30175084558183307668822925)
              ·
                refine ⟨11315656709318740375808597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30175084558183307668822925 11315656709318740375808597)
                ·
                  refine ⟨132605352062328988779007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11315656709318740375808597 132605352062328988779007)
                  ·
                    rfl

theorem cell22_1162116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1162116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162116 prefixEnd_1162116 := by exact prefixLift 1162116
  have htrace : WordTrace (prefixWord ++ tailWord_1162116) baseStart_1162116 baseEnd_1162116 := by
    simpa [prefixWord, tailWord_1162116, baseEnd_1162116] using wordTrace_append hprefix tailTrace_1162116
  have hstable : (prefixWord ++ tailWord_1162116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162116).length < 2 ^ (prefixWord ++ tailWord_1162116).sum := by decide
  have hdescent : baseEnd_1162116 < baseStart_1162116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162135 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1162135 : Nat := 118140960795 + 1162135 * 2 ^ 59
def prefixEnd_1162135 : Nat := 4983230072969 + 3 ^ 40 * 1162135 * 2
def baseEnd_1162135 : Nat := 397822560275277250111963

theorem tailTrace_1162135 : CollatzResearch.WordTrace tailWord_1162135 prefixEnd_1162135 397822560275277250111963 := by
  unfold tailWord_1162135
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386545644790846701559859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28257697096527231134373239 42386545644790846701559859)
  ·
    refine ⟨63579818467186270052339789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42386545644790846701559859 63579818467186270052339789)
    ·
      refine ⟨23842431925194851269627421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63579818467186270052339789 23842431925194851269627421)
      ·
        refine ⟨8940911971948069226110283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23842431925194851269627421 8940911971948069226110283)
        ·
          refine ⟨13411367957922103839165425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940911971948069226110283 13411367957922103839165425)
          ·
            refine ⟨10058525968441577879374069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13411367957922103839165425 10058525968441577879374069)
            ·
              refine ⟨942986809541397926191319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10058525968441577879374069 942986809541397926191319)
              ·
                refine ⟨1414480214312096889286979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942986809541397926191319 1414480214312096889286979)
                ·
                  refine ⟨2121720321468145333930469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414480214312096889286979 2121720321468145333930469)
                  ·
                    refine ⟨397822560275277250111963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121720321468145333930469 397822560275277250111963)
                    ·
                      rfl

theorem cell22_1162135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1162135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162135 prefixEnd_1162135 := by exact prefixLift 1162135
  have htrace : WordTrace (prefixWord ++ tailWord_1162135) baseStart_1162135 baseEnd_1162135 := by
    simpa [prefixWord, tailWord_1162135, baseEnd_1162135] using wordTrace_append hprefix tailTrace_1162135
  have hstable : (prefixWord ++ tailWord_1162135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162135).length < 2 ^ (prefixWord ++ tailWord_1162135).sum := by decide
  have hdescent : baseEnd_1162135 < baseStart_1162135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162165 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1162165 : Nat := 118140960795 + 1162165 * 2 ^ 59
def prefixEnd_1162165 : Nat := 4983230072969 + 3 ^ 40 * 1162165 * 2
def baseEnd_1162165 : Nat := 397832829888367171861871

theorem tailTrace_1162165 : CollatzResearch.WordTrace tailWord_1162165 prefixEnd_1162165 397832829888367171861871 := by
  unfold tailWord_1162165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42387639834682161825151949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28258426556454774550101299 42387639834682161825151949)
  ·
    refine ⟨15895364938005810684431981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42387639834682161825151949 15895364938005810684431981)
    ·
      refine ⟨5960761851752179006661993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15895364938005810684431981 5960761851752179006661993)
      ·
        refine ⟨4470571388814134254996495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5960761851752179006661993 4470571388814134254996495)
        ·
          refine ⟨6705857083221201382494743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470571388814134254996495 6705857083221201382494743)
          ·
            refine ⟨10058785624831802073742115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705857083221201382494743 10058785624831802073742115)
            ·
              refine ⟨15088178437247703110613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058785624831802073742115 15088178437247703110613173)
              ·
                refine ⟨1414516728491972166619985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15088178437247703110613173 1414516728491972166619985)
                ·
                  refine ⟨1060887546368979124964989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1414516728491972166619985 1060887546368979124964989)
                  ·
                    refine ⟨397832829888367171861871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060887546368979124964989 397832829888367171861871)
                    ·
                      rfl

theorem cell22_1162165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1162165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162165 prefixEnd_1162165 := by exact prefixLift 1162165
  have htrace : WordTrace (prefixWord ++ tailWord_1162165) baseStart_1162165 baseEnd_1162165 := by
    simpa [prefixWord, tailWord_1162165, baseEnd_1162165] using wordTrace_append hprefix tailTrace_1162165
  have hstable : (prefixWord ++ tailWord_1162165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162165).length < 2 ^ (prefixWord ++ tailWord_1162165).sum := by decide
  have hdescent : baseEnd_1162165 < baseStart_1162165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162193 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_1162193 : Nat := 118140960795 + 1162193 * 2 ^ 59
def prefixEnd_1162193 : Nat := 4983230072969 + 3 ^ 40 * 1162193 * 2
def baseEnd_1162193 : Nat := 397842414860584432161785

theorem tailTrace_1162193 : CollatzResearch.WordTrace tailWord_1162193 prefixEnd_1162193 397842414860584432161785 := by
  unfold tailWord_1162193
  simp only [CollatzResearch.WordTrace]
  refine ⟨42388661078580722607171233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28259107385720481738114155 42388661078580722607171233)
  ·
    refine ⟨31791495808935541955378425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42388661078580722607171233 31791495808935541955378425)
    ·
      refine ⟨23843621856701656466533819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31791495808935541955378425 23843621856701656466533819)
      ·
        refine ⟨35765432785052484699800729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23843621856701656466533819 35765432785052484699800729)
        ·
          refine ⟨26824074588789363524850547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35765432785052484699800729 26824074588789363524850547)
          ·
            refine ⟨40236111883184045287275821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26824074588789363524850547 40236111883184045287275821)
            ·
              refine ⟨15088541956194016982728433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40236111883184045287275821 15088541956194016982728433)
              ·
                refine ⟨11316406467145512737046325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15088541956194016982728433 11316406467145512737046325)
                ·
                  refine ⟨1060913106294891819098093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11316406467145512737046325 1060913106294891819098093)
                  ·
                    refine ⟨397842414860584432161785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1060913106294891819098093 397842414860584432161785)
                    ·
                      rfl

theorem cell22_1162193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_1162193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162193 prefixEnd_1162193 := by exact prefixLift 1162193
  have htrace : WordTrace (prefixWord ++ tailWord_1162193) baseStart_1162193 baseEnd_1162193 := by
    simpa [prefixWord, tailWord_1162193, baseEnd_1162193] using wordTrace_append hprefix tailTrace_1162193
  have hstable : (prefixWord ++ tailWord_1162193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162193).length < 2 ^ (prefixWord ++ tailWord_1162193).sum := by decide
  have hdescent : baseEnd_1162193 < baseStart_1162193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162229 : List Nat := [1, 3, 5, 2, 1, 2, 2, 6]
def baseStart_1162229 : Nat := 118140960795 + 1162229 * 2 ^ 59
def prefixEnd_1162229 : Nat := 4983230072969 + 3 ^ 40 * 1162229 * 2
def baseEnd_1162229 : Nat := 44206082044032482029075

theorem tailTrace_1162229 : CollatzResearch.WordTrace tailWord_1162229 prefixEnd_1162229 44206082044032482029075 := by
  unfold tailWord_1162229
  simp only [CollatzResearch.WordTrace]
  refine ⟨42389974106450300755481741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28259982737633533836987827 42389974106450300755481741)
  ·
    refine ⟨15896240289918862783305653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42389974106450300755481741 15896240289918862783305653)
    ·
      refine ⟨1490272527179893385934905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15896240289918862783305653 1490272527179893385934905)
      ·
        refine ⟨1117704395384920039451179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490272527179893385934905 1117704395384920039451179)
        ·
          refine ⟨1676556593077380059176769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1117704395384920039451179 1676556593077380059176769)
          ·
            refine ⟨1257417444808035044382577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676556593077380059176769 1257417444808035044382577)
            ·
              refine ⟨943063083606026283286933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257417444808035044382577 943063083606026283286933)
              ·
                refine ⟨44206082044032482029075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 943063083606026283286933 44206082044032482029075)
                ·
                  rfl

theorem cell22_1162229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 6].length) (baseStart_1162229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162229 prefixEnd_1162229 := by exact prefixLift 1162229
  have htrace : WordTrace (prefixWord ++ tailWord_1162229) baseStart_1162229 baseEnd_1162229 := by
    simpa [prefixWord, tailWord_1162229, baseEnd_1162229] using wordTrace_append hprefix tailTrace_1162229
  have hstable : (prefixWord ++ tailWord_1162229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162229).length < 2 ^ (prefixWord ++ tailWord_1162229).sum := by decide
  have hdescent : baseEnd_1162229 < baseStart_1162229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162283 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_1162283 : Nat := 118140960795 + 1162283 * 2 ^ 59
def prefixEnd_1162283 : Nat := 4983230072969 + 3 ^ 40 * 1162283 * 2
def baseEnd_1162283 : Nat := 397873223699854197411509

theorem tailTrace_1162283 : CollatzResearch.WordTrace tailWord_1162283 prefixEnd_1162283 397873223699854197411509 := by
  unfold tailWord_1162283
  simp only [CollatzResearch.WordTrace]
  refine ⟨42391943648254667977947503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28261295765503111985298335 42391943648254667977947503)
  ·
    refine ⟨63587915472382001966921255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42391943648254667977947503 63587915472382001966921255)
    ·
      refine ⟨95381873208573002950381883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63587915472382001966921255 95381873208573002950381883)
      ·
        refine ⟨143072809812859504425572825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95381873208573002950381883 143072809812859504425572825)
        ·
          refine ⟨107304607359644628319179619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143072809812859504425572825 107304607359644628319179619)
          ·
            refine ⟨160956911039466942478769429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107304607359644628319179619 160956911039466942478769429)
            ·
              refine ⟨7544855204975012928692317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 160956911039466942478769429 7544855204975012928692317)
              ·
                refine ⟨2829320701865629848259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7544855204975012928692317 2829320701865629848259619)
                ·
                  refine ⟨4243981052798444772389429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829320701865629848259619 4243981052798444772389429)
                  ·
                    refine ⟨397873223699854197411509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4243981052798444772389429 397873223699854197411509)
                    ·
                      rfl

theorem cell22_1162283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_1162283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162283 prefixEnd_1162283 := by exact prefixLift 1162283
  have htrace : WordTrace (prefixWord ++ tailWord_1162283) baseStart_1162283 baseEnd_1162283 := by
    simpa [prefixWord, tailWord_1162283, baseEnd_1162283] using wordTrace_append hprefix tailTrace_1162283
  have hstable : (prefixWord ++ tailWord_1162283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162283).length < 2 ^ (prefixWord ++ tailWord_1162283).sum := by decide
  have hdescent : baseEnd_1162283 < baseStart_1162283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162298 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_1162298 : Nat := 118140960795 + 1162298 * 2 ^ 59
def prefixEnd_1162298 : Nat := 4983230072969 + 3 ^ 40 * 1162298 * 2
def baseEnd_1162298 : Nat := 397878358506399158286463

theorem tailTrace_1162298 : CollatzResearch.WordTrace tailWord_1162298 prefixEnd_1162298 397878358506399158286463 := by
  unfold tailWord_1162298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10598122685800081384935887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28261660495466883693162365 10598122685800081384935887)
  ·
    refine ⟨15897184028700122077403831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10598122685800081384935887 15897184028700122077403831)
    ·
      refine ⟨23845776043050183116105747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15897184028700122077403831 23845776043050183116105747)
      ·
        refine ⟨35768664064575274674158621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845776043050183116105747 35768664064575274674158621)
        ·
          refine ⟨13413249024215728002809483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35768664064575274674158621 13413249024215728002809483)
          ·
            refine ⟨20119873536323592004214225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13413249024215728002809483 20119873536323592004214225)
            ·
              refine ⟨15089905152242694003160669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20119873536323592004214225 15089905152242694003160669)
              ·
                refine ⟨5658714432091010251185251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15089905152242694003160669 5658714432091010251185251)
                ·
                  refine ⟨8488071648136515376777877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5658714432091010251185251 8488071648136515376777877)
                  ·
                    refine ⟨397878358506399158286463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8488071648136515376777877 397878358506399158286463)
                    ·
                      rfl

theorem cell22_1162298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_1162298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162298 prefixEnd_1162298 := by exact prefixLift 1162298
  have htrace : WordTrace (prefixWord ++ tailWord_1162298) baseStart_1162298 baseEnd_1162298 := by
    simpa [prefixWord, tailWord_1162298, baseEnd_1162298] using wordTrace_append hprefix tailTrace_1162298
  have hstable : (prefixWord ++ tailWord_1162298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162298).length < 2 ^ (prefixWord ++ tailWord_1162298).sum := by decide
  have hdescent : baseEnd_1162298 < baseStart_1162298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162300 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1162300 : Nat := 118140960795 + 1162300 * 2 ^ 59
def prefixEnd_1162300 : Nat := 4983230072969 + 3 ^ 40 * 1162300 * 2
def baseEnd_1162300 : Nat := 397879043147271819736457

theorem tailTrace_1162300 : CollatzResearch.WordTrace tailWord_1162300 prefixEnd_1162300 397879043147271819736457 := by
  unfold tailWord_1162300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21196281844596539940658177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28261709126128719920877569 21196281844596539940658177)
  ·
    refine ⟨15897211383447404955493633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21196281844596539940658177 15897211383447404955493633)
    ·
      refine ⟨11922908537585553716620225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15897211383447404955493633 11922908537585553716620225)
      ·
        refine ⟨8942181403189165287465169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11922908537585553716620225 8942181403189165287465169)
        ·
          refine ⟨6706636052391873965598877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8942181403189165287465169 6706636052391873965598877)
          ·
            refine ⟨2514988519646952737099579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6706636052391873965598877 2514988519646952737099579)
            ·
              refine ⟨3772482779470429105649369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2514988519646952737099579 3772482779470429105649369)
              ·
                refine ⟨2829362084602821829237027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772482779470429105649369 2829362084602821829237027)
                ·
                  refine ⟨4244043126904232743855541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829362084602821829237027 4244043126904232743855541)
                  ·
                    refine ⟨397879043147271819736457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4244043126904232743855541 397879043147271819736457)
                    ·
                      rfl

theorem cell22_1162300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1162300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162300 prefixEnd_1162300 := by exact prefixLift 1162300
  have htrace : WordTrace (prefixWord ++ tailWord_1162300) baseStart_1162300 baseEnd_1162300 := by
    simpa [prefixWord, tailWord_1162300, baseEnd_1162300] using wordTrace_append hprefix tailTrace_1162300
  have hstable : (prefixWord ++ tailWord_1162300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162300).length < 2 ^ (prefixWord ++ tailWord_1162300).sum := by decide
  have hdescent : baseEnd_1162300 < baseStart_1162300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162334 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1162334 : Nat := 118140960795 + 1162334 * 2 ^ 59
def prefixEnd_1162334 : Nat := 4983230072969 + 3 ^ 40 * 1162334 * 2
def baseEnd_1162334 : Nat := 397890682042107064386353

theorem tailTrace_1162334 : CollatzResearch.WordTrace tailWord_1162334 prefixEnd_1162334 397890682042107064386353 := by
  unfold tailWord_1162334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299225471383737961006757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28262535847379935792036037 5299225471383737961006757)
  ·
    refine ⟨993604775884450867688767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5299225471383737961006757 993604775884450867688767)
    ·
      refine ⟨1490407163826676301533151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993604775884450867688767 1490407163826676301533151)
      ·
        refine ⟨2235610745740014452299727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490407163826676301533151 2235610745740014452299727)
        ·
          refine ⟨3353416118610021678449591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235610745740014452299727 3353416118610021678449591)
          ·
            refine ⟨5030124177915032517674387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3353416118610021678449591 5030124177915032517674387)
            ·
              refine ⟨7545186266872548776511581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030124177915032517674387 7545186266872548776511581)
              ·
                refine ⟨2829444850077205791191843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7545186266872548776511581 2829444850077205791191843)
                ·
                  refine ⟨4244167275115808686787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829444850077205791191843 4244167275115808686787765)
                  ·
                    refine ⟨397890682042107064386353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4244167275115808686787765 397890682042107064386353)
                    ·
                      rfl

theorem cell22_1162334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1162334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162334 prefixEnd_1162334 := by exact prefixLift 1162334
  have htrace : WordTrace (prefixWord ++ tailWord_1162334) baseStart_1162334 baseEnd_1162334 := by
    simpa [prefixWord, tailWord_1162334, baseEnd_1162334] using wordTrace_append hprefix tailTrace_1162334
  have hstable : (prefixWord ++ tailWord_1162334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162334).length < 2 ^ (prefixWord ++ tailWord_1162334).sum := by decide
  have hdescent : baseEnd_1162334 < baseStart_1162334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162345 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_1162345 : Nat := 118140960795 + 1162345 * 2 ^ 59
def prefixEnd_1162345 : Nat := 4983230072969 + 3 ^ 40 * 1162345 * 2
def baseEnd_1162345 : Nat := 397894447566906702361319

theorem tailTrace_1162345 : CollatzResearch.WordTrace tailWord_1162345 prefixEnd_1162345 397894447566906702361319 := by
  unfold tailWord_1162345
  simp only [CollatzResearch.WordTrace]
  refine ⟨42394204974030052566704489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28262803316020035044469659 42394204974030052566704489)
  ·
    refine ⟨31795653730522539425028367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42394204974030052566704489 31795653730522539425028367)
    ·
      refine ⟨47693480595783809137542551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31795653730522539425028367 47693480595783809137542551)
      ·
        refine ⟨71540220893675713706313827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47693480595783809137542551 71540220893675713706313827)
        ·
          refine ⟨107310331340513570559470741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71540220893675713706313827 107310331340513570559470741)
          ·
            refine ⟨5030171781586573619975191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107310331340513570559470741 5030171781586573619975191)
            ·
              refine ⟨7545257672379860429962787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030171781586573619975191 7545257672379860429962787)
              ·
                refine ⟨11317886508569790644944181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7545257672379860429962787 11317886508569790644944181)
                ·
                  refine ⟨1061051860178417872963517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11317886508569790644944181 1061051860178417872963517)
                  ·
                    refine ⟨397894447566906702361319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061051860178417872963517 397894447566906702361319)
                    ·
                      rfl

theorem cell22_1162345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_1162345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162345 prefixEnd_1162345 := by exact prefixLift 1162345
  have htrace : WordTrace (prefixWord ++ tailWord_1162345) baseStart_1162345 baseEnd_1162345 := by
    simpa [prefixWord, tailWord_1162345, baseEnd_1162345] using wordTrace_append hprefix tailTrace_1162345
  have hstable : (prefixWord ++ tailWord_1162345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162345).length < 2 ^ (prefixWord ++ tailWord_1162345).sum := by decide
  have hdescent : baseEnd_1162345 < baseStart_1162345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162413 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1162413 : Nat := 118140960795 + 1162413 * 2 ^ 59
def prefixEnd_1162413 : Nat := 4983230072969 + 3 ^ 40 * 1162413 * 2
def baseEnd_1162413 : Nat := 397917725356577191661111

theorem tailTrace_1162413 : CollatzResearch.WordTrace tailWord_1162413 prefixEnd_1162413 397917725356577191661111 := by
  unfold tailWord_1162413
  simp only [CollatzResearch.WordTrace]
  refine ⟨42396685137783700180179893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28264456758522466786786595 42396685137783700180179893)
  ·
    refine ⟨3974689231667221891891865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42396685137783700180179893 3974689231667221891891865)
    ·
      refine ⟨2981016923750416418918899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3974689231667221891891865 2981016923750416418918899)
      ·
        refine ⟨4471525385625624628378349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2981016923750416418918899 4471525385625624628378349)
        ·
          refine ⟨1676822019609609235641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4471525385625624628378349 1676822019609609235641881)
          ·
            refine ⟨1257616514707206926731411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1676822019609609235641881 1257616514707206926731411)
            ·
              refine ⟨1886424772060810390097117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257616514707206926731411 1886424772060810390097117)
              ·
                refine ⟨707409289522803896286419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886424772060810390097117 707409289522803896286419)
                ·
                  refine ⟨1061113934284205844429629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707409289522803896286419 1061113934284205844429629)
                  ·
                    refine ⟨397917725356577191661111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061113934284205844429629 397917725356577191661111)
                    ·
                      rfl

theorem cell22_1162413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1162413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162413 prefixEnd_1162413 := by exact prefixLift 1162413
  have htrace : WordTrace (prefixWord ++ tailWord_1162413) baseStart_1162413 baseEnd_1162413 := by
    simpa [prefixWord, tailWord_1162413, baseEnd_1162413] using wordTrace_append hprefix tailTrace_1162413
  have hstable : (prefixWord ++ tailWord_1162413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162413).length < 2 ^ (prefixWord ++ tailWord_1162413).sum := by decide
  have hdescent : baseEnd_1162413 < baseStart_1162413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162456 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_1162456 : Nat := 118140960795 + 1162456 * 2 ^ 59
def prefixEnd_1162456 : Nat := 4983230072969 + 3 ^ 40 * 1162456 * 2
def baseEnd_1162456 : Nat := 397932445135339412835979

theorem tailTrace_1162456 : CollatzResearch.WordTrace tailWord_1162456 prefixEnd_1162456 397932445135339412835979 := by
  unfold tailWord_1162456
  simp only [CollatzResearch.WordTrace]
  refine ⟨21199126738313959261997611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28265502317751945682663481 21199126738313959261997611)
  ·
    refine ⟨31798690107470938892996417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21199126738313959261997611 31798690107470938892996417)
    ·
      refine ⟨23849017580603204169747313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31798690107470938892996417 23849017580603204169747313)
      ·
        refine ⟨17886763185452403127310485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23849017580603204169747313 17886763185452403127310485)
        ·
          refine ⟨838442024318081396592679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17886763185452403127310485 838442024318081396592679)
          ·
            refine ⟨1257663036477122094889019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838442024318081396592679 1257663036477122094889019)
            ·
              refine ⟨1886494554715683142333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257663036477122094889019 1886494554715683142333529)
              ·
                refine ⟨1414870916036762356750147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886494554715683142333529 1414870916036762356750147)
                ·
                  refine ⟨2122306374055143535125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414870916036762356750147 2122306374055143535125221)
                  ·
                    refine ⟨397932445135339412835979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122306374055143535125221 397932445135339412835979)
                    ·
                      rfl

theorem cell22_1162456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_1162456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162456 prefixEnd_1162456 := by exact prefixLift 1162456
  have htrace : WordTrace (prefixWord ++ tailWord_1162456) baseStart_1162456 baseEnd_1162456 := by
    simpa [prefixWord, tailWord_1162456, baseEnd_1162456] using wordTrace_append hprefix tailTrace_1162456
  have hstable : (prefixWord ++ tailWord_1162456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162456).length < 2 ^ (prefixWord ++ tailWord_1162456).sum := by decide
  have hdescent : baseEnd_1162456 < baseStart_1162456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162465 : List Nat := [1, 2, 3, 1, 3, 2, 2, 8]
def baseStart_1162465 : Nat := 118140960795 + 1162465 * 2 ^ 59
def prefixEnd_1162465 : Nat := 4983230072969 + 3 ^ 40 * 1162465 * 2
def baseEnd_1162465 : Nat := 44215058446585154373439

theorem tailTrace_1162465 : CollatzResearch.WordTrace tailWord_1162465 prefixEnd_1162465 44215058446585154373439 := by
  unfold tailWord_1162465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42398581733595313061072849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28265721155730208707381899 42398581733595313061072849)
  ·
    refine ⟨31798936300196484795804637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42398581733595313061072849 31798936300196484795804637)
    ·
      refine ⟨11924601112573681798426739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31798936300196484795804637 11924601112573681798426739)
      ·
        refine ⟨17886901668860522697640109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924601112573681798426739 17886901668860522697640109)
        ·
          refine ⟨6707588125822696011615041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17886901668860522697640109 6707588125822696011615041)
          ·
            refine ⟨5030691094367022008711281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6707588125822696011615041 5030691094367022008711281)
            ·
              refine ⟨3773018320775266506533461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5030691094367022008711281 3773018320775266506533461)
              ·
                refine ⟨44215058446585154373439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3773018320775266506533461 44215058446585154373439)
                ·
                  rfl

theorem cell22_1162465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 8].length) (baseStart_1162465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162465 prefixEnd_1162465 := by exact prefixLift 1162465
  have htrace : WordTrace (prefixWord ++ tailWord_1162465) baseStart_1162465 baseEnd_1162465 := by
    simpa [prefixWord, tailWord_1162465, baseEnd_1162465] using wordTrace_append hprefix tailTrace_1162465
  have hstable : (prefixWord ++ tailWord_1162465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162465).length < 2 ^ (prefixWord ++ tailWord_1162465).sum := by decide
  have hdescent : baseEnd_1162465 < baseStart_1162465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162482 : List Nat := [3, 2, 1, 3, 4, 9]
def baseStart_1162482 : Nat := 118140960795 + 1162482 * 2 ^ 59
def prefixEnd_1162482 : Nat := 4983230072969 + 3 ^ 40 * 1162482 * 2
def baseEnd_1162482 : Nat := 4912856116872642119579

theorem tailTrace_1162482 : CollatzResearch.WordTrace tailWord_1162482 prefixEnd_1162482 4912856116872642119579 := by
  unfold tailWord_1162482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10599800443633431241110425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28266134516355816642961133 10599800443633431241110425)
  ·
    refine ⟨7949850332725073430832819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10599800443633431241110425 7949850332725073430832819)
    ·
      refine ⟨11924775499087610146249229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7949850332725073430832819 11924775499087610146249229)
      ·
        refine ⟨4471790812157853804843461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11924775499087610146249229 4471790812157853804843461)
        ·
          refine ⟨838460777279597588408149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4471790812157853804843461 838460777279597588408149)
          ·
            refine ⟨4912856116872642119579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 838460777279597588408149 4912856116872642119579)
            ·
              rfl

theorem cell22_1162482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 9].length) (baseStart_1162482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162482 prefixEnd_1162482 := by exact prefixLift 1162482
  have htrace : WordTrace (prefixWord ++ tailWord_1162482) baseStart_1162482 baseEnd_1162482 := by
    simpa [prefixWord, tailWord_1162482, baseEnd_1162482] using wordTrace_append hprefix tailTrace_1162482
  have hstable : (prefixWord ++ tailWord_1162482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162482).length < 2 ^ (prefixWord ++ tailWord_1162482).sum := by decide
  have hdescent : baseEnd_1162482 < baseStart_1162482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162495 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1162495 : Nat := 118140960795 + 1162495 * 2 ^ 59
def prefixEnd_1162495 : Nat := 4983230072969 + 3 ^ 40 * 1162495 * 2
def baseEnd_1162495 : Nat := 397945795632356311110859

theorem tailTrace_1162495 : CollatzResearch.WordTrace tailWord_1162495 prefixEnd_1162495 397945795632356311110859 := by
  unfold tailWord_1162495
  simp only [CollatzResearch.WordTrace]
  refine ⟨42399675923486628184664939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28266450615657752123109959 42399675923486628184664939)
  ·
    refine ⟨63599513885229942276997409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42399675923486628184664939 63599513885229942276997409)
    ·
      refine ⟨47699635413922456707748057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63599513885229942276997409 47699635413922456707748057)
      ·
        refine ⟨35774726560441842530811043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47699635413922456707748057 35774726560441842530811043)
        ·
          refine ⟨53662089840662763796216565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35774726560441842530811043 53662089840662763796216565)
          ·
            refine ⟨5030820922562134105895303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53662089840662763796216565 5030820922562134105895303)
            ·
              refine ⟨7546231383843201158842955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030820922562134105895303 7546231383843201158842955)
              ·
                refine ⟨11319347075764801738264433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546231383843201158842955 11319347075764801738264433)
                ·
                  refine ⟨8489510306823601303698325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11319347075764801738264433 8489510306823601303698325)
                  ·
                    refine ⟨397945795632356311110859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8489510306823601303698325 397945795632356311110859)
                    ·
                      rfl

theorem cell22_1162495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1162495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162495 prefixEnd_1162495 := by exact prefixLift 1162495
  have htrace : WordTrace (prefixWord ++ tailWord_1162495) baseStart_1162495 baseEnd_1162495 := by
    simpa [prefixWord, tailWord_1162495, baseEnd_1162495] using wordTrace_append hprefix tailTrace_1162495
  have hstable : (prefixWord ++ tailWord_1162495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162495).length < 2 ^ (prefixWord ++ tailWord_1162495).sum := by decide
  have hdescent : baseEnd_1162495 < baseStart_1162495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162531 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 1, 3]
def baseStart_1162531 : Nat := 118140960795 + 1162531 * 2 ^ 59
def prefixEnd_1162531 : Nat := 4983230072969 + 3 ^ 40 * 1162531 * 2
def baseEnd_1162531 : Nat := 397958119168064217210749

theorem tailTrace_1162531 : CollatzResearch.WordTrace tailWord_1162531 prefixEnd_1162531 397958119168064217210749 := by
  unfold tailWord_1162531
  simp only [CollatzResearch.WordTrace]
  refine ⟨42400988951356206332975447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28267325967570804221983631 42400988951356206332975447)
  ·
    refine ⟨63601483427034309499463171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42400988951356206332975447 63601483427034309499463171)
    ·
      refine ⟨95402225140551464249194757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63601483427034309499463171 95402225140551464249194757)
      ·
        refine ⟨17887917213853399546724017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95402225140551464249194757 17887917213853399546724017)
        ·
          refine ⟨13415937910390049660043013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17887917213853399546724017 13415937910390049660043013)
          ·
            refine ⟨2515488358198134311258065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13415937910390049660043013 2515488358198134311258065)
            ·
              refine ⟨1886616268648600733443549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2515488358198134311258065 1886616268648600733443549)
              ·
                refine ⟨707481100743225275041331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1886616268648600733443549 707481100743225275041331)
                ·
                  refine ⟨1061221651114837912561997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 707481100743225275041331 1061221651114837912561997)
                  ·
                    refine ⟨397958119168064217210749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061221651114837912561997 397958119168064217210749)
                    ·
                      rfl

theorem cell22_1162531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 3].length) (baseStart_1162531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162531 prefixEnd_1162531 := by exact prefixLift 1162531
  have htrace : WordTrace (prefixWord ++ tailWord_1162531) baseStart_1162531 baseEnd_1162531 := by
    simpa [prefixWord, tailWord_1162531, baseEnd_1162531] using wordTrace_append hprefix tailTrace_1162531
  have hstable : (prefixWord ++ tailWord_1162531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162531).length < 2 ^ (prefixWord ++ tailWord_1162531).sum := by decide
  have hdescent : baseEnd_1162531 < baseStart_1162531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162561 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 5]
def baseStart_1162561 : Nat := 118140960795 + 1162561 * 2 ^ 59
def prefixEnd_1162561 : Nat := 4983230072969 + 3 ^ 40 * 1162561 * 2
def baseEnd_1162561 : Nat := 132656129593718046320219

theorem tailTrace_1162561 : CollatzResearch.WordTrace tailWord_1162561 prefixEnd_1162561 132656129593718046320219 := by
  unfold tailWord_1162561
  simp only [CollatzResearch.WordTrace]
  refine ⟨42402083141247521456567537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28268055427498347637711691 42402083141247521456567537)
  ·
    refine ⟨31801562355935641092425653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42402083141247521456567537 31801562355935641092425653)
    ·
      refine ⟨2981396470868966352414905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31801562355935641092425653 2981396470868966352414905)
      ·
        refine ⟨2236047353151724764311179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2981396470868966352414905 2236047353151724764311179)
        ·
          refine ⟨3354071029727587146466769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236047353151724764311179 3354071029727587146466769)
          ·
            refine ⟨2515553272295690359850077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354071029727587146466769 2515553272295690359850077)
            ·
              refine ⟨943332477110883884943779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2515553272295690359850077 943332477110883884943779)
              ·
                refine ⟨1414998715666325827415669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943332477110883884943779 1414998715666325827415669)
                ·
                  refine ⟨132656129593718046320219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1414998715666325827415669 132656129593718046320219)
                  ·
                    rfl

theorem cell22_1162561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_1162561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162561 prefixEnd_1162561 := by exact prefixLift 1162561
  have htrace : WordTrace (prefixWord ++ tailWord_1162561) baseStart_1162561 baseEnd_1162561 := by
    simpa [prefixWord, tailWord_1162561, baseEnd_1162561] using wordTrace_append hprefix tailTrace_1162561
  have hstable : (prefixWord ++ tailWord_1162561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162561).length < 2 ^ (prefixWord ++ tailWord_1162561).sum := by decide
  have hdescent : baseEnd_1162561 < baseStart_1162561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162572 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1162572 : Nat := 118140960795 + 1162572 * 2 ^ 59
def prefixEnd_1162572 : Nat := 4983230072969 + 3 ^ 40 * 1162572 * 2
def baseEnd_1162572 : Nat := 132657384768651258978541

theorem tailTrace_1162572 : CollatzResearch.WordTrace tailWord_1162572 prefixEnd_1162572 132657384768651258978541 := by
  unfold tailWord_1162572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21201242172103835167608985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28268322896138446890145313 21201242172103835167608985)
  ·
    refine ⟨15900931629077876375706739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21201242172103835167608985 15900931629077876375706739)
    ·
      refine ⟨23851397443616814563560109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15900931629077876375706739 23851397443616814563560109)
      ·
        refine ⟨8944274041356305461335041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23851397443616814563560109 8944274041356305461335041)
        ·
          refine ⟨6708205531017229096001281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8944274041356305461335041 6708205531017229096001281)
          ·
            refine ⟨5031154148262921822000961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6708205531017229096001281 5031154148262921822000961)
            ·
              refine ⟨3773365611197191366500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031154148262921822000961 3773365611197191366500721)
              ·
                refine ⟨2830024208397893524875541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773365611197191366500721 2830024208397893524875541)
                ·
                  refine ⟨132657384768651258978541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2830024208397893524875541 132657384768651258978541)
                  ·
                    rfl

theorem cell22_1162572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1162572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162572 prefixEnd_1162572 := by exact prefixLift 1162572
  have htrace : WordTrace (prefixWord ++ tailWord_1162572) baseStart_1162572 baseEnd_1162572 := by
    simpa [prefixWord, tailWord_1162572, baseEnd_1162572] using wordTrace_append hprefix tailTrace_1162572
  have hstable : (prefixWord ++ tailWord_1162572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162572).length < 2 ^ (prefixWord ++ tailWord_1162572).sum := by decide
  have hdescent : baseEnd_1162572 < baseStart_1162572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162574 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1162574 : Nat := 118140960795 + 1162574 * 2 ^ 59
def prefixEnd_1162574 : Nat := 4983230072969 + 3 ^ 40 * 1162574 * 2
def baseEnd_1162574 : Nat := 397972838946826438385617

theorem tailTrace_1162574 : CollatzResearch.WordTrace tailWord_1162574 prefixEnd_1162574 397972838946826438385617 := by
  unfold tailWord_1162574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300319661275053084598847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28268371526800283117860517 5300319661275053084598847)
  ·
    refine ⟨7950479491912579626898271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5300319661275053084598847 7950479491912579626898271)
    ·
      refine ⟨11925719237868869440347407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7950479491912579626898271 11925719237868869440347407)
      ·
        refine ⟨17888578856803304160521111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11925719237868869440347407 17888578856803304160521111)
        ·
          refine ⟨26832868285204956240781667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17888578856803304160521111 26832868285204956240781667)
          ·
            refine ⟨40249302427807434361172501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26832868285204956240781667 40249302427807434361172501)
            ·
              refine ⟨1886686051303473485679961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40249302427807434361172501 1886686051303473485679961)
              ·
                refine ⟨1415014538477605114259971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886686051303473485679961 1415014538477605114259971)
                ·
                  refine ⟨2122521807716407671389957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415014538477605114259971 2122521807716407671389957)
                  ·
                    refine ⟨397972838946826438385617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122521807716407671389957 397972838946826438385617)
                    ·
                      rfl

theorem cell22_1162574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1162574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162574 prefixEnd_1162574 := by exact prefixLift 1162574
  have htrace : WordTrace (prefixWord ++ tailWord_1162574) baseStart_1162574 baseEnd_1162574 := by
    simpa [prefixWord, tailWord_1162574, baseEnd_1162574] using wordTrace_append hprefix tailTrace_1162574
  have hstable : (prefixWord ++ tailWord_1162574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162574).length < 2 ^ (prefixWord ++ tailWord_1162574).sum := by decide
  have hdescent : baseEnd_1162574 < baseStart_1162574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162604 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_1162604 : Nat := 118140960795 + 1162604 * 2 ^ 59
def prefixEnd_1162604 : Nat := 4983230072969 + 3 ^ 40 * 1162604 * 2
def baseEnd_1162604 : Nat := 397983108559916360135525

theorem tailTrace_1162604 : CollatzResearch.WordTrace tailWord_1162604 prefixEnd_1162604 397983108559916360135525 := by
  unfold tailWord_1162604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21201825740045869900191433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28269100986727826533588577 21201825740045869900191433)
  ·
    refine ⟨15901369305034402425143575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21201825740045869900191433 15901369305034402425143575)
    ·
      refine ⟨23852053957551603637715363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15901369305034402425143575 23852053957551603637715363)
      ·
        refine ⟨35778080936327405456573045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23852053957551603637715363 35778080936327405456573045)
        ·
          refine ⟨3354195087780694261553723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35778080936327405456573045 3354195087780694261553723)
          ·
            refine ⟨5031292631671041392330585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354195087780694261553723 5031292631671041392330585)
            ·
              refine ⟨3773469473753281044247939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031292631671041392330585 3773469473753281044247939)
              ·
                refine ⟨5660204210629921566371909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773469473753281044247939 5660204210629921566371909)
                ·
                  refine ⟨1061288289493110293694733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5660204210629921566371909 1061288289493110293694733)
                  ·
                    refine ⟨397983108559916360135525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061288289493110293694733 397983108559916360135525)
                    ·
                      rfl

theorem cell22_1162604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_1162604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162604 prefixEnd_1162604 := by exact prefixLift 1162604
  have htrace : WordTrace (prefixWord ++ tailWord_1162604) baseStart_1162604 baseEnd_1162604 := by
    simpa [prefixWord, tailWord_1162604, baseEnd_1162604] using wordTrace_append hprefix tailTrace_1162604
  have hstable : (prefixWord ++ tailWord_1162604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162604).length < 2 ^ (prefixWord ++ tailWord_1162604).sum := by decide
  have hdescent : baseEnd_1162604 < baseStart_1162604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162741 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 6]
def baseStart_1162741 : Nat := 118140960795 + 1162741 * 2 ^ 59
def prefixEnd_1162741 : Nat := 4983230072969 + 3 ^ 40 * 1162741 * 2
def baseEnd_1162741 : Nat := 132676668819897889820035

theorem tailTrace_1162741 : CollatzResearch.WordTrace tailWord_1162741 prefixEnd_1162741 132676668819897889820035 := by
  unfold tailWord_1162741
  simp only [CollatzResearch.WordTrace]
  refine ⟨42408648280595412198120077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28272432187063608132080051 42408648280595412198120077)
  ·
    refine ⟨15903243105223279574295029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42408648280595412198120077 15903243105223279574295029)
    ·
      refine ⟨1490929041114682460090159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15903243105223279574295029 1490929041114682460090159)
      ·
        refine ⟨2236393561672023690135239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1490929041114682460090159 2236393561672023690135239)
        ·
          refine ⟨3354590342508035535202859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236393561672023690135239 3354590342508035535202859)
          ·
            refine ⟨5031885513762053302804289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354590342508035535202859 5031885513762053302804289)
            ·
              refine ⟨3773914135321539977103217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031885513762053302804289 3773914135321539977103217)
              ·
                refine ⟨2830435601491154982827413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773914135321539977103217 2830435601491154982827413)
                ·
                  refine ⟨132676668819897889820035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2830435601491154982827413 132676668819897889820035)
                  ·
                    rfl

theorem cell22_1162741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_1162741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162741 prefixEnd_1162741 := by exact prefixLift 1162741
  have htrace : WordTrace (prefixWord ++ tailWord_1162741) baseStart_1162741 baseEnd_1162741 := by
    simpa [prefixWord, tailWord_1162741, baseEnd_1162741] using wordTrace_append hprefix tailTrace_1162741
  have hstable : (prefixWord ++ tailWord_1162741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162741).length < 2 ^ (prefixWord ++ tailWord_1162741).sum := by decide
  have hdescent : baseEnd_1162741 < baseStart_1162741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1162767 : Nat := 118140960795 + 1162767 * 2 ^ 59
def prefixEnd_1162767 : Nat := 4983230072969 + 3 ^ 40 * 1162767 * 2
def baseEnd_1162767 : Nat := 398038906791038268310025

theorem tailTrace_1162767 : CollatzResearch.WordTrace tailWord_1162767 prefixEnd_1162767 398038906791038268310025 := by
  unfold tailWord_1162767
  simp only [CollatzResearch.WordTrace]
  refine ⟨42409596578501218638566555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28273064385667479092377703 42409596578501218638566555)
  ·
    refine ⟨63614394867751827957849833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42409596578501218638566555 63614394867751827957849833)
    ·
      refine ⟨47710796150813870968387375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63614394867751827957849833 47710796150813870968387375)
      ·
        refine ⟨71566194226220806452581063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47710796150813870968387375 71566194226220806452581063)
        ·
          refine ⟨107349291339331209678871595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71566194226220806452581063 107349291339331209678871595)
          ·
            refine ⟨161023937008996814518307393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107349291339331209678871595 161023937008996814518307393)
            ·
              refine ⟨120767952756747610888730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161023937008996814518307393 120767952756747610888730545)
              ·
                refine ⟨90575964567560708166547909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120767952756747610888730545 90575964567560708166547909)
                ·
                  refine ⟨16982993356417632781227733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90575964567560708166547909 16982993356417632781227733)
                  ·
                    refine ⟨398038906791038268310025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16982993356417632781227733 398038906791038268310025)
                    ·
                      rfl

theorem cell22_1162767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1162767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162767 prefixEnd_1162767 := by exact prefixLift 1162767
  have htrace : WordTrace (prefixWord ++ tailWord_1162767) baseStart_1162767 baseEnd_1162767 := by
    simpa [prefixWord, tailWord_1162767, baseEnd_1162767] using wordTrace_append hprefix tailTrace_1162767
  have hstable : (prefixWord ++ tailWord_1162767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162767).length < 2 ^ (prefixWord ++ tailWord_1162767).sum := by decide
  have hdescent : baseEnd_1162767 < baseStart_1162767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162874 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_1162874 : Nat := 118140960795 + 1162874 * 2 ^ 59
def prefixEnd_1162874 : Nat := 4983230072969 + 3 ^ 40 * 1162874 * 2
def baseEnd_1162874 : Nat := 398075535077725655884697

theorem tailTrace_1162874 : CollatzResearch.WordTrace tailWord_1162874 prefixEnd_1162874 398075535077725655884697 := by
  unfold tailWord_1162874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10603374797278393978177919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28275666126075717275141117 10603374797278393978177919)
  ·
    refine ⟨15905062195917590967266879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10603374797278393978177919 15905062195917590967266879)
    ·
      refine ⟨23857593293876386450900319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15905062195917590967266879 23857593293876386450900319)
      ·
        refine ⟨35786389940814579676350479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23857593293876386450900319 35786389940814579676350479)
        ·
          refine ⟨53679584911221869514525719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35786389940814579676350479 53679584911221869514525719)
          ·
            refine ⟨80519377366832804271788579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53679584911221869514525719 80519377366832804271788579)
            ·
              refine ⟨120779066050249206407682869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80519377366832804271788579 120779066050249206407682869)
              ·
                refine ⟨11323037442210863100720269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120779066050249206407682869 11323037442210863100720269)
                ·
                  refine ⟨4246139040829073662770101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11323037442210863100720269 4246139040829073662770101)
                  ·
                    refine ⟨398075535077725655884697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4246139040829073662770101 398075535077725655884697)
                    ·
                      rfl

theorem cell22_1162874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_1162874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162874 prefixEnd_1162874 := by exact prefixLift 1162874
  have htrace : WordTrace (prefixWord ++ tailWord_1162874) baseStart_1162874 baseEnd_1162874 := by
    simpa [prefixWord, tailWord_1162874, baseEnd_1162874] using wordTrace_append hprefix tailTrace_1162874
  have hstable : (prefixWord ++ tailWord_1162874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162874).length < 2 ^ (prefixWord ++ tailWord_1162874).sum := by decide
  have hdescent : baseEnd_1162874 < baseStart_1162874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162891 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 4, 3]
def baseStart_1162891 : Nat := 118140960795 + 1162891 * 2 ^ 59
def prefixEnd_1162891 : Nat := 4983230072969 + 3 ^ 40 * 1162891 * 2
def baseEnd_1162891 : Nat := 398081354525143278209645

theorem tailTrace_1162891 : CollatzResearch.WordTrace tailWord_1162891 prefixEnd_1162891 398081354525143278209645 := by
  unfold tailWord_1162891
  simp only [CollatzResearch.WordTrace]
  refine ⟨42414119230051987816080527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28276079486701325210720351 42414119230051987816080527)
  ·
    refine ⟨63621178845077981724120791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42414119230051987816080527 63621178845077981724120791)
    ·
      refine ⟨95431768267616972586181187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63621178845077981724120791 95431768267616972586181187)
      ·
        refine ⟨143147652401425458879271781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95431768267616972586181187 143147652401425458879271781)
        ·
          refine ⟨26840184825267273539863459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143147652401425458879271781 26840184825267273539863459)
          ·
            refine ⟨40260277237900910309795189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26840184825267273539863459 40260277237900910309795189)
            ·
              refine ⟨3774400991053210341543299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40260277237900910309795189 3774400991053210341543299)
              ·
                refine ⟨5661601486579815512314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774400991053210341543299 5661601486579815512314949)
                ·
                  refine ⟨1061550278733715408559053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5661601486579815512314949 1061550278733715408559053)
                  ·
                    refine ⟨398081354525143278209645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061550278733715408559053 398081354525143278209645)
                    ·
                      rfl

theorem cell22_1162891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].length) (baseStart_1162891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162891 prefixEnd_1162891 := by exact prefixLift 1162891
  have htrace : WordTrace (prefixWord ++ tailWord_1162891) baseStart_1162891 baseEnd_1162891 := by
    simpa [prefixWord, tailWord_1162891, baseEnd_1162891] using wordTrace_append hprefix tailTrace_1162891
  have hstable : (prefixWord ++ tailWord_1162891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162891).length < 2 ^ (prefixWord ++ tailWord_1162891).sum := by decide
  have hdescent : baseEnd_1162891 < baseStart_1162891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1162936 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_1162936 : Nat := 118140960795 + 1162936 * 2 ^ 59
def prefixEnd_1162936 : Nat := 4983230072969 + 3 ^ 40 * 1162936 * 2
def baseEnd_1162936 : Nat := 398096758944778160834507

theorem tailTrace_1162936 : CollatzResearch.WordTrace tailWord_1162936 prefixEnd_1162936 398096758944778160834507 := by
  unfold tailWord_1162936
  simp only [CollatzResearch.WordTrace]
  refine ⟨21207880257444480250734331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28277173676592640334312441 21207880257444480250734331)
  ·
    refine ⟨31811820386166720376101497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21207880257444480250734331 31811820386166720376101497)
    ·
      refine ⟨23858865289625040282076123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31811820386166720376101497 23858865289625040282076123)
      ·
        refine ⟨35788297934437560423114185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23858865289625040282076123 35788297934437560423114185)
        ·
          refine ⟨26841223450828170317335639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35788297934437560423114185 26841223450828170317335639)
          ·
            refine ⟨40261835176242255476003459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26841223450828170317335639 40261835176242255476003459)
            ·
              refine ⟨60392752764363383214005189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40261835176242255476003459 60392752764363383214005189)
              ·
                refine ⟨11323641143318134352625973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60392752764363383214005189 11323641143318134352625973)
                ·
                  refine ⟨1061591357186075095558685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11323641143318134352625973 1061591357186075095558685)
                  ·
                    refine ⟨398096758944778160834507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061591357186075095558685 398096758944778160834507)
                    ·
                      rfl

theorem cell22_1162936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_1162936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1162936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1162936 prefixEnd_1162936 := by exact prefixLift 1162936
  have htrace : WordTrace (prefixWord ++ tailWord_1162936) baseStart_1162936 baseEnd_1162936 := by
    simpa [prefixWord, tailWord_1162936, baseEnd_1162936] using wordTrace_append hprefix tailTrace_1162936
  have hstable : (prefixWord ++ tailWord_1162936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1162936).length < 2 ^ (prefixWord ++ tailWord_1162936).sum := by decide
  have hdescent : baseEnd_1162936 < baseStart_1162936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1162936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163021 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1163021 : Nat := 118140960795 + 1163021 * 2 ^ 59
def prefixEnd_1163021 : Nat := 4983230072969 + 3 ^ 40 * 1163021 * 2
def baseEnd_1163021 : Nat := 398125856181866272459247

theorem tailTrace_1163021 : CollatzResearch.WordTrace tailWord_1163021 prefixEnd_1163021 398125856181866272459247 := by
  unfold tailWord_1163021
  simp only [CollatzResearch.WordTrace]
  refine ⟨42418860719581020018312917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28279240479720680012208611 42418860719581020018312917)
  ·
    refine ⟨994192048115180156679209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42418860719581020018312917 994192048115180156679209)
    ·
      refine ⟨745644036086385117509407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994192048115180156679209 745644036086385117509407)
      ·
        refine ⟨1118466054129577676264111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745644036086385117509407 1118466054129577676264111)
        ·
          refine ⟨1677699081194366514396167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118466054129577676264111 1677699081194366514396167)
          ·
            refine ⟨2516548621791549771594251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677699081194366514396167 2516548621791549771594251)
            ·
              refine ⟨3774822932687324657391377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516548621791549771594251 3774822932687324657391377)
              ·
                refine ⟨2831117199515493493043533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774822932687324657391377 2831117199515493493043533)
                ·
                  refine ⟨1061668949818310059891325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2831117199515493493043533 1061668949818310059891325)
                  ·
                    refine ⟨398125856181866272459247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1061668949818310059891325 398125856181866272459247)
                    ·
                      rfl

theorem cell22_1163021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1163021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163021 prefixEnd_1163021 := by exact prefixLift 1163021
  have htrace : WordTrace (prefixWord ++ tailWord_1163021) baseStart_1163021 baseEnd_1163021 := by
    simpa [prefixWord, tailWord_1163021, baseEnd_1163021] using wordTrace_append hprefix tailTrace_1163021
  have hstable : (prefixWord ++ tailWord_1163021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163021).length < 2 ^ (prefixWord ++ tailWord_1163021).sum := by decide
  have hdescent : baseEnd_1163021 < baseStart_1163021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163045 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 4]
def baseStart_1163045 : Nat := 118140960795 + 1163045 * 2 ^ 59
def prefixEnd_1163045 : Nat := 4983230072969 + 3 ^ 40 * 1163045 * 2
def baseEnd_1163045 : Nat := 132711357290779403286391

theorem tailTrace_1163045 : CollatzResearch.WordTrace tailWord_1163045 prefixEnd_1163045 132711357290779403286391 := by
  unfold tailWord_1163045
  simp only [CollatzResearch.WordTrace]
  refine ⟨42419736071494072117186589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28279824047662714744791059 42419736071494072117186589)
  ·
    refine ⟨15907401026810277043944971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42419736071494072117186589 15907401026810277043944971)
    ·
      refine ⟨23861101540215415565917457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15907401026810277043944971 23861101540215415565917457)
      ·
        refine ⟨17895826155161561674438093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23861101540215415565917457 17895826155161561674438093)
        ·
          refine ⟨6710934808185585627914285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17895826155161561674438093 6710934808185585627914285)
          ·
            refine ⟨2516600553069594610467857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6710934808185585627914285 2516600553069594610467857)
            ·
              refine ⟨1887450414802195957850893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516600553069594610467857 1887450414802195957850893)
              ·
                refine ⟨707793905550823484194085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1887450414802195957850893 707793905550823484194085)
                ·
                  refine ⟨132711357290779403286391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707793905550823484194085 132711357290779403286391)
                  ·
                    rfl

theorem cell22_1163045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_1163045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163045 prefixEnd_1163045 := by exact prefixLift 1163045
  have htrace : WordTrace (prefixWord ++ tailWord_1163045) baseStart_1163045 baseEnd_1163045 := by
    simpa [prefixWord, tailWord_1163045, baseEnd_1163045] using wordTrace_append hprefix tailTrace_1163045
  have hstable : (prefixWord ++ tailWord_1163045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163045).length < 2 ^ (prefixWord ++ tailWord_1163045).sum := by decide
  have hdescent : baseEnd_1163045 < baseStart_1163045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163062 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1163062 : Nat := 118140960795 + 1163062 * 2 ^ 59
def prefixEnd_1163062 : Nat := 4983230072969 + 3 ^ 40 * 1163062 * 2
def baseEnd_1163062 : Nat := 132713297106585277394707

theorem tailTrace_1163062 : CollatzResearch.WordTrace tailWord_1163062 prefixEnd_1163062 132713297106585277394707 := by
  unfold tailWord_1163062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651272257027030251284715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28280237408288322680370293 2651272257027030251284715)
  ·
    refine ⟨3976908385540545376927073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2651272257027030251284715 3976908385540545376927073)
    ·
      refine ⟨2982681289155409032695305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3976908385540545376927073 2982681289155409032695305)
      ·
        refine ⟨2237010966866556774521479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2982681289155409032695305 2237010966866556774521479)
        ·
          refine ⟨3355516450299835161782219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237010966866556774521479 3355516450299835161782219)
          ·
            refine ⟨5033274675449752742673329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355516450299835161782219 5033274675449752742673329)
            ·
              refine ⟨3774956006587314557004997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5033274675449752742673329 3774956006587314557004997)
              ·
                refine ⟨707804251235121479438437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3774956006587314557004997 707804251235121479438437)
                ·
                  refine ⟨132713297106585277394707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707804251235121479438437 132713297106585277394707)
                  ·
                    rfl

theorem cell22_1163062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1163062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163062 prefixEnd_1163062 := by exact prefixLift 1163062
  have htrace : WordTrace (prefixWord ++ tailWord_1163062) baseStart_1163062 baseEnd_1163062 := by
    simpa [prefixWord, tailWord_1163062, baseEnd_1163062] using wordTrace_append hprefix tailTrace_1163062
  have hstable : (prefixWord ++ tailWord_1163062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163062).length < 2 ^ (prefixWord ++ tailWord_1163062).sum := by decide
  have hdescent : baseEnd_1163062 < baseStart_1163062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163090 : List Nat := [3, 2, 2, 1, 1, 5, 2, 6]
def baseStart_1163090 : Nat := 118140960795 + 1163090 * 2 ^ 59
def prefixEnd_1163090 : Nat := 4983230072969 + 3 ^ 40 * 1163090 * 2
def baseEnd_1163090 : Nat := 44238830699108121387115

theorem tailTrace_1163090 : CollatzResearch.WordTrace tailWord_1163090 prefixEnd_1163090 44238830699108121387115 := by
  unfold tailWord_1163090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605344339082761200643681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28280918237554029868383149 10605344339082761200643681)
  ·
    refine ⟨7954008254312070900482761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10605344339082761200643681 7954008254312070900482761)
    ·
      refine ⟨5965506190734053175362071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7954008254312070900482761 5965506190734053175362071)
      ·
        refine ⟨8948259286101079763043107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965506190734053175362071 8948259286101079763043107)
        ·
          refine ⟨13422388929151619644564661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8948259286101079763043107 13422388929151619644564661)
          ·
            refine ⟨1258348962107964341677937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13422388929151619644564661 1258348962107964341677937)
            ·
              refine ⟨943761721580973256258453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1258348962107964341677937 943761721580973256258453)
              ·
                refine ⟨44238830699108121387115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 943761721580973256258453 44238830699108121387115)
                ·
                  rfl

theorem cell22_1163090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_1163090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163090 prefixEnd_1163090 := by exact prefixLift 1163090
  have htrace : WordTrace (prefixWord ++ tailWord_1163090) baseStart_1163090 baseEnd_1163090 := by
    simpa [prefixWord, tailWord_1163090, baseEnd_1163090] using wordTrace_append hprefix tailTrace_1163090
  have hstable : (prefixWord ++ tailWord_1163090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163090).length < 2 ^ (prefixWord ++ tailWord_1163090).sum := by decide
  have hdescent : baseEnd_1163090 < baseStart_1163090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163131 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_1163131 : Nat := 118140960795 + 1163131 * 2 ^ 59
def prefixEnd_1163131 : Nat := 4983230072969 + 3 ^ 40 * 1163131 * 2
def baseEnd_1163131 : Nat := 398163511429862652208909

theorem tailTrace_1163131 : CollatzResearch.WordTrace tailWord_1163131 prefixEnd_1163131 398163511429862652208909 := by
  unfold tailWord_1163131
  simp only [CollatzResearch.WordTrace]
  refine ⟨42422872749182508804817247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28281915166121672536544831 42422872749182508804817247)
  ·
    refine ⟨63634309123773763207225871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42422872749182508804817247 63634309123773763207225871)
    ·
      refine ⟨95451463685660644810838807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63634309123773763207225871 95451463685660644810838807)
      ·
        refine ⟨143177195528490967216258211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95451463685660644810838807 143177195528490967216258211)
        ·
          refine ⟨214765793292736450824387317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143177195528490967216258211 214765793292736450824387317)
          ·
            refine ⟨20134293121194042264786311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214765793292736450824387317 20134293121194042264786311)
            ·
              refine ⟨30201439681791063397179467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20134293121194042264786311 30201439681791063397179467)
              ·
                refine ⟨45302159522686595095769201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30201439681791063397179467 45302159522686595095769201)
                ·
                  refine ⟨33976619642014946321826901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45302159522686595095769201 33976619642014946321826901)
                  ·
                    refine ⟨398163511429862652208909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33976619642014946321826901 398163511429862652208909)
                    ·
                      rfl

theorem cell22_1163131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_1163131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163131 prefixEnd_1163131 := by exact prefixLift 1163131
  have htrace : WordTrace (prefixWord ++ tailWord_1163131) baseStart_1163131 baseEnd_1163131 := by
    simpa [prefixWord, tailWord_1163131, baseEnd_1163131] using wordTrace_append hprefix tailTrace_1163131
  have hstable : (prefixWord ++ tailWord_1163131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163131).length < 2 ^ (prefixWord ++ tailWord_1163131).sum := by decide
  have hdescent : baseEnd_1163131 < baseStart_1163131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163193 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1163193 : Nat := 118140960795 + 1163193 * 2 ^ 59
def prefixEnd_1163193 : Nat := 4983230072969 + 3 ^ 40 * 1163193 * 2
def baseEnd_1163193 : Nat := 398184735296915157158719

theorem tailTrace_1163193 : CollatzResearch.WordTrace tailWord_1163193 prefixEnd_1163193 398184735296915157158719 := by
  unfold tailWord_1163193
  simp only [CollatzResearch.WordTrace]
  refine ⟨42425134074957893393574233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28283422716638595595716155 42425134074957893393574233)
  ·
    refine ⟨31818850556218420045180675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42425134074957893393574233 31818850556218420045180675)
    ·
      refine ⟨47728275834327630067771013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31818850556218420045180675 47728275834327630067771013)
      ·
        refine ⟨8949051718936430637707065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47728275834327630067771013 8949051718936430637707065)
        ·
          refine ⟨6711788789202322978280299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8949051718936430637707065 6711788789202322978280299)
          ·
            refine ⟨10067683183803484467420449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6711788789202322978280299 10067683183803484467420449)
            ·
              refine ⟨7550762387852613350565337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067683183803484467420449 7550762387852613350565337)
              ·
                refine ⟨5663071790889460012924003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550762387852613350565337 5663071790889460012924003)
                ·
                  refine ⟨8494607686334190019386005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5663071790889460012924003 8494607686334190019386005)
                  ·
                    refine ⟨398184735296915157158719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8494607686334190019386005 398184735296915157158719)
                    ·
                      rfl

theorem cell22_1163193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1163193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163193 prefixEnd_1163193 := by exact prefixLift 1163193
  have htrace : WordTrace (prefixWord ++ tailWord_1163193) baseStart_1163193 baseEnd_1163193 := by
    simpa [prefixWord, tailWord_1163193, baseEnd_1163193] using wordTrace_append hprefix tailTrace_1163193
  have hstable : (prefixWord ++ tailWord_1163193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163193).length < 2 ^ (prefixWord ++ tailWord_1163193).sum := by decide
  have hdescent : baseEnd_1163193 < baseStart_1163193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163210 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1163210 : Nat := 118140960795 + 1163210 * 2 ^ 59
def prefixEnd_1163210 : Nat := 4983230072969 + 3 ^ 40 * 1163210 * 2
def baseEnd_1163210 : Nat := 398190554744332779483667

theorem tailTrace_1163210 : CollatzResearch.WordTrace tailWord_1163210 prefixEnd_1163210 398190554744332779483667 := by
  unfold tailWord_1163210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10606438528974076324235771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28283836077264203531295389 10606438528974076324235771)
  ·
    refine ⟨15909657793461114486353657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10606438528974076324235771 15909657793461114486353657)
    ·
      refine ⟨11932243345095835864765243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15909657793461114486353657 11932243345095835864765243)
      ·
        refine ⟨17898365017643753797147865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11932243345095835864765243 17898365017643753797147865)
        ·
          refine ⟨13423773763232815347860899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17898365017643753797147865 13423773763232815347860899)
          ·
            refine ⟨20135660644849223021791349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13423773763232815347860899 20135660644849223021791349)
            ·
              refine ⟨1887718185454614658292939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20135660644849223021791349 1887718185454614658292939)
              ·
                refine ⟨2831577278181921987439409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887718185454614658292939 2831577278181921987439409)
                ·
                  refine ⟨2123682958636441490579557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831577278181921987439409 2123682958636441490579557)
                  ·
                    refine ⟨398190554744332779483667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2123682958636441490579557 398190554744332779483667)
                    ·
                      rfl

theorem cell22_1163210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1163210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163210 prefixEnd_1163210 := by exact prefixLift 1163210
  have htrace : WordTrace (prefixWord ++ tailWord_1163210) baseStart_1163210 baseEnd_1163210 := by
    simpa [prefixWord, tailWord_1163210, baseEnd_1163210] using wordTrace_append hprefix tailTrace_1163210
  have hstable : (prefixWord ++ tailWord_1163210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163210).length < 2 ^ (prefixWord ++ tailWord_1163210).sum := by decide
  have hdescent : baseEnd_1163210 < baseStart_1163210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163304 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_1163304 : Nat := 118140960795 + 1163304 * 2 ^ 59
def prefixEnd_1163304 : Nat := 4983230072969 + 3 ^ 40 * 1163304 * 2
def baseEnd_1163304 : Nat := 132740910955115955877793

theorem tailTrace_1163304 : CollatzResearch.WordTrace tailWord_1163304 prefixEnd_1163304 132740910955115955877793 := by
  unfold tailWord_1163304
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214591288777879675432483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28286121718370506233909977 21214591288777879675432483)
  ·
    refine ⟨31821886933166819513148725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214591288777879675432483 31821886933166819513148725)
    ·
      refine ⟨2983301899984389329357693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31821886933166819513148725 2983301899984389329357693)
      ·
        refine ⟨1118738212494145998509135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2983301899984389329357693 1118738212494145998509135)
        ·
          refine ⟨1678107318741218997763703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118738212494145998509135 1678107318741218997763703)
          ·
            refine ⟨2517160978111828496645555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678107318741218997763703 2517160978111828496645555)
            ·
              refine ⟨3775741467167742744968333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517160978111828496645555 3775741467167742744968333)
              ·
                refine ⟨1415903050187903529363125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3775741467167742744968333 1415903050187903529363125)
                ·
                  refine ⟨132740910955115955877793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1415903050187903529363125 132740910955115955877793)
                  ·
                    rfl

theorem cell22_1163304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_1163304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163304 prefixEnd_1163304 := by exact prefixLift 1163304
  have htrace : WordTrace (prefixWord ++ tailWord_1163304) baseStart_1163304 baseEnd_1163304 := by
    simpa [prefixWord, tailWord_1163304, baseEnd_1163304] using wordTrace_append hprefix tailTrace_1163304
  have hstable : (prefixWord ++ tailWord_1163304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163304).length < 2 ^ (prefixWord ++ tailWord_1163304).sum := by decide
  have hdescent : baseEnd_1163304 < baseStart_1163304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163317 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1163317 : Nat := 118140960795 + 1163317 * 2 ^ 59
def prefixEnd_1163317 : Nat := 4983230072969 + 3 ^ 40 * 1163317 * 2
def baseEnd_1163317 : Nat := 398227183031020167058339

theorem tailTrace_1163317 : CollatzResearch.WordTrace tailWord_1163317 prefixEnd_1163317 398227183031020167058339 := by
  unfold tailWord_1163317
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429656726508662571088205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28286437817672441714058803 42429656726508662571088205)
  ·
    refine ⟨15911121272440748464158077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42429656726508662571088205 15911121272440748464158077)
    ·
      refine ⟨5966670477165280674059279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15911121272440748464158077 5966670477165280674059279)
      ·
        refine ⟨8950005715747921011088919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966670477165280674059279 8950005715747921011088919)
        ·
          refine ⟨13425008573621881516633379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950005715747921011088919 13425008573621881516633379)
          ·
            refine ⟨20137512860432822274950069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425008573621881516633379 20137512860432822274950069)
            ·
              refine ⟨1887891830665577088276569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20137512860432822274950069 1887891830665577088276569)
              ·
                refine ⟨1415918872999182816207427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1887891830665577088276569 1415918872999182816207427)
                ·
                  refine ⟨2123878309498774224311141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415918872999182816207427 2123878309498774224311141)
                  ·
                    refine ⟨398227183031020167058339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2123878309498774224311141 398227183031020167058339)
                    ·
                      rfl

theorem cell22_1163317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1163317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163317 prefixEnd_1163317 := by exact prefixLift 1163317
  have htrace : WordTrace (prefixWord ++ tailWord_1163317) baseStart_1163317 baseEnd_1163317 := by
    simpa [prefixWord, tailWord_1163317, baseEnd_1163317] using wordTrace_append hprefix tailTrace_1163317
  have hstable : (prefixWord ++ tailWord_1163317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163317).length < 2 ^ (prefixWord ++ tailWord_1163317).sum := by decide
  have hdescent : baseEnd_1163317 < baseStart_1163317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163349 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 4]
def baseStart_1163349 : Nat := 118140960795 + 1163349 * 2 ^ 59
def prefixEnd_1163349 : Nat := 4983230072969 + 3 ^ 40 * 1163349 * 2
def baseEnd_1163349 : Nat := 132746045761660916752747

theorem tailTrace_1163349 : CollatzResearch.WordTrace tailWord_1163349 prefixEnd_1163349 132746045761660916752747 := by
  unfold tailWord_1163349
  simp only [CollatzResearch.WordTrace]
  refine ⟨42430823862392732036253101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28287215908261821357502067 42430823862392732036253101)
  ·
    refine ⟨15911558948397274513594913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42430823862392732036253101 15911558948397274513594913)
    ·
      refine ⟨11933669211297955885196185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15911558948397274513594913 11933669211297955885196185)
      ·
        refine ⟨8950251908473466913897139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11933669211297955885196185 8950251908473466913897139)
        ·
          refine ⟨13425377862710200370845709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950251908473466913897139 13425377862710200370845709)
          ·
            refine ⟨5034516698516325139067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13425377862710200370845709 5034516698516325139067141)
            ·
              refine ⟨943971880971810963575089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5034516698516325139067141 943971880971810963575089)
              ·
                refine ⟨707978910728858222681317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 943971880971810963575089 707978910728858222681317)
                ·
                  refine ⟨132746045761660916752747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 707978910728858222681317 132746045761660916752747)
                  ·
                    rfl

theorem cell22_1163349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_1163349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163349 prefixEnd_1163349 := by exact prefixLift 1163349
  have htrace : WordTrace (prefixWord ++ tailWord_1163349) baseStart_1163349 baseEnd_1163349 := by
    simpa [prefixWord, tailWord_1163349, baseEnd_1163349] using wordTrace_append hprefix tailTrace_1163349
  have hstable : (prefixWord ++ tailWord_1163349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163349).length < 2 ^ (prefixWord ++ tailWord_1163349).sum := by decide
  have hdescent : baseEnd_1163349 < baseStart_1163349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163360 : List Nat := [2, 1, 1, 3, 2, 3, 3, 7]
def baseStart_1163360 : Nat := 118140960795 + 1163360 * 2 ^ 59
def prefixEnd_1163360 : Nat := 4983230072969 + 3 ^ 40 * 1163360 * 2
def baseEnd_1163360 : Nat := 44249100312198043137023

theorem tailTrace_1163360 : CollatzResearch.WordTrace tailWord_1163360 prefixEnd_1163360 44249100312198043137023 := by
  unfold tailWord_1163360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215612532676440457451767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28287483376901920609935689 21215612532676440457451767)
  ·
    refine ⟨31823418799014660686177651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21215612532676440457451767 31823418799014660686177651)
    ·
      refine ⟨47735128198521991029266477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31823418799014660686177651 47735128198521991029266477)
      ·
        refine ⟨17900673074445746635974929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47735128198521991029266477 17900673074445746635974929)
        ·
          refine ⟨13425504805834309976981197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17900673074445746635974929 13425504805834309976981197)
          ·
            refine ⟨5034564302187866241367949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13425504805834309976981197 5034564302187866241367949)
            ·
              refine ⟨1887961613320449840512981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5034564302187866241367949 1887961613320449840512981)
              ·
                refine ⟨44249100312198043137023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1887961613320449840512981 44249100312198043137023)
                ·
                  rfl

theorem cell22_1163360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_1163360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163360 prefixEnd_1163360 := by exact prefixLift 1163360
  have htrace : WordTrace (prefixWord ++ tailWord_1163360) baseStart_1163360 baseEnd_1163360 := by
    simpa [prefixWord, tailWord_1163360, baseEnd_1163360] using wordTrace_append hprefix tailTrace_1163360
  have hstable : (prefixWord ++ tailWord_1163360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163360).length < 2 ^ (prefixWord ++ tailWord_1163360).sum := by decide
  have hdescent : baseEnd_1163360 < baseStart_1163360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163435 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_1163435 : Nat := 118140960795 + 1163435 * 2 ^ 59
def prefixEnd_1163435 : Nat := 4983230072969 + 3 ^ 40 * 1163435 * 2
def baseEnd_1163435 : Nat := 398267576842507192607977

theorem tailTrace_1163435 : CollatzResearch.WordTrace tailWord_1163435 prefixEnd_1163435 398267576842507192607977 := by
  unfold tailWord_1163435
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433960540081168723883759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28289307026720779149255839 42433960540081168723883759)
  ·
    refine ⟨63650940810121753085825639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42433960540081168723883759 63650940810121753085825639)
    ·
      refine ⟨95476411215182629628738459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63650940810121753085825639 95476411215182629628738459)
      ·
        refine ⟨143214616822773944443107689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95476411215182629628738459 143214616822773944443107689)
        ·
          refine ⟨107410962617080458332330767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143214616822773944443107689 107410962617080458332330767)
          ·
            refine ⟨161116443925620687498496151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107410962617080458332330767 161116443925620687498496151)
            ·
              refine ⟨241674665888431031247744227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161116443925620687498496151 241674665888431031247744227)
              ·
                refine ⟨362511998832646546871616341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241674665888431031247744227 362511998832646546871616341)
                ·
                  refine ⟨2124093743160038360575877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 362511998832646546871616341 2124093743160038360575877)
                  ·
                    refine ⟨398267576842507192607977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124093743160038360575877 398267576842507192607977)
                    ·
                      rfl

theorem cell22_1163435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_1163435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163435 prefixEnd_1163435 := by exact prefixLift 1163435
  have htrace : WordTrace (prefixWord ++ tailWord_1163435) baseStart_1163435 baseEnd_1163435 := by
    simpa [prefixWord, tailWord_1163435, baseEnd_1163435] using wordTrace_append hprefix tailTrace_1163435
  have hstable : (prefixWord ++ tailWord_1163435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163435).length < 2 ^ (prefixWord ++ tailWord_1163435).sum := by decide
  have hdescent : baseEnd_1163435 < baseStart_1163435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163450 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_1163450 : Nat := 118140960795 + 1163450 * 2 ^ 59
def prefixEnd_1163450 : Nat := 4983230072969 + 3 ^ 40 * 1163450 * 2
def baseEnd_1163450 : Nat := 132757570549684051160977

theorem tailTrace_1163450 : CollatzResearch.WordTrace tailWord_1163450 prefixEnd_1163450 132757570549684051160977 := by
  unfold tailWord_1163450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10608626908756706571419951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28289671756684550857119869 10608626908756706571419951)
  ·
    refine ⟨15912940363135059857129927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10608626908756706571419951 15912940363135059857129927)
    ·
      refine ⟨23869410544702589785694891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15912940363135059857129927 23869410544702589785694891)
      ·
        refine ⟨35804115817053884678542337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23869410544702589785694891 35804115817053884678542337)
        ·
          refine ⟨26853086862790413508906753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35804115817053884678542337 26853086862790413508906753)
          ·
            refine ⟨20139815147092810131680065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26853086862790413508906753 20139815147092810131680065)
            ·
              refine ⟨15104861360319607598760049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20139815147092810131680065 15104861360319607598760049)
              ·
                refine ⟨11328646020239705699070037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15104861360319607598760049 11328646020239705699070037)
                ·
                  refine ⟨132757570549684051160977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11328646020239705699070037 132757570549684051160977)
                  ·
                    rfl

theorem cell22_1163450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_1163450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163450 prefixEnd_1163450 := by exact prefixLift 1163450
  have htrace : WordTrace (prefixWord ++ tailWord_1163450) baseStart_1163450 baseEnd_1163450 := by
    simpa [prefixWord, tailWord_1163450, baseEnd_1163450] using wordTrace_append hprefix tailTrace_1163450
  have hstable : (prefixWord ++ tailWord_1163450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163450).length < 2 ^ (prefixWord ++ tailWord_1163450).sum := by decide
  have hdescent : baseEnd_1163450 < baseStart_1163450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163465 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1163465 : Nat := 118140960795 + 1163465 * 2 ^ 59
def prefixEnd_1163465 : Nat := 4983230072969 + 3 ^ 40 * 1163465 * 2
def baseEnd_1163465 : Nat := 398277846455597114357885

theorem tailTrace_1163465 : CollatzResearch.WordTrace tailWord_1163465 prefixEnd_1163465 398277846455597114357885 := by
  unfold tailWord_1163465
  simp only [CollatzResearch.WordTrace]
  refine ⟨42435054729972483847475849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28290036486648322564983899 42435054729972483847475849)
  ·
    refine ⟨31826291047479362885606887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42435054729972483847475849 31826291047479362885606887)
    ·
      refine ⟨47739436571219044328410331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31826291047479362885606887 47739436571219044328410331)
      ·
        refine ⟨71609154856828566492615497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47739436571219044328410331 71609154856828566492615497)
        ·
          refine ⟨53706866142621424869461623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71609154856828566492615497 53706866142621424869461623)
          ·
            refine ⟨80560299213932137304192435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53706866142621424869461623 80560299213932137304192435)
            ·
              refine ⟨120840448820898205956288653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80560299213932137304192435 120840448820898205956288653)
              ·
                refine ⟨45315168307836827233608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120840448820898205956288653 45315168307836827233608245)
                ·
                  refine ⟨4248297028859702553150773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45315168307836827233608245 4248297028859702553150773)
                  ·
                    refine ⟨398277846455597114357885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4248297028859702553150773 398277846455597114357885)
                    ·
                      rfl

theorem cell22_1163465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1163465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163465 prefixEnd_1163465 := by exact prefixLift 1163465
  have htrace : WordTrace (prefixWord ++ tailWord_1163465) baseStart_1163465 baseEnd_1163465 := by
    simpa [prefixWord, tailWord_1163465, baseEnd_1163465] using wordTrace_append hprefix tailTrace_1163465
  have hstable : (prefixWord ++ tailWord_1163465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163465).length < 2 ^ (prefixWord ++ tailWord_1163465).sum := by decide
  have hdescent : baseEnd_1163465 < baseStart_1163465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
