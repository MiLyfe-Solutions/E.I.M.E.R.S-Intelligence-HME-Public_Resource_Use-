import V185TrunkScan23Chunk1164

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6901718 : List Nat := [5, 2, 1, 1, 4, 1, 1, 8]
def baseStart_6901718 : Nat := 118140960795 + 6901718 * 2 ^ 59
def prefixEnd_6901718 : Nat := 4983230072969 + 3 ^ 40 * 6901718 * 2
def baseEnd_6901718 : Nat := 131255506510649378899429

theorem tailTrace_6901718 : CollatzResearch.WordTrace tailWord_6901718 prefixEnd_6901718 131255506510649378899429 := by
  unfold tailWord_6901718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15732895975641367527303113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167817557073507920291233205 15732895975641367527303113)
  ·
    refine ⟨11799671981731025645477335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15732895975641367527303113 11799671981731025645477335)
    ·
      refine ⟨17699507972596538468216003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11799671981731025645477335 17699507972596538468216003)
      ·
        refine ⟨26549261958894807702324005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17699507972596538468216003 26549261958894807702324005)
        ·
          refine ⟨4977986617292776444185751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26549261958894807702324005 4977986617292776444185751)
          ·
            refine ⟨7466979925939164666278627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977986617292776444185751 7466979925939164666278627)
            ·
              refine ⟨11200469888908746999417941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466979925939164666278627 11200469888908746999417941)
              ·
                refine ⟨131255506510649378899429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11200469888908746999417941 131255506510649378899429)
                ·
                  rfl

theorem cell23_6901718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_6901718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901718 prefixEnd_6901718 := by exact prefixLift 6901718
  have htrace : WordTrace (prefixWord ++ tailWord_6901718) baseStart_6901718 baseEnd_6901718 := by
    simpa [prefixWord, tailWord_6901718, baseEnd_6901718] using wordTrace_append hprefix tailTrace_6901718
  have hstable : (prefixWord ++ tailWord_6901718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901718).length < 2 ^ (prefixWord ++ tailWord_6901718).sum := by decide
  have hdescent : baseEnd_6901718 < baseStart_6901718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901727 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 8]
def baseStart_6901727 : Nat := 118140960795 + 6901727 * 2 ^ 59
def prefixEnd_6901727 : Nat := 4983230072969 + 3 ^ 40 * 6901727 * 2
def baseEnd_6901727 : Nat := 1181301099037807898357347

theorem tailTrace_6901727 : CollatzResearch.WordTrace tailWord_6901727 prefixEnd_6901727 1181301099037807898357347 := by
  unfold tailWord_6901727
  simp only [CollatzResearch.WordTrace]
  refine ⟨251726663867229274973927435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167817775911486183315951623 251726663867229274973927435)
  ·
    refine ⟨377589995800843912460891153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251726663867229274973927435 377589995800843912460891153)
    ·
      refine ⟨283192496850632934345668365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377589995800843912460891153 283192496850632934345668365)
      ·
        refine ⟨106197186318987350379625637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283192496850632934345668365 106197186318987350379625637)
        ·
          refine ⟨19911972434810128196179807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106197186318987350379625637 19911972434810128196179807)
          ·
            refine ⟨29867958652215192294269711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19911972434810128196179807 29867958652215192294269711)
            ·
              refine ⟨44801937978322788441404567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29867958652215192294269711 44801937978322788441404567)
              ·
                refine ⟨67202906967484182662106851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44801937978322788441404567 67202906967484182662106851)
                ·
                  refine ⟨100804360451226273993160277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67202906967484182662106851 100804360451226273993160277)
                  ·
                    refine ⟨1181301099037807898357347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100804360451226273993160277 1181301099037807898357347)
                    ·
                      rfl

theorem cell23_6901727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_6901727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901727 prefixEnd_6901727 := by exact prefixLift 6901727
  have htrace : WordTrace (prefixWord ++ tailWord_6901727) baseStart_6901727 baseEnd_6901727 := by
    simpa [prefixWord, tailWord_6901727, baseEnd_6901727] using wordTrace_append hprefix tailTrace_6901727
  have hstable : (prefixWord ++ tailWord_6901727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901727).length < 2 ^ (prefixWord ++ tailWord_6901727).sum := by decide
  have hdescent : baseEnd_6901727 < baseStart_6901727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901774 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_6901774 : Nat := 118140960795 + 6901774 * 2 ^ 59
def prefixEnd_6901774 : Nat := 4983230072969 + 3 ^ 40 * 6901774 * 2
def baseEnd_6901774 : Nat := 393769714522687223464925

theorem tailTrace_6901774 : CollatzResearch.WordTrace tailWord_6901774 prefixEnd_6901774 393769714522687223464925 := by
  unfold tailWord_6901774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466047262257375250111047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167818918732039334667258917 31466047262257375250111047)
  ·
    refine ⟨47199070893386062875166571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31466047262257375250111047 47199070893386062875166571)
    ·
      refine ⟨70798606340079094312749857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47199070893386062875166571 70798606340079094312749857)
      ·
        refine ⟨53098954755059320734562393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70798606340079094312749857 53098954755059320734562393)
        ·
          refine ⟨39824216066294490550921795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53098954755059320734562393 39824216066294490550921795)
          ·
            refine ⟨59736324099441735826382693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39824216066294490550921795 59736324099441735826382693)
            ·
              refine ⟨11200560768645325467446755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59736324099441735826382693 11200560768645325467446755)
              ·
                refine ⟨16800841152967988201170133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11200560768645325467446755 16800841152967988201170133)
                ·
                  refine ⟨393769714522687223464925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16800841152967988201170133 393769714522687223464925)
                  ·
                    rfl

theorem cell23_6901774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_6901774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901774 prefixEnd_6901774 := by exact prefixLift 6901774
  have htrace : WordTrace (prefixWord ++ tailWord_6901774) baseStart_6901774 baseEnd_6901774 := by
    simpa [prefixWord, tailWord_6901774, baseEnd_6901774] using wordTrace_append hprefix tailTrace_6901774
  have hstable : (prefixWord ++ tailWord_6901774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901774).length < 2 ^ (prefixWord ++ tailWord_6901774).sum := by decide
  have hdescent : baseEnd_6901774 < baseStart_6901774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901784 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_6901784 : Nat := 118140960795 + 6901784 * 2 ^ 59
def prefixEnd_6901784 : Nat := 4983230072969 + 3 ^ 40 * 6901784 * 2
def baseEnd_6901784 : Nat := 3543932565510729972059279

theorem tailTrace_6901784 : CollatzResearch.WordTrace tailWord_6901784 prefixEnd_6901784 3543932565510729972059279 := by
  unfold tailWord_6901784
  simp only [CollatzResearch.WordTrace]
  refine ⟨125864371414011386854376203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167819161885348515805834937 125864371414011386854376203)
  ·
    refine ⟨188796557121017080281564305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125864371414011386854376203 188796557121017080281564305)
    ·
      refine ⟨141597417840762810211173229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188796557121017080281564305 141597417840762810211173229)
      ·
        refine ⟨53099031690286053829189961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141597417840762810211173229 53099031690286053829189961)
        ·
          refine ⟨39824273767714540371892471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53099031690286053829189961 39824273767714540371892471)
          ·
            refine ⟨59736410651571810557838707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39824273767714540371892471 59736410651571810557838707)
            ·
              refine ⟨89604615977357715836758061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59736410651571810557838707 89604615977357715836758061)
              ·
                refine ⟨33601730991509143438784273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89604615977357715836758061 33601730991509143438784273)
                ·
                  refine ⟨25201298243631857579088205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33601730991509143438784273 25201298243631857579088205)
                  ·
                    refine ⟨9450486841361946592158077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25201298243631857579088205 9450486841361946592158077)
                    ·
                      refine ⟨3543932565510729972059279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450486841361946592158077 3543932565510729972059279)
                      ·
                        rfl

theorem cell23_6901784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_6901784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901784 prefixEnd_6901784 := by exact prefixLift 6901784
  have htrace : WordTrace (prefixWord ++ tailWord_6901784) baseStart_6901784 baseEnd_6901784 := by
    simpa [prefixWord, tailWord_6901784, baseEnd_6901784] using wordTrace_append hprefix tailTrace_6901784
  have hstable : (prefixWord ++ tailWord_6901784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901784).length < 2 ^ (prefixWord ++ tailWord_6901784).sum := by decide
  have hdescent : baseEnd_6901784 < baseStart_6901784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901787 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 6, 5]
def baseStart_6901787 : Nat := 118140960795 + 6901787 * 2 ^ 59
def prefixEnd_6901787 : Nat := 4983230072969 + 3 ^ 40 * 6901787 * 2
def baseEnd_6901787 : Nat := 1181311368650897820107255

theorem tailTrace_6901787 : CollatzResearch.WordTrace tailWord_6901787 prefixEnd_6901787 1181311368650897820107255 := by
  unfold tailWord_6901787
  simp only [CollatzResearch.WordTrace]
  refine ⟨251728852247011905221111615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167819234831341270147407743 251728852247011905221111615)
  ·
    refine ⟨377593278370517857831667423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251728852247011905221111615 377593278370517857831667423)
    ·
      refine ⟨566389917555776786747501135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377593278370517857831667423 566389917555776786747501135)
      ·
        refine ⟨849584876333665180121251703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566389917555776786747501135 849584876333665180121251703)
        ·
          refine ⟨1274377314500497770181877555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849584876333665180121251703 1274377314500497770181877555)
          ·
            refine ⟨1911565971750746655272816333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274377314500497770181877555 1911565971750746655272816333)
            ·
              refine ⟨716837239406529995727306125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911565971750746655272816333 716837239406529995727306125)
              ·
                refine ⟨268813964777448748397739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716837239406529995727306125 268813964777448748397739797)
                ·
                  refine ⟨12600654598942910081144053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 268813964777448748397739797 12600654598942910081144053)
                  ·
                    refine ⟨1181311368650897820107255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12600654598942910081144053 1181311368650897820107255)
                    ·
                      rfl

theorem cell23_6901787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 5].length) (baseStart_6901787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901787 prefixEnd_6901787 := by exact prefixLift 6901787
  have htrace : WordTrace (prefixWord ++ tailWord_6901787) baseStart_6901787 baseEnd_6901787 := by
    simpa [prefixWord, tailWord_6901787, baseEnd_6901787] using wordTrace_append hprefix tailTrace_6901787
  have hstable : (prefixWord ++ tailWord_6901787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901787).length < 2 ^ (prefixWord ++ tailWord_6901787).sum := by decide
  have hdescent : baseEnd_6901787 < baseStart_6901787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901824 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_6901824 : Nat := 118140960795 + 6901824 * 2 ^ 59
def prefixEnd_6901824 : Nat := 4983230072969 + 3 ^ 40 * 6901824 * 2
def baseEnd_6901824 : Nat := 3543953104736909815559095

theorem tailTrace_6901824 : CollatzResearch.WordTrace tailWord_6901824 prefixEnd_6901824 3543953104736909815559095 := by
  unfold tailWord_6901824
  simp only [CollatzResearch.WordTrace]
  refine ⟨125865100873938930270104263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167820134498585240360139017 125865100873938930270104263)
  ·
    refine ⟨188797651310908395405156395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125865100873938930270104263 188797651310908395405156395)
    ·
      refine ⟨283196476966362593107734593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188797651310908395405156395 283196476966362593107734593)
      ·
        refine ⟨212397357724771944830800945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283196476966362593107734593 212397357724771944830800945)
        ·
          refine ⟨159298018293578958623100709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212397357724771944830800945 159298018293578958623100709)
          ·
            refine ⟨29868378430046054741831383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159298018293578958623100709 29868378430046054741831383)
            ·
              refine ⟨44802567645069082112747075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29868378430046054741831383 44802567645069082112747075)
              ·
                refine ⟨67203851467603623169120613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44802567645069082112747075 67203851467603623169120613)
                ·
                  refine ⟨12600722150175679344210115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67203851467603623169120613 12600722150175679344210115)
                  ·
                    refine ⟨18901083225263519016315173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12600722150175679344210115 18901083225263519016315173)
                    ·
                      refine ⟨3543953104736909815559095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18901083225263519016315173 3543953104736909815559095)
                      ·
                        rfl

theorem cell23_6901824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_6901824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901824 prefixEnd_6901824 := by exact prefixLift 6901824
  have htrace : WordTrace (prefixWord ++ tailWord_6901824) baseStart_6901824 baseEnd_6901824 := by
    simpa [prefixWord, tailWord_6901824, baseEnd_6901824] using wordTrace_append hprefix tailTrace_6901824
  have hstable : (prefixWord ++ tailWord_6901824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901824).length < 2 ^ (prefixWord ++ tailWord_6901824).sum := by decide
  have hdescent : baseEnd_6901824 < baseStart_6901824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901827 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5]
def baseStart_6901827 : Nat := 118140960795 + 6901827 * 2 ^ 59
def prefixEnd_6901827 : Nat := 4983230072969 + 3 ^ 40 * 6901827 * 2
def baseEnd_6901827 : Nat := 3543954645178873303821581

theorem tailTrace_6901827 : CollatzResearch.WordTrace tailWord_6901827 prefixEnd_6901827 3543954645178873303821581 := by
  unfold tailWord_6901827
  simp only [CollatzResearch.WordTrace]
  refine ⟨251730311166866992052567735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167820207444577994701711823 251730311166866992052567735)
  ·
    refine ⟨377595466750300488078851603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251730311166866992052567735 377595466750300488078851603)
    ·
      refine ⟨566393200125450732118277405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377595466750300488078851603 566393200125450732118277405)
      ·
        refine ⟨212397450047044024544354027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566393200125450732118277405 212397450047044024544354027)
        ·
          refine ⟨318596175070566036816531041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212397450047044024544354027 318596175070566036816531041)
          ·
            refine ⟨238947131302924527612398281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318596175070566036816531041 238947131302924527612398281)
            ·
              refine ⟨179210348477193395709298711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238947131302924527612398281 179210348477193395709298711)
              ·
                refine ⟨268815522715790093563948067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179210348477193395709298711 268815522715790093563948067)
                ·
                  refine ⟨403223284073685140345922101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268815522715790093563948067 403223284073685140345922101)
                  ·
                    refine ⟨37802182881907981907430197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 403223284073685140345922101 37802182881907981907430197)
                    ·
                      refine ⟨3543954645178873303821581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37802182881907981907430197 3543954645178873303821581)
                      ·
                        rfl

theorem cell23_6901827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_6901827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901827 prefixEnd_6901827 := by exact prefixLift 6901827
  have htrace : WordTrace (prefixWord ++ tailWord_6901827) baseStart_6901827 baseEnd_6901827 := by
    simpa [prefixWord, tailWord_6901827, baseEnd_6901827] using wordTrace_append hprefix tailTrace_6901827
  have hstable : (prefixWord ++ tailWord_6901827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901827).length < 2 ^ (prefixWord ++ tailWord_6901827).sum := by decide
  have hdescent : baseEnd_6901827 < baseStart_6901827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901861 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_6901861 : Nat := 118140960795 + 6901861 * 2 ^ 59
def prefixEnd_6901861 : Nat := 4983230072969 + 3 ^ 40 * 6901861 * 2
def baseEnd_6901861 : Nat := 3543972103521126170796425

theorem tailTrace_6901861 : CollatzResearch.WordTrace tailWord_6901861 prefixEnd_6901861 3543972103521126170796425 := by
  unfold tailWord_6901861
  simp only [CollatzResearch.WordTrace]
  refine ⟨251731551248743815859305437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167821034165829210572870291 251731551248743815859305437)
  ·
    refine ⟨94399331718278930947239539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251731551248743815859305437 94399331718278930947239539)
    ·
      refine ⟨141598997577418396420859309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94399331718278930947239539 141598997577418396420859309)
      ·
        refine ⟨53099624091531898657822241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141598997577418396420859309 53099624091531898657822241)
        ·
          refine ⟨39824718068648923993366681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53099624091531898657822241 39824718068648923993366681)
          ·
            refine ⟨29868538551486692995025011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39824718068648923993366681 29868538551486692995025011)
            ·
              refine ⟨44802807827230039492537517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29868538551486692995025011 44802807827230039492537517)
              ·
                refine ⟨16801052935211264809701569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44802807827230039492537517 16801052935211264809701569)
                ·
                  refine ⟨12600789701408448607276177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16801052935211264809701569 12600789701408448607276177)
                  ·
                    refine ⟨9450592276056336455457133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12600789701408448607276177 9450592276056336455457133)
                    ·
                      refine ⟨3543972103521126170796425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450592276056336455457133 3543972103521126170796425)
                      ·
                        rfl

theorem cell23_6901861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_6901861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901861 prefixEnd_6901861 := by exact prefixLift 6901861
  have htrace : WordTrace (prefixWord ++ tailWord_6901861) baseStart_6901861 baseEnd_6901861 := by
    simpa [prefixWord, tailWord_6901861, baseEnd_6901861] using wordTrace_append hprefix tailTrace_6901861
  have hstable : (prefixWord ++ tailWord_6901861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901861).length < 2 ^ (prefixWord ++ tailWord_6901861).sum := by decide
  have hdescent : baseEnd_6901861 < baseStart_6901861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901878 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6901878 : Nat := 118140960795 + 6901878 * 2 ^ 59
def prefixEnd_6901878 : Nat := 4983230072969 + 3 ^ 40 * 6901878 * 2
def baseEnd_6901878 : Nat := 3543980832692252604283847

theorem tailTrace_6901878 : CollatzResearch.WordTrace tailWord_6901878 prefixEnd_6901878 3543980832692252604283847 := by
  unfold tailWord_6901878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733260705605139235167143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167821447526454818508449525 15733260705605139235167143)
  ·
    refine ⟨23599891058407708852750715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15733260705605139235167143 23599891058407708852750715)
    ·
      refine ⟨35399836587611563279126073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23599891058407708852750715 35399836587611563279126073)
      ·
        refine ⟨26549877440708672459344555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35399836587611563279126073 26549877440708672459344555)
        ·
          refine ⟨39824816161063008689016833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26549877440708672459344555 39824816161063008689016833)
          ·
            refine ⟨29868612120797256516762625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39824816161063008689016833 29868612120797256516762625)
            ·
              refine ⟨22401459090597942387571969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29868612120797256516762625 22401459090597942387571969)
              ·
                refine ⟨16801094317948456790678977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22401459090597942387571969 16801094317948456790678977)
                ·
                  refine ⟨12600820738461342593009233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16801094317948456790678977 12600820738461342593009233)
                  ·
                    refine ⟨9450615553846006944756925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12600820738461342593009233 9450615553846006944756925)
                    ·
                      refine ⟨3543980832692252604283847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450615553846006944756925 3543980832692252604283847)
                      ·
                        rfl

theorem cell23_6901878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6901878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901878 prefixEnd_6901878 := by exact prefixLift 6901878
  have htrace : WordTrace (prefixWord ++ tailWord_6901878) baseStart_6901878 baseEnd_6901878 := by
    simpa [prefixWord, tailWord_6901878, baseEnd_6901878] using wordTrace_append hprefix tailTrace_6901878
  have hstable : (prefixWord ++ tailWord_6901878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901878).length < 2 ^ (prefixWord ++ tailWord_6901878).sum := by decide
  have hdescent : baseEnd_6901878 < baseStart_6901878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901881 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 6]
def baseStart_6901881 : Nat := 118140960795 + 6901881 * 2 ^ 59
def prefixEnd_6901881 : Nat := 4983230072969 + 3 ^ 40 * 6901881 * 2
def baseEnd_6901881 : Nat := 393775819237135121394037

theorem tailTrace_6901881 : CollatzResearch.WordTrace tailWord_6901881 prefixEnd_6901881 393775819237135121394037 := by
  unfold tailWord_6901881
  simp only [CollatzResearch.WordTrace]
  refine ⟨251732280708671359275033497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167821520472447572850022331 251732280708671359275033497)
  ·
    refine ⟨188799210531503519456275123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251732280708671359275033497 188799210531503519456275123)
    ·
      refine ⟨283198815797255279184412685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188799210531503519456275123 283198815797255279184412685)
      ·
        refine ⟨106199555923970729694154757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283198815797255279184412685 106199555923970729694154757)
        ·
          refine ⟨19912416735744511817654017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106199555923970729694154757 19912416735744511817654017)
          ·
            refine ⟨14934312551808383863240513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19912416735744511817654017 14934312551808383863240513)
            ·
              refine ⟨11200734413856287897430385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14934312551808383863240513 11200734413856287897430385)
              ·
                refine ⟨8400550810392215923072789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200734413856287897430385 8400550810392215923072789)
                ·
                  refine ⟨393775819237135121394037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8400550810392215923072789 393775819237135121394037)
                  ·
                    rfl

theorem cell23_6901881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_6901881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901881 prefixEnd_6901881 := by exact prefixLift 6901881
  have htrace : WordTrace (prefixWord ++ tailWord_6901881) baseStart_6901881 baseEnd_6901881 := by
    simpa [prefixWord, tailWord_6901881, baseEnd_6901881] using wordTrace_append hprefix tailTrace_6901881
  have hstable : (prefixWord ++ tailWord_6901881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901881).length < 2 ^ (prefixWord ++ tailWord_6901881).sum := by decide
  have hdescent : baseEnd_6901881 < baseStart_6901881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901885 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_6901885 : Nat := 118140960795 + 6901885 * 2 ^ 59
def prefixEnd_6901885 : Nat := 4983230072969 + 3 ^ 40 * 6901885 * 2
def baseEnd_6901885 : Nat := 1181328142352278025632105

theorem tailTrace_6901885 : CollatzResearch.WordTrace tailWord_6901885 prefixEnd_6901885 1181328142352278025632105 := by
  unfold tailWord_6901885
  simp only [CollatzResearch.WordTrace]
  refine ⟨251732426600656867958179109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167821617733771245305452739 251732426600656867958179109)
  ·
    refine ⟨47199829987623162742158583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251732426600656867958179109 47199829987623162742158583)
    ·
      refine ⟨70799744981434744113237875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47199829987623162742158583 70799744981434744113237875)
      ·
        refine ⟨106199617472152116169856813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70799744981434744113237875 106199617472152116169856813)
        ·
          refine ⟨39824856552057043563696305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106199617472152116169856813 39824856552057043563696305)
          ·
            refine ⟨29868642414042782672772229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39824856552057043563696305 29868642414042782672772229)
            ·
              refine ⟨5600370452633021751144793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29868642414042782672772229 5600370452633021751144793)
              ·
                refine ⟨4200277839474766313358595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600370452633021751144793 4200277839474766313358595)
                ·
                  refine ⟨6300416759212149470037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200277839474766313358595 6300416759212149470037893)
                  ·
                    refine ⟨1181328142352278025632105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300416759212149470037893 1181328142352278025632105)
                    ·
                      rfl

theorem cell23_6901885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_6901885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901885 prefixEnd_6901885 := by exact prefixLift 6901885
  have htrace : WordTrace (prefixWord ++ tailWord_6901885) baseStart_6901885 baseEnd_6901885 := by
    simpa [prefixWord, tailWord_6901885, baseEnd_6901885] using wordTrace_append hprefix tailTrace_6901885
  have hstable : (prefixWord ++ tailWord_6901885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901885).length < 2 ^ (prefixWord ++ tailWord_6901885).sum := by decide
  have hdescent : baseEnd_6901885 < baseStart_6901885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901925 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_6901925 : Nat := 118140960795 + 6901925 * 2 ^ 59
def prefixEnd_6901925 : Nat := 4983230072969 + 3 ^ 40 * 6901925 * 2
def baseEnd_6901925 : Nat := 3544004966283013920396131

theorem tailTrace_6901925 : CollatzResearch.WordTrace tailWord_6901925 prefixEnd_6901925 3544004966283013920396131 := by
  unfold tailWord_6901925
  simp only [CollatzResearch.WordTrace]
  refine ⟨251733885520511954789635229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167822590347007969859756819 251733885520511954789635229)
  ·
    refine ⟨94400207070191983046113211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251733885520511954789635229 94400207070191983046113211)
    ·
      refine ⟨141600310605287974569169817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94400207070191983046113211 141600310605287974569169817)
      ·
        refine ⟨106200232953965980926877363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141600310605287974569169817 106200232953965980926877363)
        ·
          refine ⟨159300349430948971390316045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106200232953965980926877363 159300349430948971390316045)
          ·
            refine ⟨59737631036605864271368517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159300349430948971390316045 59737631036605864271368517)
            ·
              refine ⟨11200805819363599550881597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59737631036605864271368517 11200805819363599550881597)
              ·
                refine ⟨4200302182261349831580599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11200805819363599550881597 4200302182261349831580599)
                ·
                  refine ⟨6300453273392024747370899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200302182261349831580599 6300453273392024747370899)
                  ·
                    refine ⟨9450679910088037121056349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6300453273392024747370899 9450679910088037121056349)
                    ·
                      refine ⟨3544004966283013920396131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450679910088037121056349 3544004966283013920396131)
                      ·
                        rfl

theorem cell23_6901925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_6901925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901925 prefixEnd_6901925 := by exact prefixLift 6901925
  have htrace : WordTrace (prefixWord ++ tailWord_6901925) baseStart_6901925 baseEnd_6901925 := by
    simpa [prefixWord, tailWord_6901925, baseEnd_6901925] using wordTrace_append hprefix tailTrace_6901925
  have hstable : (prefixWord ++ tailWord_6901925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901925).length < 2 ^ (prefixWord ++ tailWord_6901925).sum := by decide
  have hdescent : baseEnd_6901925 < baseStart_6901925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901944 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_6901944 : Nat := 118140960795 + 6901944 * 2 ^ 59
def prefixEnd_6901944 : Nat := 4983230072969 + 3 ^ 40 * 6901944 * 2
def baseEnd_6901944 : Nat := 3544014722415449346058543

theorem tailTrace_6901944 : CollatzResearch.WordTrace tailWord_6901944 prefixEnd_6901944 3544014722415449346058543 := by
  unfold tailWord_6901944
  simp only [CollatzResearch.WordTrace]
  refine ⟨125867289253721560517288443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167823052338295414023051257 125867289253721560517288443)
  ·
    refine ⟨188800933880582340775932665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125867289253721560517288443 188800933880582340775932665)
    ·
      refine ⟨141600700410436755581949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188800933880582340775932665 141600700410436755581949499)
      ·
        refine ⟨212401050615655133372924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141600700410436755581949499 212401050615655133372924249)
        ·
          refine ⟨159300787961741350029693187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212401050615655133372924249 159300787961741350029693187)
          ·
            refine ⟨238951181942612025044539781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159300787961741350029693187 238951181942612025044539781)
            ·
              refine ⟨44803346614239754695851209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238951181942612025044539781 44803346614239754695851209)
              ·
                refine ⟨33602509960679816021888407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44803346614239754695851209 33602509960679816021888407)
                ·
                  refine ⟨50403764941019724032832611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33602509960679816021888407 50403764941019724032832611)
                  ·
                    refine ⟨75605647411529586049248917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50403764941019724032832611 75605647411529586049248917)
                    ·
                      refine ⟨3544014722415449346058543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75605647411529586049248917 3544014722415449346058543)
                      ·
                        rfl

theorem cell23_6901944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_6901944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901944 prefixEnd_6901944 := by exact prefixLift 6901944
  have htrace : WordTrace (prefixWord ++ tailWord_6901944) baseStart_6901944 baseEnd_6901944 := by
    simpa [prefixWord, tailWord_6901944, baseEnd_6901944] using wordTrace_append hprefix tailTrace_6901944
  have hstable : (prefixWord ++ tailWord_6901944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901944).length < 2 ^ (prefixWord ++ tailWord_6901944).sum := by decide
  have hdescent : baseEnd_6901944 < baseStart_6901944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6901999 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 1, 2, 2]
def baseStart_6901999 : Nat := 118140960795 + 6901999 * 2 ^ 59
def prefixEnd_6901999 : Nat := 4983230072969 + 3 ^ 40 * 6901999 * 2
def baseEnd_6901999 : Nat := 3544042963851446630870791

theorem tailTrace_6901999 : CollatzResearch.WordTrace tailWord_6901999 prefixEnd_6901999 3544042963851446630870791 := by
  unfold tailWord_6901999
  simp only [CollatzResearch.WordTrace]
  refine ⟨251736584522243865427829051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167824389681495910285219367 251736584522243865427829051)
  ·
    refine ⟨377604876783365798141743577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251736584522243865427829051 377604876783365798141743577)
    ·
      refine ⟨283203657587524348606307683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377604876783365798141743577 283203657587524348606307683)
      ·
        refine ⟨424805486381286522909461525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283203657587524348606307683 424805486381286522909461525)
        ·
          refine ⟨19912757174122805761381009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 424805486381286522909461525 19912757174122805761381009)
          ·
            refine ⟨14934567880592104321035757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19912757174122805761381009 14934567880592104321035757)
            ·
              refine ⟨5600462955222039120388409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14934567880592104321035757 5600462955222039120388409)
              ·
                refine ⟨4200347216416529340291307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600462955222039120388409 4200347216416529340291307)
                ·
                  refine ⟨6300520824624794010436961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200347216416529340291307 6300520824624794010436961)
                  ·
                    refine ⟨4725390618468595507827721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300520824624794010436961 4725390618468595507827721)
                    ·
                      refine ⟨3544042963851446630870791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725390618468595507827721 3544042963851446630870791)
                      ·
                        rfl

theorem cell23_6901999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 2, 2].length) (baseStart_6901999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6901999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6901999 prefixEnd_6901999 := by exact prefixLift 6901999
  have htrace : WordTrace (prefixWord ++ tailWord_6901999) baseStart_6901999 baseEnd_6901999 := by
    simpa [prefixWord, tailWord_6901999, baseEnd_6901999] using wordTrace_append hprefix tailTrace_6901999
  have hstable : (prefixWord ++ tailWord_6901999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6901999).length < 2 ^ (prefixWord ++ tailWord_6901999).sum := by decide
  have hdescent : baseEnd_6901999 < baseStart_6901999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6901999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902025 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 1, 3, 2]
def baseStart_6902025 : Nat := 118140960795 + 6902025 * 2 ^ 59
def prefixEnd_6902025 : Nat := 4983230072969 + 3 ^ 40 * 6902025 * 2
def baseEnd_6902025 : Nat := 3544056314348463529145671

theorem tailTrace_6902025 : CollatzResearch.WordTrace tailWord_6902025 prefixEnd_6902025 3544056314348463529145671 := by
  unfold tailWord_6902025
  simp only [CollatzResearch.WordTrace]
  refine ⟨251737532820149671868275529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167825021880099781245517019 251737532820149671868275529)
  ·
    refine ⟨188803149615112253901206647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251737532820149671868275529 188803149615112253901206647)
    ·
      refine ⟨283204724422668380851809971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188803149615112253901206647 283204724422668380851809971)
      ·
        refine ⟨424807086634002571277714957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283204724422668380851809971 424807086634002571277714957)
        ·
          refine ⟨159302657487750964229143109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424807086634002571277714957 159302657487750964229143109)
          ·
            refine ⟨29869248278953305792964333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159302657487750964229143109 29869248278953305792964333)
            ·
              refine ⟨11200968104607489672361625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29869248278953305792964333 11200968104607489672361625)
              ·
                refine ⟨8400726078455617254271219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200968104607489672361625 8400726078455617254271219)
                ·
                  refine ⟨12601089117683425881406829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8400726078455617254271219 12601089117683425881406829)
                  ·
                    refine ⟨4725408419131284705527561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12601089117683425881406829 4725408419131284705527561)
                    ·
                      refine ⟨3544056314348463529145671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725408419131284705527561 3544056314348463529145671)
                      ·
                        rfl

theorem cell23_6902025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3, 2].length) (baseStart_6902025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902025 prefixEnd_6902025 := by exact prefixLift 6902025
  have htrace : WordTrace (prefixWord ++ tailWord_6902025) baseStart_6902025 baseEnd_6902025 := by
    simpa [prefixWord, tailWord_6902025, baseEnd_6902025] using wordTrace_append hprefix tailTrace_6902025
  have hstable : (prefixWord ++ tailWord_6902025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902025).length < 2 ^ (prefixWord ++ tailWord_6902025).sum := by decide
  have hdescent : baseEnd_6902025 < baseStart_6902025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902051 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6902051 : Nat := 118140960795 + 6902051 * 2 ^ 59
def prefixEnd_6902051 : Nat := 4983230072969 + 3 ^ 40 * 6902051 * 2
def baseEnd_6902051 : Nat := 3544069664845480427420551

theorem tailTrace_6902051 : CollatzResearch.WordTrace tailWord_6902051 prefixEnd_6902051 3544069664845480427420551 := by
  unfold tailWord_6902051
  simp only [CollatzResearch.WordTrace]
  refine ⟨251738481118055478308722007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167825654078703652205814671 251738481118055478308722007)
  ·
    refine ⟨377607721677083217463083011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251738481118055478308722007 377607721677083217463083011)
    ·
      refine ⟨566411582515624826194624517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377607721677083217463083011 566411582515624826194624517)
      ·
        refine ⟨106202171721679654911492097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566411582515624826194624517 106202171721679654911492097)
        ·
          refine ⟨79651628791259741183619073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106202171721679654911492097 79651628791259741183619073)
          ·
            refine ⟨59738721593444805887714305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79651628791259741183619073 59738721593444805887714305)
            ·
              refine ⟨44804041195083604415785729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59738721593444805887714305 44804041195083604415785729)
              ·
                refine ⟨33603030896312703311839297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44804041195083604415785729 33603030896312703311839297)
                ·
                  refine ⟨25202273172234527483879473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33603030896312703311839297 25202273172234527483879473)
                  ·
                    refine ⟨18901704879175895612909605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25202273172234527483879473 18901704879175895612909605)
                    ·
                      refine ⟨3544069664845480427420551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18901704879175895612909605 3544069664845480427420551)
                      ·
                        rfl

theorem cell23_6902051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6902051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902051 prefixEnd_6902051 := by exact prefixLift 6902051
  have htrace : WordTrace (prefixWord ++ tailWord_6902051) baseStart_6902051 baseEnd_6902051 := by
    simpa [prefixWord, tailWord_6902051, baseEnd_6902051] using wordTrace_append hprefix tailTrace_6902051
  have hstable : (prefixWord ++ tailWord_6902051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902051).length < 2 ^ (prefixWord ++ tailWord_6902051).sum := by decide
  have hdescent : baseEnd_6902051 < baseStart_6902051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902068 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6902068 : Nat := 118140960795 + 6902068 * 2 ^ 59
def prefixEnd_6902068 : Nat := 4983230072969 + 3 ^ 40 * 6902068 * 2
def baseEnd_6902068 : Nat := 3544078394016606860907973

theorem tailTrace_6902068 : CollatzResearch.WordTrace tailWord_6902068 prefixEnd_6902068 3544078394016606860907973 := by
  unfold tailWord_6902068
  simp only [CollatzResearch.WordTrace]
  refine ⟨125869550579496945106045429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167826067439329260141393905 125869550579496945106045429)
  ·
    refine ⟨11800270366827838603691759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125869550579496945106045429 11800270366827838603691759)
    ·
      refine ⟨17700405550241757905537639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11800270366827838603691759 17700405550241757905537639)
      ·
        refine ⟨26550608325362636858306459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17700405550241757905537639 26550608325362636858306459)
        ·
          refine ⟨39825912488043955287459689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26550608325362636858306459 39825912488043955287459689)
          ·
            refine ⟨29869434366032966465594767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39825912488043955287459689 29869434366032966465594767)
            ·
              refine ⟨44804151549049449698392151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29869434366032966465594767 44804151549049449698392151)
              ·
                refine ⟨67206227323574174547588227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44804151549049449698392151 67206227323574174547588227)
                ·
                  refine ⟨100809340985361261821382341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67206227323574174547588227 100809340985361261821382341)
                  ·
                    refine ⟨18901751434755236591509189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100809340985361261821382341 18901751434755236591509189)
                    ·
                      refine ⟨3544078394016606860907973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18901751434755236591509189 3544078394016606860907973)
                      ·
                        rfl

theorem cell23_6902068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6902068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902068 prefixEnd_6902068 := by exact prefixLift 6902068
  have htrace : WordTrace (prefixWord ++ tailWord_6902068) baseStart_6902068 baseEnd_6902068 := by
    simpa [prefixWord, tailWord_6902068, baseEnd_6902068] using wordTrace_append hprefix tailTrace_6902068
  have hstable : (prefixWord ++ tailWord_6902068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902068).length < 2 ^ (prefixWord ++ tailWord_6902068).sum := by decide
  have hdescent : baseEnd_6902068 < baseStart_6902068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902078 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 7]
def baseStart_6902078 : Nat := 118140960795 + 6902078 * 2 ^ 59
def prefixEnd_6902078 : Nat := 4983230072969 + 3 ^ 40 * 6902078 * 2
def baseEnd_6902078 : Nat := 393787058758127980198103

theorem tailTrace_6902078 : CollatzResearch.WordTrace tailWord_6902078 prefixEnd_6902078 393787058758127980198103 := by
  unfold tailWord_6902078
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467433236119707739994361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167826310592638441279969925 31467433236119707739994361)
  ·
    refine ⟨23600574927089780804995771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31467433236119707739994361 23600574927089780804995771)
    ·
      refine ⟨35400862390634671207493657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23600574927089780804995771 35400862390634671207493657)
      ·
        refine ⟨26550646792976003405620243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35400862390634671207493657 26550646792976003405620243)
        ·
          refine ⟨39825970189464005108430365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26550646792976003405620243 39825970189464005108430365)
          ·
            refine ⟨14934738821049001915661387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39825970189464005108430365 14934738821049001915661387)
            ·
              refine ⟨22402108231573502873492081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14934738821049001915661387 22402108231573502873492081)
              ·
                refine ⟨16801581173680127155119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22402108231573502873492081 16801581173680127155119061)
                ·
                  refine ⟨393787058758127980198103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16801581173680127155119061 393787058758127980198103)
                  ·
                    rfl

theorem cell23_6902078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_6902078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902078 prefixEnd_6902078 := by exact prefixLift 6902078
  have htrace : WordTrace (prefixWord ++ tailWord_6902078) baseStart_6902078 baseEnd_6902078 := by
    simpa [prefixWord, tailWord_6902078, baseEnd_6902078] using wordTrace_append hprefix tailTrace_6902078
  have hstable : (prefixWord ++ tailWord_6902078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902078).length < 2 ^ (prefixWord ++ tailWord_6902078).sum := by decide
  have hdescent : baseEnd_6902078 < baseStart_6902078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902091 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 2, 5]
def baseStart_6902091 : Nat := 118140960795 + 6902091 * 2 ^ 59
def prefixEnd_6902091 : Nat := 4983230072969 + 3 ^ 40 * 6902091 * 2
def baseEnd_6902091 : Nat := 1181363401357220090306789

theorem tailTrace_6902091 : CollatzResearch.WordTrace tailWord_6902091 prefixEnd_6902091 1181363401357220090306789 := by
  unfold tailWord_6902091
  simp only [CollatzResearch.WordTrace]
  refine ⟨251739940037910565140178127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167826626691940376760118751 251739940037910565140178127)
  ·
    refine ⟨377609910056865847710267191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251739940037910565140178127 377609910056865847710267191)
    ·
      refine ⟨566414865085298771565400787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377609910056865847710267191 566414865085298771565400787)
      ·
        refine ⟨849622297627948157348101181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566414865085298771565400787 849622297627948157348101181)
        ·
          refine ⟨318608361610480559005537943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849622297627948157348101181 318608361610480559005537943)
          ·
            refine ⟨477912542415720838508306915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318608361610480559005537943 477912542415720838508306915)
            ·
              refine ⟨716868813623581257762460373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477912542415720838508306915 716868813623581257762460373)
              ·
                refine ⟨16801612819302685728807665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 716868813623581257762460373 16801612819302685728807665)
                ·
                  refine ⟨12601209614477014296605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16801612819302685728807665 12601209614477014296605749)
                  ·
                    refine ⟨1181363401357220090306789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12601209614477014296605749 1181363401357220090306789)
                    ·
                      rfl

theorem cell23_6902091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 5].length) (baseStart_6902091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902091 prefixEnd_6902091 := by exact prefixLift 6902091
  have htrace : WordTrace (prefixWord ++ tailWord_6902091) baseStart_6902091 baseEnd_6902091 := by
    simpa [prefixWord, tailWord_6902091, baseEnd_6902091] using wordTrace_append hprefix tailTrace_6902091
  have hstable : (prefixWord ++ tailWord_6902091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902091).length < 2 ^ (prefixWord ++ tailWord_6902091).sum := by decide
  have hdescent : baseEnd_6902091 < baseStart_6902091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902146 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6902146 : Nat := 118140960795 + 6902146 * 2 ^ 59
def prefixEnd_6902146 : Nat := 4983230072969 + 3 ^ 40 * 6902146 * 2
def baseEnd_6902146 : Nat := 393790938389739728414735

theorem tailTrace_6902146 : CollatzResearch.WordTrace tailWord_6902146 prefixEnd_6902146 393790938389739728414735 := by
  unfold tailWord_6902146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62935486513177827383357573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167827964035140873022286861 62935486513177827383357573)
  ·
    refine ⟨11800403721220842634379545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62935486513177827383357573 11800403721220842634379545)
    ·
      refine ⟨8850302790915631975784659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800403721220842634379545 8850302790915631975784659)
      ·
        refine ⟨13275454186373447963676989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850302790915631975784659 13275454186373447963676989)
        ·
          refine ⟨4978295319890042986378871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13275454186373447963676989 4978295319890042986378871)
          ·
            refine ⟨7467442979835064479568307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978295319890042986378871 7467442979835064479568307)
            ·
              refine ⟨11201164469752596719352461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467442979835064479568307 11201164469752596719352461)
              ·
                refine ⟨4200436676157223769757173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11201164469752596719352461 4200436676157223769757173)
                ·
                  refine ⟨393790938389739728414735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4200436676157223769757173 393790938389739728414735)
                  ·
                    rfl

theorem cell23_6902146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6902146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902146 prefixEnd_6902146 := by exact prefixLift 6902146
  have htrace : WordTrace (prefixWord ++ tailWord_6902146) baseStart_6902146 baseEnd_6902146 := by
    simpa [prefixWord, tailWord_6902146, baseEnd_6902146] using wordTrace_append hprefix tailTrace_6902146
  have hstable : (prefixWord ++ tailWord_6902146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902146).length < 2 ^ (prefixWord ++ tailWord_6902146).sum := by decide
  have hdescent : baseEnd_6902146 < baseStart_6902146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902148 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6902148 : Nat := 118140960795 + 6902148 * 2 ^ 59
def prefixEnd_6902148 : Nat := 4983230072969 + 3 ^ 40 * 6902148 * 2
def baseEnd_6902148 : Nat := 3544119472468966547907605

theorem tailTrace_6902148 : CollatzResearch.WordTrace tailWord_6902148 prefixEnd_6902148 3544119472468966547907605 := by
  unfold tailWord_6902148
  simp only [CollatzResearch.WordTrace]
  refine ⟨125871009499352031937501549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167828012665802709250002065 125871009499352031937501549)
  ·
    refine ⟨47201628562257011976563081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125871009499352031937501549 47201628562257011976563081)
    ·
      refine ⟨35401221421692758982422311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47201628562257011976563081 35401221421692758982422311)
      ·
        refine ⟨53101832132539138473633467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35401221421692758982422311 53101832132539138473633467)
        ·
          refine ⟨79652748198808707710450201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53101832132539138473633467 79652748198808707710450201)
          ·
            refine ⟨59739561149106530782837651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79652748198808707710450201 59739561149106530782837651)
            ·
              refine ⟨89609341723659796174256477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59739561149106530782837651 89609341723659796174256477)
              ·
                refine ⟨33603503146372423565346179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89609341723659796174256477 33603503146372423565346179)
                ·
                  refine ⟨50405254719558635348019269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33603503146372423565346179 50405254719558635348019269)
                  ·
                    refine ⟨9450985259917244127753613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50405254719558635348019269 9450985259917244127753613)
                    ·
                      refine ⟨3544119472468966547907605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9450985259917244127753613 3544119472468966547907605)
                      ·
                        rfl

theorem cell23_6902148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6902148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902148 prefixEnd_6902148 := by exact prefixLift 6902148
  have htrace : WordTrace (prefixWord ++ tailWord_6902148) baseStart_6902148 baseEnd_6902148 := by
    simpa [prefixWord, tailWord_6902148, baseEnd_6902148] using wordTrace_append hprefix tailTrace_6902148
  have hstable : (prefixWord ++ tailWord_6902148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902148).length < 2 ^ (prefixWord ++ tailWord_6902148).sum := by decide
  have hdescent : baseEnd_6902148 < baseStart_6902148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902151 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 10]
def baseStart_6902151 : Nat := 118140960795 + 6902151 * 2 ^ 59
def prefixEnd_6902151 : Nat := 4983230072969 + 3 ^ 40 * 6902151 * 2
def baseEnd_6902151 : Nat := 393791223656770004018899

theorem tailTrace_6902151 : CollatzResearch.WordTrace tailWord_6902151 prefixEnd_6902151 393791223656770004018899 := by
  unfold tailWord_6902151
  simp only [CollatzResearch.WordTrace]
  refine ⟨251742128417693195387362307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167828085611795463591574871 251742128417693195387362307)
  ·
    refine ⟨377613192626539793081043461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251742128417693195387362307 377613192626539793081043461)
    ·
      refine ⟨70802473617476211202695649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377613192626539793081043461 70802473617476211202695649)
      ·
        refine ⟨53101855213107158402021737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70802473617476211202695649 53101855213107158402021737)
        ·
          refine ⟨39826391409830368801516303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53101855213107158402021737 39826391409830368801516303)
          ·
            refine ⟨59739587114745553202274455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39826391409830368801516303 59739587114745553202274455)
            ·
              refine ⟨89609380672118329803411683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59739587114745553202274455 89609380672118329803411683)
              ·
                refine ⟨134414071008177494705117525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89609380672118329803411683 134414071008177494705117525)
                ·
                  refine ⟨393791223656770004018899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134414071008177494705117525 393791223656770004018899)
                  ·
                    rfl

theorem cell23_6902151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 10].length) (baseStart_6902151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902151 prefixEnd_6902151 := by exact prefixLift 6902151
  have htrace : WordTrace (prefixWord ++ tailWord_6902151) baseStart_6902151 baseEnd_6902151 := by
    simpa [prefixWord, tailWord_6902151, baseEnd_6902151] using wordTrace_append hprefix tailTrace_6902151
  have hstable : (prefixWord ++ tailWord_6902151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902151).length < 2 ^ (prefixWord ++ tailWord_6902151).sum := by decide
  have hdescent : baseEnd_6902151 < baseStart_6902151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902168 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 8]
def baseStart_6902168 : Nat := 118140960795 + 6902168 * 2 ^ 59
def prefixEnd_6902168 : Nat := 4983230072969 + 3 ^ 40 * 6902168 * 2
def baseEnd_6902168 : Nat := 393792193564672941073057

theorem tailTrace_6902168 : CollatzResearch.WordTrace tailWord_6902168 prefixEnd_6902168 393792193564672941073057 := by
  unfold tailWord_6902168
  simp only [CollatzResearch.WordTrace]
  refine ⟨125871374229315803645365579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167828498972421071527154105 125871374229315803645365579)
  ·
    refine ⟨188807061343973705468048369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125871374229315803645365579 188807061343973705468048369)
    ·
      refine ⟨141605296007980279101036277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188807061343973705468048369 141605296007980279101036277)
      ·
        refine ⟨13275496500748151165722151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141605296007980279101036277 13275496500748151165722151)
        ·
          refine ⟨19913244751122226748583227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13275496500748151165722151 19913244751122226748583227)
          ·
            refine ⟨29869867126683340122874841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19913244751122226748583227 29869867126683340122874841)
            ·
              refine ⟨22402400345012505092156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29869867126683340122874841 22402400345012505092156131)
              ·
                refine ⟨33603600517518757638234197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22402400345012505092156131 33603600517518757638234197)
                ·
                  refine ⟨393792193564672941073057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33603600517518757638234197 393792193564672941073057)
                  ·
                    rfl

theorem cell23_6902168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_6902168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902168 prefixEnd_6902168 := by exact prefixLift 6902168
  have htrace : WordTrace (prefixWord ++ tailWord_6902168) baseStart_6902168 baseEnd_6902168 := by
    simpa [prefixWord, tailWord_6902168, baseEnd_6902168] using wordTrace_append hprefix tailTrace_6902168
  have hstable : (prefixWord ++ tailWord_6902168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902168).length < 2 ^ (prefixWord ++ tailWord_6902168).sum := by decide
  have hdescent : baseEnd_6902168 < baseStart_6902168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902229 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6902229 : Nat := 118140960795 + 6902229 * 2 ^ 59
def prefixEnd_6902229 : Nat := 4983230072969 + 3 ^ 40 * 6902229 * 2
def baseEnd_6902229 : Nat := 3544161064401980730994733

theorem tailTrace_6902229 : CollatzResearch.WordTrace tailWord_6902229 prefixEnd_6902229 3544161064401980730994733 := by
  unfold tailWord_6902229
  simp only [CollatzResearch.WordTrace]
  refine ⟨251744973311410614708701741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167829982207607076472467827 251744973311410614708701741)
  ·
    refine ⟨94404364991778980515763153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251744973311410614708701741 94404364991778980515763153)
    ·
      refine ⟨70803273743834235386822365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94404364991778980515763153 70803273743834235386822365)
      ·
        refine ⟨26551227653937838270058387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70803273743834235386822365 26551227653937838270058387)
        ·
          refine ⟨39826841480906757405087581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26551227653937838270058387 39826841480906757405087581)
          ·
            refine ⟨14935065555340034026907843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39826841480906757405087581 14935065555340034026907843)
            ·
              refine ⟨22402598333010051040361765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935065555340034026907843 22402598333010051040361765)
              ·
                refine ⟨4200487187439384570067831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22402598333010051040361765 4200487187439384570067831)
                ·
                  refine ⟨6300730781159076855101747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200487187439384570067831 6300730781159076855101747)
                  ·
                    refine ⟨9451096171738615282652621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6300730781159076855101747 9451096171738615282652621)
                    ·
                      refine ⟨3544161064401980730994733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9451096171738615282652621 3544161064401980730994733)
                      ·
                        rfl

theorem cell23_6902229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6902229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902229 prefixEnd_6902229 := by exact prefixLift 6902229
  have htrace : WordTrace (prefixWord ++ tailWord_6902229) baseStart_6902229 baseEnd_6902229 := by
    simpa [prefixWord, tailWord_6902229, baseEnd_6902229] using wordTrace_append hprefix tailTrace_6902229
  have hstable : (prefixWord ++ tailWord_6902229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902229).length < 2 ^ (prefixWord ++ tailWord_6902229).sum := by decide
  have hdescent : baseEnd_6902229 < baseStart_6902229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902252 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_6902252 : Nat := 118140960795 + 6902252 * 2 ^ 59
def prefixEnd_6902252 : Nat := 4983230072969 + 3 ^ 40 * 6902252 * 2
def baseEnd_6902252 : Nat := 3544172874457034141007127

theorem tailTrace_6902252 : CollatzResearch.WordTrace tailWord_6902252 prefixEnd_6902252 3544172874457034141007127 := by
  unfold tailWord_6902252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125872906095163644818394505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167830541460218193091192673 125872906095163644818394505)
  ·
    refine ⟨94404679571372733613795879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125872906095163644818394505 94404679571372733613795879)
    ·
      refine ⟨141607019357059100420693819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94404679571372733613795879 141607019357059100420693819)
      ·
        refine ⟨212410529035588650631040729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141607019357059100420693819 212410529035588650631040729)
        ·
          refine ⟨159307896776691487973280547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212410529035588650631040729 159307896776691487973280547)
          ·
            refine ⟨238961845165037231959920821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159307896776691487973280547 238961845165037231959920821)
            ·
              refine ⟨22402672984222240496242577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238961845165037231959920821 22402672984222240496242577)
              ·
                refine ⟨16802004738166680372181933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22402672984222240496242577 16802004738166680372181933)
                ·
                  refine ⟨6300751776812505139568225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16802004738166680372181933 6300751776812505139568225)
                  ·
                    refine ⟨4725563832609378854676169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300751776812505139568225 4725563832609378854676169)
                    ·
                      refine ⟨3544172874457034141007127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725563832609378854676169 3544172874457034141007127)
                      ·
                        rfl

theorem cell23_6902252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_6902252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902252 prefixEnd_6902252 := by exact prefixLift 6902252
  have htrace : WordTrace (prefixWord ++ tailWord_6902252) baseStart_6902252 baseEnd_6902252 := by
    simpa [prefixWord, tailWord_6902252, baseEnd_6902252] using wordTrace_append hprefix tailTrace_6902252
  have hstable : (prefixWord ++ tailWord_6902252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902252).length < 2 ^ (prefixWord ++ tailWord_6902252).sum := by decide
  have hdescent : baseEnd_6902252 < baseStart_6902252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902255 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_6902255 : Nat := 118140960795 + 6902255 * 2 ^ 59
def prefixEnd_6902255 : Nat := 4983230072969 + 3 ^ 40 * 6902255 * 2
def baseEnd_6902255 : Nat := 3544174414898997629269613

theorem tailTrace_6902255 : CollatzResearch.WordTrace tailWord_6902255 prefixEnd_6902255 3544174414898997629269613 := by
  unfold tailWord_6902255
  simp only [CollatzResearch.WordTrace]
  refine ⟨251745921609316421149148219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167830614406210947432765479 251745921609316421149148219)
  ·
    refine ⟨377618882413974631723722329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251745921609316421149148219 377618882413974631723722329)
    ·
      refine ⟨283214161810480973792791747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377618882413974631723722329 283214161810480973792791747)
      ·
        refine ⟨424821242715721460689187621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283214161810480973792791747 424821242715721460689187621)
        ·
          refine ⟨79653983009197773879222679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424821242715721460689187621 79653983009197773879222679)
          ·
            refine ⟨119480974513796660818834019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79653983009197773879222679 119480974513796660818834019)
            ·
              refine ⟨179221461770694991228251029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119480974513796660818834019 179221461770694991228251029)
              ·
                refine ⟨8401006020501327713824267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179221461770694991228251029 8401006020501327713824267)
                ·
                  refine ⟨12601509030751991570736401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401006020501327713824267 12601509030751991570736401)
                  ·
                    refine ⟨9451131773063993678052301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12601509030751991570736401 9451131773063993678052301)
                    ·
                      refine ⟨3544174414898997629269613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9451131773063993678052301 3544174414898997629269613)
                      ·
                        rfl

theorem cell23_6902255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_6902255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902255 prefixEnd_6902255 := by exact prefixLift 6902255
  have htrace : WordTrace (prefixWord ++ tailWord_6902255) baseStart_6902255 baseEnd_6902255 := by
    simpa [prefixWord, tailWord_6902255, baseEnd_6902255] using wordTrace_append hprefix tailTrace_6902255
  have hstable : (prefixWord ++ tailWord_6902255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902255).length < 2 ^ (prefixWord ++ tailWord_6902255).sum := by decide
  have hdescent : baseEnd_6902255 < baseStart_6902255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902279 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 2, 4]
def baseStart_6902279 : Nat := 118140960795 + 6902279 * 2 ^ 59
def prefixEnd_6902279 : Nat := 4983230072969 + 3 ^ 40 * 6902279 * 2
def baseEnd_6902279 : Nat := 1181395579478235178456501

theorem tailTrace_6902279 : CollatzResearch.WordTrace tailWord_6902279 prefixEnd_6902279 1181395579478235178456501 := by
  unfold tailWord_6902279
  simp only [CollatzResearch.WordTrace]
  refine ⟨251746796961229473248021891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167831197974152982165347927 251746796961229473248021891)
  ·
    refine ⟨377620195441844209872032837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251746796961229473248021891 377620195441844209872032837)
    ·
      refine ⟨70803786645345789351006157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377620195441844209872032837 70803786645345789351006157)
      ·
        refine ⟨26551419992004671006627309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70803786645345789351006157 26551419992004671006627309)
        ·
          refine ⟨9956782497001751627485241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26551419992004671006627309 9956782497001751627485241)
          ·
            refine ⟨7467586872751313720613931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9956782497001751627485241 7467586872751313720613931)
            ·
              refine ⟨11201380309126970580920897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467586872751313720613931 11201380309126970580920897)
              ·
                refine ⟨8401035231845227935690673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11201380309126970580920897 8401035231845227935690673)
                ·
                  refine ⟨6300776423883920951768005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8401035231845227935690673 6300776423883920951768005)
                  ·
                    refine ⟨1181395579478235178456501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300776423883920951768005 1181395579478235178456501)
                    ·
                      rfl

theorem cell23_6902279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_6902279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902279 prefixEnd_6902279 := by exact prefixLift 6902279
  have htrace : WordTrace (prefixWord ++ tailWord_6902279) baseStart_6902279 baseEnd_6902279 := by
    simpa [prefixWord, tailWord_6902279, baseEnd_6902279] using wordTrace_append hprefix tailTrace_6902279
  have hstable : (prefixWord ++ tailWord_6902279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902279).length < 2 ^ (prefixWord ++ tailWord_6902279).sum := by decide
  have hdescent : baseEnd_6902279 < baseStart_6902279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902286 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6902286 : Nat := 118140960795 + 6902286 * 2 ^ 59
def prefixEnd_6902286 : Nat := 4983230072969 + 3 ^ 40 * 6902286 * 2
def baseEnd_6902286 : Nat := 3544190332799287007981971

theorem tailTrace_6902286 : CollatzResearch.WordTrace tailWord_6902286 prefixEnd_6902286 3544190332799287007981971 := by
  unfold tailWord_6902286
  simp only [CollatzResearch.WordTrace]
  refine ⟨31468381534025514180440839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167831368181469408962351141 31468381534025514180440839)
  ·
    refine ⟨47202572301038271270661259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31468381534025514180440839 47202572301038271270661259)
    ·
      refine ⟨70803858451557406905991889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47202572301038271270661259 70803858451557406905991889)
      ·
        refine ⟨53102893838668055179493917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70803858451557406905991889 53102893838668055179493917)
        ·
          refine ⟨19913585189500520692310219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53102893838668055179493917 19913585189500520692310219)
          ·
            refine ⟨29870377784250781038465329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19913585189500520692310219 29870377784250781038465329)
            ·
              refine ⟨22402783338188085778848997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29870377784250781038465329 22402783338188085778848997)
              ·
                refine ⟨4200521875910266083534187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22402783338188085778848997 4200521875910266083534187)
                ·
                  refine ⟨6300782813865399125301281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200521875910266083534187 6300782813865399125301281)
                  ·
                    refine ⟨4725587110399049343975961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300782813865399125301281 4725587110399049343975961)
                    ·
                      refine ⟨3544190332799287007981971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725587110399049343975961 3544190332799287007981971)
                      ·
                        rfl

theorem cell23_6902286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6902286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902286 prefixEnd_6902286 := by exact prefixLift 6902286
  have htrace : WordTrace (prefixWord ++ tailWord_6902286) baseStart_6902286 baseEnd_6902286 := by
    simpa [prefixWord, tailWord_6902286, baseEnd_6902286] using wordTrace_append hprefix tailTrace_6902286
  have hstable : (prefixWord ++ tailWord_6902286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902286).length < 2 ^ (prefixWord ++ tailWord_6902286).sum := by decide
  have hdescent : baseEnd_6902286 < baseStart_6902286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902359 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_6902359 : Nat := 118140960795 + 6902359 * 2 ^ 59
def prefixEnd_6902359 : Nat := 4983230072969 + 3 ^ 40 * 6902359 * 2
def baseEnd_6902359 : Nat := 3544227816887065222369135

theorem tailTrace_6902359 : CollatzResearch.WordTrace tailWord_6902359 prefixEnd_6902359 3544227816887065222369135 := by
  unfold tailWord_6902359
  simp only [CollatzResearch.WordTrace]
  refine ⟨251749714800939646910934131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167833143200626431273956087 251749714800939646910934131)
  ·
    refine ⟨377624572201409470366401197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251749714800939646910934131 377624572201409470366401197)
    ·
      refine ⟨141609214575528551387400449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377624572201409470366401197 141609214575528551387400449)
      ·
        refine ⟨106206910931646413540550337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141609214575528551387400449 106206910931646413540550337)
        ·
          refine ⟨79655183198734810155412753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106206910931646413540550337 79655183198734810155412753)
          ·
            refine ⟨59741387399051107616559565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79655183198734810155412753 59741387399051107616559565)
            ·
              refine ⟨22403020274644165356209837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59741387399051107616559565 22403020274644165356209837)
              ·
                refine ⟨8401132602991562008578689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22403020274644165356209837 8401132602991562008578689)
                ·
                  refine ⟨6300849452243671506434017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8401132602991562008578689 6300849452243671506434017)
                  ·
                    refine ⟨4725637089182753629825513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300849452243671506434017 4725637089182753629825513)
                    ·
                      refine ⟨3544227816887065222369135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725637089182753629825513 3544227816887065222369135)
                      ·
                        rfl

theorem cell23_6902359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_6902359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902359 prefixEnd_6902359 := by exact prefixLift 6902359
  have htrace : WordTrace (prefixWord ++ tailWord_6902359) baseStart_6902359 baseEnd_6902359 := by
    simpa [prefixWord, tailWord_6902359, baseEnd_6902359] using wordTrace_append hprefix tailTrace_6902359
  have hstable : (prefixWord ++ tailWord_6902359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902359).length < 2 ^ (prefixWord ++ tailWord_6902359).sum := by decide
  have hdescent : baseEnd_6902359 < baseStart_6902359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902375 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_6902375 : Nat := 118140960795 + 6902375 * 2 ^ 59
def prefixEnd_6902375 : Nat := 4983230072969 + 3 ^ 40 * 6902375 * 2
def baseEnd_6902375 : Nat := 3544236032577537159769061

theorem tailTrace_6902375 : CollatzResearch.WordTrace tailWord_6902375 prefixEnd_6902375 3544236032577537159769061 := by
  unfold tailWord_6902375
  simp only [CollatzResearch.WordTrace]
  refine ⟨251750298368881681643516579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167833532245921121095677719 251750298368881681643516579)
  ·
    refine ⟨377625447553322522465274869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251750298368881681643516579 377625447553322522465274869)
    ·
      refine ⟨35402385708123986481119519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 377625447553322522465274869 35402385708123986481119519)
      ·
        refine ⟨53103578562185979721679279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35402385708123986481119519 53103578562185979721679279)
        ·
          refine ⟨79655367843278969582518919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53103578562185979721679279 79655367843278969582518919)
          ·
            refine ⟨119483051764918454373778379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79655367843278969582518919 119483051764918454373778379)
            ·
              refine ⟨179224577647377681560667569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119483051764918454373778379 179224577647377681560667569)
              ·
                refine ⟨134418433235533261170500677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179224577647377681560667569 134418433235533261170500677)
                ·
                  refine ⟨25203456231662486469468877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134418433235533261170500677 25203456231662486469468877)
                  ·
                    refine ⟨9451296086873432426050829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25203456231662486469468877 9451296086873432426050829)
                    ·
                      refine ⟨3544236032577537159769061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9451296086873432426050829 3544236032577537159769061)
                      ·
                        rfl

theorem cell23_6902375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_6902375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902375 prefixEnd_6902375 := by exact prefixLift 6902375
  have htrace : WordTrace (prefixWord ++ tailWord_6902375) baseStart_6902375 baseEnd_6902375 := by
    simpa [prefixWord, tailWord_6902375, baseEnd_6902375] using wordTrace_append hprefix tailTrace_6902375
  have hstable : (prefixWord ++ tailWord_6902375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902375).length < 2 ^ (prefixWord ++ tailWord_6902375).sum := by decide
  have hdescent : baseEnd_6902375 < baseStart_6902375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902405 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_6902405 : Nat := 118140960795 + 6902405 * 2 ^ 59
def prefixEnd_6902405 : Nat := 4983230072969 + 3 ^ 40 * 6902405 * 2
def baseEnd_6902405 : Nat := 3544251436997172042393923

theorem tailTrace_6902405 : CollatzResearch.WordTrace tailWord_6902405 prefixEnd_6902405 3544251436997172042393923 := by
  unfold tailWord_6902405
  simp only [CollatzResearch.WordTrace]
  refine ⟨251751392558772996767108669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167834261705848664511405779 251751392558772996767108669)
  ·
    refine ⟨94406772209539873787665751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251751392558772996767108669 94406772209539873787665751)
    ·
      refine ⟨141610158314309810681498627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94406772209539873787665751 141610158314309810681498627)
      ·
        refine ⟨212415237471464716022247941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141610158314309810681498627 212415237471464716022247941)
        ·
          refine ⟨39827857025899634254171489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212415237471464716022247941 39827857025899634254171489)
          ·
            refine ⟨29870892769424725690628617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39827857025899634254171489 29870892769424725690628617)
            ·
              refine ⟨22403169577068544267971463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29870892769424725690628617 22403169577068544267971463)
              ·
                refine ⟨33604754365602816401957195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22403169577068544267971463 33604754365602816401957195)
                ·
                  refine ⟨50407131548404224602935793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33604754365602816401957195 50407131548404224602935793)
                  ·
                    refine ⟨37805348661303168452201845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50407131548404224602935793 37805348661303168452201845)
                    ·
                      refine ⟨3544251436997172042393923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37805348661303168452201845 3544251436997172042393923)
                      ·
                        rfl

theorem cell23_6902405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_6902405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902405 prefixEnd_6902405 := by exact prefixLift 6902405
  have htrace : WordTrace (prefixWord ++ tailWord_6902405) baseStart_6902405 baseEnd_6902405 := by
    simpa [prefixWord, tailWord_6902405, baseEnd_6902405] using wordTrace_append hprefix tailTrace_6902405
  have hstable : (prefixWord ++ tailWord_6902405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902405).length < 2 ^ (prefixWord ++ tailWord_6902405).sum := by decide
  have hdescent : baseEnd_6902405 < baseStart_6902405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902432 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_6902432 : Nat := 118140960795 + 6902432 * 2 ^ 59
def prefixEnd_6902432 : Nat := 4983230072969 + 3 ^ 40 * 6902432 * 2
def baseEnd_6902432 : Nat := 3544265300974843436756299

theorem tailTrace_6902432 : CollatzResearch.WordTrace tailWord_6902432 prefixEnd_6902432 3544265300974843436756299 := by
  unfold tailWord_6902432
  simp only [CollatzResearch.WordTrace]
  refine ⟨125876188664837590189170775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167834918219783453585561033 125876188664837590189170775)
  ·
    refine ⟨188814282997256385283756163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125876188664837590189170775 188814282997256385283756163)
    ·
      refine ⟨283221424495884577925634245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188814282997256385283756163 283221424495884577925634245)
      ·
        refine ⟨53104017092978358361056421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283221424495884577925634245 53104017092978358361056421)
        ·
          refine ⟨9957003204933442192698079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53104017092978358361056421 9957003204933442192698079)
          ·
            refine ⟨14935504807400163289047119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957003204933442192698079 14935504807400163289047119)
            ·
              refine ⟨22403257211100244933570679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935504807400163289047119 22403257211100244933570679)
              ·
                refine ⟨33604885816650367400356019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22403257211100244933570679 33604885816650367400356019)
                ·
                  refine ⟨50407328724975551100534029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33604885816650367400356019 50407328724975551100534029)
                  ·
                    refine ⟨18902748271865831662700261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50407328724975551100534029 18902748271865831662700261)
                    ·
                      refine ⟨3544265300974843436756299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18902748271865831662700261 3544265300974843436756299)
                      ·
                        rfl

theorem cell23_6902432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_6902432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902432 prefixEnd_6902432 := by exact prefixLift 6902432
  have htrace : WordTrace (prefixWord ++ tailWord_6902432) baseStart_6902432 baseEnd_6902432 := by
    simpa [prefixWord, tailWord_6902432, baseEnd_6902432] using wordTrace_append hprefix tailTrace_6902432
  have hstable : (prefixWord ++ tailWord_6902432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902432).length < 2 ^ (prefixWord ++ tailWord_6902432).sum := by decide
  have hdescent : baseEnd_6902432 < baseStart_6902432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902532 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6902532 : Nat := 118140960795 + 6902532 * 2 ^ 59
def prefixEnd_6902532 : Nat := 4983230072969 + 3 ^ 40 * 6902532 * 2
def baseEnd_6902532 : Nat := 1181438883013431015168613

theorem tailTrace_6902532 : CollatzResearch.WordTrace tailWord_6902532 prefixEnd_6902532 1181438883013431015168613 := by
  unfold tailWord_6902532
  simp only [CollatzResearch.WordTrace]
  refine ⟨125878012314656448728490925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167837349752875264971321233 125878012314656448728490925)
  ·
    refine ⟨47204254617996168273184097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125878012314656448728490925 47204254617996168273184097)
    ·
      refine ⟨35403190963497126204888073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47204254617996168273184097 35403190963497126204888073)
      ·
        refine ⟨26552393222622844653666055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35403190963497126204888073 26552393222622844653666055)
        ·
          refine ⟨39828589833934266980499083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26552393222622844653666055 39828589833934266980499083)
          ·
            refine ⟨59742884750901400470748625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39828589833934266980499083 59742884750901400470748625)
            ·
              refine ⟨44807163563176050353061469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59742884750901400470748625 44807163563176050353061469)
              ·
                refine ⟨16802686336191018882398051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44807163563176050353061469 16802686336191018882398051)
                ·
                  refine ⟨25204029504286528323597077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16802686336191018882398051 25204029504286528323597077)
                  ·
                    refine ⟨1181438883013431015168613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25204029504286528323597077 1181438883013431015168613)
                    ·
                      rfl

theorem cell23_6902532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6902532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902532 prefixEnd_6902532 := by exact prefixLift 6902532
  have htrace : WordTrace (prefixWord ++ tailWord_6902532) baseStart_6902532 baseEnd_6902532 := by
    simpa [prefixWord, tailWord_6902532, baseEnd_6902532] using wordTrace_append hprefix tailTrace_6902532
  have hstable : (prefixWord ++ tailWord_6902532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902532).length < 2 ^ (prefixWord ++ tailWord_6902532).sum := by decide
  have hdescent : baseEnd_6902532 < baseStart_6902532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902539 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 5, 2, 2]
def baseStart_6902539 : Nat := 118140960795 + 6902539 * 2 ^ 59
def prefixEnd_6902539 : Nat := 4983230072969 + 3 ^ 40 * 6902539 * 2
def baseEnd_6902539 : Nat := 3544320243404874518118307

theorem tailTrace_6902539 : CollatzResearch.WordTrace tailWord_6902539 prefixEnd_6902539 3544320243404874518118307 := by
  unfold tailWord_6902539
  simp only [CollatzResearch.WordTrace]
  refine ⟨251756279940287537652486671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167837519960191691768324447 251756279940287537652486671)
  ·
    refine ⟨377634419910431306478730007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251756279940287537652486671 377634419910431306478730007)
    ·
      refine ⟨566451629865646959718095011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377634419910431306478730007 566451629865646959718095011)
      ·
        refine ⟨849677444798470439577142517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566451629865646959718095011 849677444798470439577142517)
        ·
          refine ⟨79657260449856603710357111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 849677444798470439577142517 79657260449856603710357111)
          ·
            refine ⟨119485890674784905565535667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79657260449856603710357111 119485890674784905565535667)
            ·
              refine ⟨179228836012177358348303501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119485890674784905565535667 179228836012177358348303501)
              ·
                refine ⟨67210813504566509380613813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179228836012177358348303501 67210813504566509380613813)
                ·
                  refine ⟨6301013766053110254432545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67210813504566509380613813 6301013766053110254432545)
                  ·
                    refine ⟨4725760324539832690824409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6301013766053110254432545 4725760324539832690824409)
                    ·
                      refine ⟨3544320243404874518118307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725760324539832690824409 3544320243404874518118307)
                      ·
                        rfl

theorem cell23_6902539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 2, 2].length) (baseStart_6902539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902539 prefixEnd_6902539 := by exact prefixLift 6902539
  have htrace : WordTrace (prefixWord ++ tailWord_6902539) baseStart_6902539 baseEnd_6902539 := by
    simpa [prefixWord, tailWord_6902539, baseEnd_6902539] using wordTrace_append hprefix tailTrace_6902539
  have hstable : (prefixWord ++ tailWord_6902539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902539).length < 2 ^ (prefixWord ++ tailWord_6902539).sum := by decide
  have hdescent : baseEnd_6902539 < baseStart_6902539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902545 : List Nat := [1, 2, 2, 1, 1, 3, 4, 9]
def baseStart_6902545 : Nat := 118140960795 + 6902545 * 2 ^ 59
def prefixEnd_6902545 : Nat := 4983230072969 + 3 ^ 40 * 6902545 * 2
def baseEnd_6902545 : Nat := 131271234232918573875677

theorem tailTrace_6902545 : CollatzResearch.WordTrace tailWord_6902545 prefixEnd_6902545 131271234232918573875677 := by
  unfold tailWord_6902545
  simp only [CollatzResearch.WordTrace]
  refine ⟨251756498778265800677205089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167837665852177200451470059 251756498778265800677205089)
  ·
    refine ⟨188817374083699350507903817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251756498778265800677205089 188817374083699350507903817)
    ·
      refine ⟨141613030562774512880927863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188817374083699350507903817 141613030562774512880927863)
      ·
        refine ⟨212419545844161769321391795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141613030562774512880927863 212419545844161769321391795)
        ·
          refine ⟨318629318766242653982087693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212419545844161769321391795 318629318766242653982087693)
          ·
            refine ⟨119485994537340995243282885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318629318766242653982087693 119485994537340995243282885)
            ·
              refine ⟨22403623975751436608115541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119485994537340995243282885 22403623975751436608115541)
              ·
                refine ⟨131271234232918573875677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22403623975751436608115541 131271234232918573875677)
                ·
                  rfl

theorem cell23_6902545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 9].length) (baseStart_6902545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902545 prefixEnd_6902545 := by exact prefixLift 6902545
  have htrace : WordTrace (prefixWord ++ tailWord_6902545) baseStart_6902545 baseEnd_6902545 := by
    simpa [prefixWord, tailWord_6902545, baseEnd_6902545] using wordTrace_append hprefix tailTrace_6902545
  have hstable : (prefixWord ++ tailWord_6902545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902545).length < 2 ^ (prefixWord ++ tailWord_6902545).sum := by decide
  have hdescent : baseEnd_6902545 < baseStart_6902545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902556 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6902556 : Nat := 118140960795 + 6902556 * 2 ^ 59
def prefixEnd_6902556 : Nat := 4983230072969 + 3 ^ 40 * 6902556 * 2
def baseEnd_6902556 : Nat := 3544328972576000951605729

theorem tailTrace_6902556 : CollatzResearch.WordTrace tailWord_6902556 prefixEnd_6902556 3544328972576000951605729 := by
  unfold tailWord_6902556
  simp only [CollatzResearch.WordTrace]
  refine ⟨125878449990612974777927761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167837933320817299703903681 125878449990612974777927761)
  ·
    refine ⟨94408837492959731083445821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125878449990612974777927761 94408837492959731083445821)
    ·
      refine ⟨35403314059859899156292183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94408837492959731083445821 35403314059859899156292183)
      ·
        refine ⟨53104971089789848734438275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35403314059859899156292183 53104971089789848734438275)
        ·
          refine ⟨79657456634684773101657413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53104971089789848734438275 79657456634684773101657413)
          ·
            refine ⟨14935773119003394956560765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79657456634684773101657413 14935773119003394956560765)
            ·
              refine ⟨5600914919626273108710287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14935773119003394956560765 5600914919626273108710287)
              ·
                refine ⟨8401372379439409663065431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5600914919626273108710287 8401372379439409663065431)
                ·
                  refine ⟨12602058569159114494598147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401372379439409663065431 12602058569159114494598147)
                  ·
                    refine ⟨18903087853738671741897221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12602058569159114494598147 18903087853738671741897221)
                    ·
                      refine ⟨3544328972576000951605729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18903087853738671741897221 3544328972576000951605729)
                      ·
                        rfl

theorem cell23_6902556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6902556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902556 prefixEnd_6902556 := by exact prefixLift 6902556
  have htrace : WordTrace (prefixWord ++ tailWord_6902556) baseStart_6902556 baseEnd_6902556 := by
    simpa [prefixWord, tailWord_6902556, baseEnd_6902556] using wordTrace_append hprefix tailTrace_6902556
  have hstable : (prefixWord ++ tailWord_6902556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902556).length < 2 ^ (prefixWord ++ tailWord_6902556).sum := by decide
  have hdescent : baseEnd_6902556 < baseStart_6902556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902559 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_6902559 : Nat := 118140960795 + 6902559 * 2 ^ 59
def prefixEnd_6902559 : Nat := 4983230072969 + 3 ^ 40 * 6902559 * 2
def baseEnd_6902559 : Nat := 3544330513017964439868215

theorem tailTrace_6902559 : CollatzResearch.WordTrace tailWord_6902559 prefixEnd_6902559 3544330513017964439868215 := by
  unfold tailWord_6902559
  simp only [CollatzResearch.WordTrace]
  refine ⟨251757009400215081068214731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167838006266810054045476487 251757009400215081068214731)
  ·
    refine ⟨377635514100322621602322097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251757009400215081068214731 377635514100322621602322097)
    ·
      refine ⟨283226635575241966201741573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377635514100322621602322097 283226635575241966201741573)
      ·
        refine ⟨53104994170357868662826545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283226635575241966201741573 53104994170357868662826545)
        ·
          refine ⟨39828745627768401497119909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53104994170357868662826545 39828745627768401497119909)
          ·
            refine ⟨7467889805206575280709983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39828745627768401497119909 7467889805206575280709983)
            ·
              refine ⟨11201834707809862921064975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467889805206575280709983 11201834707809862921064975)
              ·
                refine ⟨16802752061714794381597463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11201834707809862921064975 16802752061714794381597463)
                ·
                  refine ⟨25204128092572191572396195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16802752061714794381597463 25204128092572191572396195)
                  ·
                    refine ⟨37806192138858287358594293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25204128092572191572396195 37806192138858287358594293)
                    ·
                      refine ⟨3544330513017964439868215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37806192138858287358594293 3544330513017964439868215)
                      ·
                        rfl

theorem cell23_6902559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_6902559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902559 prefixEnd_6902559 := by exact prefixLift 6902559
  have htrace : WordTrace (prefixWord ++ tailWord_6902559) baseStart_6902559 baseEnd_6902559 := by
    simpa [prefixWord, tailWord_6902559, baseEnd_6902559] using wordTrace_append hprefix tailTrace_6902559
  have hstable : (prefixWord ++ tailWord_6902559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902559).length < 2 ^ (prefixWord ++ tailWord_6902559).sum := by decide
  have hdescent : baseEnd_6902559 < baseStart_6902559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902572 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_6902572 : Nat := 118140960795 + 6902572 * 2 ^ 59
def prefixEnd_6902572 : Nat := 4983230072969 + 3 ^ 40 * 6902572 * 2
def baseEnd_6902572 : Nat := 3544337188266472889005655

theorem tailTrace_6902572 : CollatzResearch.WordTrace tailWord_6902572 prefixEnd_6902572 3544337188266472889005655 := by
  unfold tailWord_6902572
  simp only [CollatzResearch.WordTrace]
  refine ⟨125878741774583992144218985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167838322366111989525625313 125878741774583992144218985)
  ·
    refine ⟨94409056330937994108164239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125878741774583992144218985 94409056330937994108164239)
    ·
      refine ⟨141613584496406991162246359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94409056330937994108164239 141613584496406991162246359)
      ·
        refine ⟨212420376744610486743369539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141613584496406991162246359 212420376744610486743369539)
        ·
          refine ⟨318630565116915730115054309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212420376744610486743369539 318630565116915730115054309)
          ·
            refine ⟨59743230959421699396572683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318630565116915730115054309 59743230959421699396572683)
            ·
              refine ⟨89614846439132549094859025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59743230959421699396572683 89614846439132549094859025)
              ·
                refine ⟨67211134829349411821144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89614846439132549094859025 67211134829349411821144269)
                ·
                  refine ⟨25204175561006029432929101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67211134829349411821144269 25204175561006029432929101)
                  ·
                    refine ⟨9451565835377261037348413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25204175561006029432929101 9451565835377261037348413)
                    ·
                      refine ⟨3544337188266472889005655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9451565835377261037348413 3544337188266472889005655)
                      ·
                        rfl

theorem cell23_6902572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_6902572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902572 prefixEnd_6902572 := by exact prefixLift 6902572
  have htrace : WordTrace (prefixWord ++ tailWord_6902572) baseStart_6902572 baseEnd_6902572 := by
    simpa [prefixWord, tailWord_6902572, baseEnd_6902572] using wordTrace_append hprefix tailTrace_6902572
  have hstable : (prefixWord ++ tailWord_6902572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902572).length < 2 ^ (prefixWord ++ tailWord_6902572).sum := by decide
  have hdescent : baseEnd_6902572 < baseStart_6902572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902629 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_6902629 : Nat := 118140960795 + 6902629 * 2 ^ 59
def prefixEnd_6902629 : Nat := 4983230072969 + 3 ^ 40 * 6902629 * 2
def baseEnd_6902629 : Nat := 3544366456663779165992893

theorem tailTrace_6902629 : CollatzResearch.WordTrace tailWord_6902629 prefixEnd_6902629 3544366456663779165992893 := by
  unfold tailWord_6902629
  simp only [CollatzResearch.WordTrace]
  refine ⟨251759562509961483023262941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167839708339974322015508627 251759562509961483023262941)
  ·
    refine ⟨94409835941235556133723603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251759562509961483023262941 94409835941235556133723603)
    ·
      refine ⟨141614753911853334200585405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94409835941235556133723603 141614753911853334200585405)
      ·
        refine ⟨53105532716945000325219527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141614753911853334200585405 53105532716945000325219527)
        ·
          refine ⟨79658299075417500487829291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53105532716945000325219527 79658299075417500487829291)
          ·
            refine ⟨119487448613126250731743937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79658299075417500487829291 119487448613126250731743937)
            ·
              refine ⟨89615586459844688048807953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119487448613126250731743937 89615586459844688048807953)
              ·
                refine ⟨67211689844883516036605965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89615586459844688048807953 67211689844883516036605965)
                ·
                  refine ⟨25204383691831318513727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67211689844883516036605965 25204383691831318513727237)
                  ·
                    refine ⟨4725821942218372221323857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25204383691831318513727237 4725821942218372221323857)
                    ·
                      refine ⟨3544366456663779165992893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725821942218372221323857 3544366456663779165992893)
                      ·
                        rfl

theorem cell23_6902629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_6902629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902629 prefixEnd_6902629 := by exact prefixLift 6902629
  have htrace : WordTrace (prefixWord ++ tailWord_6902629) baseStart_6902629 baseEnd_6902629 := by
    simpa [prefixWord, tailWord_6902629, baseEnd_6902629] using wordTrace_append hprefix tailTrace_6902629
  have hstable : (prefixWord ++ tailWord_6902629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902629).length < 2 ^ (prefixWord ++ tailWord_6902629).sum := by decide
  have hdescent : baseEnd_6902629 < baseStart_6902629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902719 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 6, 2]
def baseStart_6902719 : Nat := 118140960795 + 6902719 * 2 ^ 59
def prefixEnd_6902719 : Nat := 4983230072969 + 3 ^ 40 * 6902719 * 2
def baseEnd_6902719 : Nat := 3544412669922683813867479

theorem tailTrace_6902719 : CollatzResearch.WordTrace tailWord_6902719 prefixEnd_6902719 3544412669922683813867479 := by
  unfold tailWord_6902719
  simp only [CollatzResearch.WordTrace]
  refine ⟨251762845079635428394039211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167841896719756952262692807 251762845079635428394039211)
  ·
    refine ⟨377644267619453142591058817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251762845079635428394039211 377644267619453142591058817)
    ·
      refine ⟨283233200714589856943294113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377644267619453142591058817 283233200714589856943294113)
      ·
        refine ⟨212424900535942392707470585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283233200714589856943294113 212424900535942392707470585)
        ·
          refine ⟨159318675401956794530602939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212424900535942392707470585 159318675401956794530602939)
          ·
            refine ⟨238978013102935191795904409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159318675401956794530602939 238978013102935191795904409)
            ·
              refine ⟨179233509827201393846928307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238978013102935191795904409 179233509827201393846928307)
              ·
                refine ⟨268850264740802090770392461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179233509827201393846928307 268850264740802090770392461)
                ·
                  refine ⟨100818849277800784038897173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268850264740802090770392461 100818849277800784038897173)
                  ·
                    refine ⟨4725883559896911751823305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100818849277800784038897173 4725883559896911751823305)
                    ·
                      refine ⟨3544412669922683813867479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4725883559896911751823305 3544412669922683813867479)
                      ·
                        rfl

theorem cell23_6902719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_6902719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902719 prefixEnd_6902719 := by exact prefixLift 6902719
  have htrace : WordTrace (prefixWord ++ tailWord_6902719) baseStart_6902719 baseEnd_6902719 := by
    simpa [prefixWord, tailWord_6902719, baseEnd_6902719] using wordTrace_append hprefix tailTrace_6902719
  have hstable : (prefixWord ++ tailWord_6902719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902719).length < 2 ^ (prefixWord ++ tailWord_6902719).sum := by decide
  have hdescent : baseEnd_6902719 < baseStart_6902719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902770 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6902770 : Nat := 118140960795 + 6902770 * 2 ^ 59
def prefixEnd_6902770 : Nat := 4983230072969 + 3 ^ 40 * 6902770 * 2
def baseEnd_6902770 : Nat := 3544438857436063114329745

theorem tailTrace_6902770 : CollatzResearch.WordTrace tailWord_6902770 prefixEnd_6902770 3544438857436063114329745 := by
  unfold tailWord_6902770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62941176300612666026036441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167843136801633776069430509 62941176300612666026036441)
  ·
    refine ⟨47205882225459499519527331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62941176300612666026036441 47205882225459499519527331)
    ·
      refine ⟨70808823338189249279290997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47205882225459499519527331 70808823338189249279290997)
      ·
        refine ⟨6638327187955242119933531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70808823338189249279290997 6638327187955242119933531)
        ·
          refine ⟨9957490781932863179900297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638327187955242119933531 9957490781932863179900297)
          ·
            refine ⟨7468118086449647384925223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957490781932863179900297 7468118086449647384925223)
            ·
              refine ⟨11202177129674471077387835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468118086449647384925223 11202177129674471077387835)
              ·
                refine ⟨16803265694511706616081753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202177129674471077387835 16803265694511706616081753)
                ·
                  refine ⟨12602449270883779962061315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16803265694511706616081753 12602449270883779962061315)
                  ·
                    refine ⟨18903673906325669943091973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12602449270883779962061315 18903673906325669943091973)
                    ·
                      refine ⟨3544438857436063114329745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18903673906325669943091973 3544438857436063114329745)
                      ·
                        rfl

theorem cell23_6902770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6902770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902770 prefixEnd_6902770 := by exact prefixLift 6902770
  have htrace : WordTrace (prefixWord ++ tailWord_6902770) baseStart_6902770 baseEnd_6902770 := by
    simpa [prefixWord, tailWord_6902770, baseEnd_6902770] using wordTrace_append hprefix tailTrace_6902770
  have hstable : (prefixWord ++ tailWord_6902770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902770).length < 2 ^ (prefixWord ++ tailWord_6902770).sum := by decide
  have hdescent : baseEnd_6902770 < baseStart_6902770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902809 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6902809 : Nat := 118140960795 + 6902809 * 2 ^ 59
def prefixEnd_6902809 : Nat := 4983230072969 + 3 ^ 40 * 6902809 * 2
def baseEnd_6902809 : Nat := 3544458883181588461742065

theorem tailTrace_6902809 : CollatzResearch.WordTrace tailWord_6902809 prefixEnd_6902809 3544458883181588461742065 := by
  unfold tailWord_6902809
  simp only [CollatzResearch.WordTrace]
  refine ⟨251766127649309373764815481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167844085099539582509876987 251766127649309373764815481)
  ·
    refine ⟨188824595736982030323611611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251766127649309373764815481 188824595736982030323611611)
    ·
      refine ⟨283236893605473045485417417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188824595736982030323611611 283236893605473045485417417)
      ·
        refine ⟨212427670204104784114063063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283236893605473045485417417 212427670204104784114063063)
        ·
          refine ⟨318641505306157176171094595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212427670204104784114063063 318641505306157176171094595)
          ·
            refine ⟨477962257959235764256641893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318641505306157176171094595 477962257959235764256641893)
            ·
              refine ⟨89617923367356705798120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477962257959235764256641893 89617923367356705798120355)
              ·
                refine ⟨134426885051035058697180533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89617923367356705798120355 134426885051035058697180533)
                ·
                  refine ⟨12602520473534536752860675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134426885051035058697180533 12602520473534536752860675)
                  ·
                    refine ⟨18903780710301805129291013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12602520473534536752860675 18903780710301805129291013)
                    ·
                      refine ⟨3544458883181588461742065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18903780710301805129291013 3544458883181588461742065)
                      ·
                        rfl

theorem cell23_6902809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6902809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902809 prefixEnd_6902809 := by exact prefixLift 6902809
  have htrace : WordTrace (prefixWord ++ tailWord_6902809) baseStart_6902809 baseEnd_6902809 := by
    simpa [prefixWord, tailWord_6902809, baseEnd_6902809] using wordTrace_append hprefix tailTrace_6902809
  have hstable : (prefixWord ++ tailWord_6902809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902809).length < 2 ^ (prefixWord ++ tailWord_6902809).sum := by decide
  have hdescent : baseEnd_6902809 < baseStart_6902809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902823 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6902823 : Nat := 118140960795 + 6902823 * 2 ^ 59
def prefixEnd_6902823 : Nat := 4983230072969 + 3 ^ 40 * 6902823 * 2
def baseEnd_6902823 : Nat := 1181488690636917135655667

theorem tailTrace_6902823 : CollatzResearch.WordTrace tailWord_6902823 prefixEnd_6902823 1181488690636917135655667 := by
  unfold tailWord_6902823
  simp only [CollatzResearch.WordTrace]
  refine ⟨251766638271258654155825123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167844425514172436103883415 251766638271258654155825123)
  ·
    refine ⟨377649957406887981233737685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251766638271258654155825123 377649957406887981233737685)
    ·
      refine ⟨8851170876723937060165727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 377649957406887981233737685 8851170876723937060165727)
      ·
        refine ⟨13276756315085905590248591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851170876723937060165727 13276756315085905590248591)
        ·
          refine ⟨19915134472628858385372887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276756315085905590248591 19915134472628858385372887)
          ·
            refine ⟨29872701708943287578059331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19915134472628858385372887 29872701708943287578059331)
            ·
              refine ⟨44809052563414931367088997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29872701708943287578059331 44809052563414931367088997)
              ·
                refine ⟨8401697355640299631329187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44809052563414931367088997 8401697355640299631329187)
                ·
                  refine ⟨12602546033460449446993781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401697355640299631329187 12602546033460449446993781)
                  ·
                    refine ⟨1181488690636917135655667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12602546033460449446993781 1181488690636917135655667)
                    ·
                      rfl

theorem cell23_6902823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6902823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902823 prefixEnd_6902823 := by exact prefixLift 6902823
  have htrace : WordTrace (prefixWord ++ tailWord_6902823) baseStart_6902823 baseEnd_6902823 := by
    simpa [prefixWord, tailWord_6902823, baseEnd_6902823] using wordTrace_append hprefix tailTrace_6902823
  have hstable : (prefixWord ++ tailWord_6902823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902823).length < 2 ^ (prefixWord ++ tailWord_6902823).sum := by decide
  have hdescent : baseEnd_6902823 < baseStart_6902823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902839 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_6902839 : Nat := 118140960795 + 6902839 * 2 ^ 59
def prefixEnd_6902839 : Nat := 4983230072969 + 3 ^ 40 * 6902839 * 2
def baseEnd_6902839 : Nat := 3544474287601223344366927

theorem tailTrace_6902839 : CollatzResearch.WordTrace tailWord_6902839 prefixEnd_6902839 3544474287601223344366927 := by
  unfold tailWord_6902839
  simp only [CollatzResearch.WordTrace]
  refine ⟨251767221839200688888407571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167844814559467125925605047 251767221839200688888407571)
  ·
    refine ⟨377650832758801033332611357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251767221839200688888407571 377650832758801033332611357)
    ·
      refine ⟨141619062284550387499729259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377650832758801033332611357 141619062284550387499729259)
      ·
        refine ⟨212428593426825581249593889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141619062284550387499729259 212428593426825581249593889)
        ·
          refine ⟨159321445070119185937195417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212428593426825581249593889 159321445070119185937195417)
          ·
            refine ⟨119491083802589389452896563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159321445070119185937195417 119491083802589389452896563)
            ·
              refine ⟨179236625703884084179344845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119491083802589389452896563 179236625703884084179344845)
              ·
                refine ⟨67213734638956531567254317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179236625703884084179344845 67213734638956531567254317)
                ·
                  refine ⟨25205150489608699337720369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67213734638956531567254317 25205150489608699337720369)
                  ·
                    refine ⟨18903862867206524503290277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25205150489608699337720369 18903862867206524503290277)
                    ·
                      refine ⟨3544474287601223344366927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18903862867206524503290277 3544474287601223344366927)
                      ·
                        rfl

theorem cell23_6902839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_6902839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902839 prefixEnd_6902839 := by exact prefixLift 6902839
  have htrace : WordTrace (prefixWord ++ tailWord_6902839) baseStart_6902839 baseEnd_6902839 := by
    simpa [prefixWord, tailWord_6902839, baseEnd_6902839] using wordTrace_append hprefix tailTrace_6902839
  have hstable : (prefixWord ++ tailWord_6902839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902839).length < 2 ^ (prefixWord ++ tailWord_6902839).sum := by decide
  have hdescent : baseEnd_6902839 < baseStart_6902839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902859 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3]
def baseStart_6902859 : Nat := 118140960795 + 6902859 * 2 ^ 59
def prefixEnd_6902859 : Nat := 4983230072969 + 3 ^ 40 * 6902859 * 2
def baseEnd_6902859 : Nat := 3544484557214313266116835

theorem tailTrace_6902859 : CollatzResearch.WordTrace tailWord_6902859 prefixEnd_6902859 3544484557214313266116835 := by
  unfold tailWord_6902859
  simp only [CollatzResearch.WordTrace]
  refine ⟨251767951299128232304135631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167845300866085488202757087 251767951299128232304135631)
  ·
    refine ⟨377651926948692348456203447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251767951299128232304135631 377651926948692348456203447)
    ·
      refine ⟨566477890423038522684305171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377651926948692348456203447 566477890423038522684305171)
      ·
        refine ⟨849716835634557784026457757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566477890423038522684305171 849716835634557784026457757)
        ·
          refine ⟨318643813362959169009921659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849716835634557784026457757 318643813362959169009921659)
          ·
            refine ⟨477965720044438753514882489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318643813362959169009921659 477965720044438753514882489)
            ·
              refine ⟨358474290033329065136161867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477965720044438753514882489 358474290033329065136161867)
              ·
                refine ⟨537711435049993597704242801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358474290033329065136161867 537711435049993597704242801)
                ·
                  refine ⟨403283576287495198278182101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537711435049993597704242801 403283576287495198278182101)
                  ·
                    refine ⟨9451958819238168709644893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 403283576287495198278182101 9451958819238168709644893)
                    ·
                      refine ⟨3544484557214313266116835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9451958819238168709644893 3544484557214313266116835)
                      ·
                        rfl

theorem cell23_6902859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 3].length) (baseStart_6902859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902859 prefixEnd_6902859 := by exact prefixLift 6902859
  have htrace : WordTrace (prefixWord ++ tailWord_6902859) baseStart_6902859 baseEnd_6902859 := by
    simpa [prefixWord, tailWord_6902859, baseEnd_6902859] using wordTrace_append hprefix tailTrace_6902859
  have hstable : (prefixWord ++ tailWord_6902859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902859).length < 2 ^ (prefixWord ++ tailWord_6902859).sum := by decide
  have hdescent : baseEnd_6902859 < baseStart_6902859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902866 : List Nat := [3, 2, 2, 1, 3, 2, 2, 8]
def baseStart_6902866 : Nat := 118140960795 + 6902866 * 2 ^ 59
def prefixEnd_6902866 : Nat := 4983230072969 + 3 ^ 40 * 6902866 * 2
def baseEnd_6902866 : Nat := 131277338947366471804789

theorem tailTrace_6902866 : CollatzResearch.WordTrace tailWord_6902866 prefixEnd_6902866 131277338947366471804789 := by
  unfold tailWord_6902866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62942051652525718124910113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167845471073401914999760301 62942051652525718124910113)
  ·
    refine ⟨47206538739394288593682585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62942051652525718124910113 47206538739394288593682585)
    ·
      refine ⟨35404904054545716445261939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47206538739394288593682585 35404904054545716445261939)
      ·
        refine ⟨53107356081818574667892909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35404904054545716445261939 53107356081818574667892909)
        ·
          refine ⟨19915258530681965500459841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53107356081818574667892909 19915258530681965500459841)
          ·
            refine ⟨14936443898011474125344881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19915258530681965500459841 14936443898011474125344881)
            ·
              refine ⟨11202332923508605594008661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14936443898011474125344881 11202332923508605594008661)
              ·
                refine ⟨131277338947366471804789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11202332923508605594008661 131277338947366471804789)
                ·
                  rfl

theorem cell23_6902866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 8].length) (baseStart_6902866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902866 prefixEnd_6902866 := by exact prefixLift 6902866
  have htrace : WordTrace (prefixWord ++ tailWord_6902866) baseStart_6902866 baseEnd_6902866 := by
    simpa [prefixWord, tailWord_6902866, baseEnd_6902866] using wordTrace_append hprefix tailTrace_6902866
  have hstable : (prefixWord ++ tailWord_6902866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902866).length < 2 ^ (prefixWord ++ tailWord_6902866).sum := by decide
  have hdescent : baseEnd_6902866 < baseStart_6902866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902869 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6902869 : Nat := 118140960795 + 6902869 * 2 ^ 59
def prefixEnd_6902869 : Nat := 4983230072969 + 3 ^ 40 * 6902869 * 2
def baseEnd_6902869 : Nat := 3544489692020858226991789

theorem tailTrace_6902869 : CollatzResearch.WordTrace tailWord_6902869 prefixEnd_6902869 3544489692020858226991789 := by
  unfold tailWord_6902869
  simp only [CollatzResearch.WordTrace]
  refine ⟨251768316029092004011999661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167845544019394669341333107 251768316029092004011999661)
  ·
    refine ⟨94413118510909501504499873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251768316029092004011999661 94413118510909501504499873)
    ·
      refine ⟨70809838883182126128374905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94413118510909501504499873 70809838883182126128374905)
      ·
        refine ⟨53107379162386594596281179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70809838883182126128374905 53107379162386594596281179)
        ·
          refine ⟨79661068743579891894421769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53107379162386594596281179 79661068743579891894421769)
          ·
            refine ⟨59745801557684918920816327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79661068743579891894421769 59745801557684918920816327)
            ·
              refine ⟨89618702336527378381224491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59745801557684918920816327 89618702336527378381224491)
              ·
                refine ⟨134428053504791067571836737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89618702336527378381224491 134428053504791067571836737)
                ·
                  refine ⟨100821040128593300678877553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134428053504791067571836737 100821040128593300678877553)
                  ·
                    refine ⟨75615780096444975509158165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100821040128593300678877553 75615780096444975509158165)
                    ·
                      refine ⟨3544489692020858226991789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75615780096444975509158165 3544489692020858226991789)
                      ·
                        rfl

theorem cell23_6902869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6902869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902869 prefixEnd_6902869 := by exact prefixLift 6902869
  have htrace : WordTrace (prefixWord ++ tailWord_6902869) baseStart_6902869 baseEnd_6902869 := by
    simpa [prefixWord, tailWord_6902869, baseEnd_6902869] using wordTrace_append hprefix tailTrace_6902869
  have hstable : (prefixWord ++ tailWord_6902869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902869).length < 2 ^ (prefixWord ++ tailWord_6902869).sum := by decide
  have hdescent : baseEnd_6902869 < baseStart_6902869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902877 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6902877 : Nat := 118140960795 + 6902877 * 2 ^ 59
def prefixEnd_6902877 : Nat := 4983230072969 + 3 ^ 40 * 6902877 * 2
def baseEnd_6902877 : Nat := 3544493799866094195691753

theorem tailTrace_6902877 : CollatzResearch.WordTrace tailWord_6902877 prefixEnd_6902877 3544493799866094195691753 := by
  unfold tailWord_6902877
  simp only [CollatzResearch.WordTrace]
  refine ⟨251768607813063021378290885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167845738542042014252193923 251768607813063021378290885)
  ·
    refine ⟨47206613964949316508429541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251768607813063021378290885 47206613964949316508429541)
    ·
      refine ⟨8851240118427996845330539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47206613964949316508429541 8851240118427996845330539)
      ·
        refine ⟨13276860177641995267995809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851240118427996845330539 13276860177641995267995809)
        ·
          refine ⟨9957645133231496450996857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13276860177641995267995809 9957645133231496450996857)
          ·
            refine ⟨7468233849923622338247643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9957645133231496450996857 7468233849923622338247643)
            ·
              refine ⟨11202350774885433507371465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468233849923622338247643 11202350774885433507371465)
              ·
                refine ⟨8401763081164075130528599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11202350774885433507371465 8401763081164075130528599)
                ·
                  refine ⟨12602644621746112695792899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401763081164075130528599 12602644621746112695792899)
                  ·
                    refine ⟨18903966932619169043689349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12602644621746112695792899 18903966932619169043689349)
                    ·
                      refine ⟨3544493799866094195691753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18903966932619169043689349 3544493799866094195691753)
                      ·
                        rfl

theorem cell23_6902877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6902877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902877 prefixEnd_6902877 := by exact prefixLift 6902877
  have htrace : WordTrace (prefixWord ++ tailWord_6902877) baseStart_6902877 baseEnd_6902877 := by
    simpa [prefixWord, tailWord_6902877, baseEnd_6902877] using wordTrace_append hprefix tailTrace_6902877
  have hstable : (prefixWord ++ tailWord_6902877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902877).length < 2 ^ (prefixWord ++ tailWord_6902877).sum := by decide
  have hdescent : baseEnd_6902877 < baseStart_6902877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902893 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6902893 : Nat := 118140960795 + 6902893 * 2 ^ 59
def prefixEnd_6902893 : Nat := 4983230072969 + 3 ^ 40 * 6902893 * 2
def baseEnd_6902893 : Nat := 3544502015556566133091679

theorem tailTrace_6902893 : CollatzResearch.WordTrace tailWord_6902893 prefixEnd_6902893 3544502015556566133091679 := by
  unfold tailWord_6902893
  simp only [CollatzResearch.WordTrace]
  refine ⟨251769191381005056110873333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167846127587336704073915555 251769191381005056110873333)
  ·
    refine ⟨23603361691969224010394375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251769191381005056110873333 23603361691969224010394375)
    ·
      refine ⟨35405042537953836015591563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603361691969224010394375 35405042537953836015591563)
      ·
        refine ⟨53107563806930754023387345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405042537953836015591563 53107563806930754023387345)
        ·
          refine ⟨39830672855198065517540509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53107563806930754023387345 39830672855198065517540509)
          ·
            refine ⟨14936502320699274569077691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39830672855198065517540509 14936502320699274569077691)
            ·
              refine ⟨22404753481048911853616537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14936502320699274569077691 22404753481048911853616537)
              ·
                refine ⟨16803565110786683890212403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22404753481048911853616537 16803565110786683890212403)
                ·
                  refine ⟨25205347666180025835318605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16803565110786683890212403 25205347666180025835318605)
                  ·
                    refine ⟨9452005374817509688244477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25205347666180025835318605 9452005374817509688244477)
                    ·
                      refine ⟨3544502015556566133091679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9452005374817509688244477 3544502015556566133091679)
                      ·
                        rfl

theorem cell23_6902893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6902893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902893 prefixEnd_6902893 := by exact prefixLift 6902893
  have htrace : WordTrace (prefixWord ++ tailWord_6902893) baseStart_6902893 baseEnd_6902893 := by
    simpa [prefixWord, tailWord_6902893, baseEnd_6902893] using wordTrace_append hprefix tailTrace_6902893
  have hstable : (prefixWord ++ tailWord_6902893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902893).length < 2 ^ (prefixWord ++ tailWord_6902893).sum := by decide
  have hdescent : baseEnd_6902893 < baseStart_6902893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902899 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_6902899 : Nat := 118140960795 + 6902899 * 2 ^ 59
def prefixEnd_6902899 : Nat := 4983230072969 + 3 ^ 40 * 6902899 * 2
def baseEnd_6902899 : Nat := 3544505096440493109616651

theorem tailTrace_6902899 : CollatzResearch.WordTrace tailWord_6902899 prefixEnd_6902899 3544505096440493109616651 := by
  unfold tailWord_6902899
  simp only [CollatzResearch.WordTrace]
  refine ⟨251769410218983319135591751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167846273479322212757061167 251769410218983319135591751)
  ·
    refine ⟨377654115328474978703387627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251769410218983319135591751 377654115328474978703387627)
    ·
      refine ⟨566481172992712468055081441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377654115328474978703387627 566481172992712468055081441)
      ·
        refine ⟨424860879744534351041311081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566481172992712468055081441 424860879744534351041311081)
        ·
          refine ⟨318645659808400763280983311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424860879744534351041311081 318645659808400763280983311)
          ·
            refine ⟨477968489712601144921474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318645659808400763280983311 477968489712601144921474967)
            ·
              refine ⟨716952734568901717382212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477968489712601144921474967 716952734568901717382212451)
              ·
                refine ⟨1075429101853352576073318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716952734568901717382212451 1075429101853352576073318677)
                ·
                  refine ⟨50410739149375902003436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1075429101853352576073318677 50410739149375902003436813)
                  ·
                    refine ⟨18904027181015963251288805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50410739149375902003436813 18904027181015963251288805)
                    ·
                      refine ⟨3544505096440493109616651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18904027181015963251288805 3544505096440493109616651)
                      ·
                        rfl

theorem cell23_6902899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_6902899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902899 prefixEnd_6902899 := by exact prefixLift 6902899
  have htrace : WordTrace (prefixWord ++ tailWord_6902899) baseStart_6902899 baseEnd_6902899 := by
    simpa [prefixWord, tailWord_6902899, baseEnd_6902899] using wordTrace_append hprefix tailTrace_6902899
  have hstable : (prefixWord ++ tailWord_6902899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902899).length < 2 ^ (prefixWord ++ tailWord_6902899).sum := by decide
  have hdescent : baseEnd_6902899 < baseStart_6902899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902916 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6902916 : Nat := 118140960795 + 6902916 * 2 ^ 59
def prefixEnd_6902916 : Nat := 4983230072969 + 3 ^ 40 * 6902916 * 2
def baseEnd_6902916 : Nat := 3544513825611619543104073

theorem tailTrace_6902916 : CollatzResearch.WordTrace tailWord_6902916 prefixEnd_6902916 3544513825611619543104073 := by
  unfold tailWord_6902916
  simp only [CollatzResearch.WordTrace]
  refine ⟨125885015129960865519480301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167846686839947820692640401 125885015129960865519480301)
  ·
    refine ⟨47206880673735324569805113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125885015129960865519480301 47206880673735324569805113)
    ·
      refine ⟨35405160505301493427353835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47206880673735324569805113 35405160505301493427353835)
      ·
        refine ⟨53107740757952240141030753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405160505301493427353835 53107740757952240141030753)
        ·
          refine ⟨39830805568464180105773065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53107740757952240141030753 39830805568464180105773065)
          ·
            refine ⟨29873104176348135079329799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39830805568464180105773065 29873104176348135079329799)
            ·
              refine ⟨44809656264522202618994699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29873104176348135079329799 44809656264522202618994699)
              ·
                refine ⟨67214484396783303928492049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44809656264522202618994699 67214484396783303928492049)
                ·
                  refine ⟨50410863297587477946369037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67214484396783303928492049 50410863297587477946369037)
                  ·
                    refine ⟨18904073736595304229888389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50410863297587477946369037 18904073736595304229888389)
                    ·
                      refine ⟨3544513825611619543104073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18904073736595304229888389 3544513825611619543104073)
                      ·
                        rfl

theorem cell23_6902916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6902916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902916 prefixEnd_6902916 := by exact prefixLift 6902916
  have htrace : WordTrace (prefixWord ++ tailWord_6902916) baseStart_6902916 baseEnd_6902916 := by
    simpa [prefixWord, tailWord_6902916, baseEnd_6902916] using wordTrace_append hprefix tailTrace_6902916
  have hstable : (prefixWord ++ tailWord_6902916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902916).length < 2 ^ (prefixWord ++ tailWord_6902916).sum := by decide
  have hdescent : baseEnd_6902916 < baseStart_6902916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902926 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_6902926 : Nat := 118140960795 + 6902926 * 2 ^ 59
def prefixEnd_6902926 : Nat := 4983230072969 + 3 ^ 40 * 6902926 * 2
def baseEnd_6902926 : Nat := 1181506320139388167993009

theorem tailTrace_6902926 : CollatzResearch.WordTrace tailWord_6902926 prefixEnd_6902926 1181506320139388167993009 := by
  unfold tailWord_6902926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31471299373735687843353079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167846929993257001831216421 31471299373735687843353079)
  ·
    refine ⟨47206949060603531765029619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31471299373735687843353079 47206949060603531765029619)
    ·
      refine ⟨70810423590905297647544429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47206949060603531765029619 70810423590905297647544429)
      ·
        refine ⟨26553908846589486617829161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70810423590905297647544429 26553908846589486617829161)
        ·
          refine ⟨19915431634942114963371871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26553908846589486617829161 19915431634942114963371871)
          ·
            refine ⟨29873147452413172445057807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19915431634942114963371871 29873147452413172445057807)
            ·
              refine ⟨44809721178619758667586711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29873147452413172445057807 44809721178619758667586711)
              ·
                refine ⟨67214581767929638001380067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44809721178619758667586711 67214581767929638001380067)
                ·
                  refine ⟨100821872651894457002070101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67214581767929638001380067 100821872651894457002070101)
                  ·
                    refine ⟨1181506320139388167993009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100821872651894457002070101 1181506320139388167993009)
                    ·
                      rfl

theorem cell23_6902926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_6902926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902926 prefixEnd_6902926 := by exact prefixLift 6902926
  have htrace : WordTrace (prefixWord ++ tailWord_6902926) baseStart_6902926 baseEnd_6902926 := by
    simpa [prefixWord, tailWord_6902926, baseEnd_6902926] using wordTrace_append hprefix tailTrace_6902926
  have hstable : (prefixWord ++ tailWord_6902926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902926).length < 2 ^ (prefixWord ++ tailWord_6902926).sum := by decide
  have hdescent : baseEnd_6902926 < baseStart_6902926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902954 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6902954 : Nat := 118140960795 + 6902954 * 2 ^ 59
def prefixEnd_6902954 : Nat := 4983230072969 + 3 ^ 40 * 6902954 * 2
def baseEnd_6902954 : Nat := 3544533337876490394428899

theorem tailTrace_6902954 : CollatzResearch.WordTrace tailWord_6902954 prefixEnd_6902954 3544533337876490394428899 := by
  unfold tailWord_6902954
  simp only [CollatzResearch.WordTrace]
  refine ⟨62942854058446015882210979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167847610822522709019229277 62942854058446015882210979)
  ·
    refine ⟨94414281087669023823316469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62942854058446015882210979 94414281087669023823316469)
    ·
      refine ⟨8851338851968970983435919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94414281087669023823316469 8851338851968970983435919)
      ·
        refine ⟨13277008277953456475153879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851338851968970983435919 13277008277953456475153879)
        ·
          refine ⟨19915512416930184712730819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13277008277953456475153879 19915512416930184712730819)
          ·
            refine ⟨29873268625395277069096229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19915512416930184712730819 29873268625395277069096229)
            ·
              refine ⟨5601237867261614450455543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29873268625395277069096229 5601237867261614450455543)
              ·
                refine ⟨8401856800892421675683315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601237867261614450455543 8401856800892421675683315)
                ·
                  refine ⟨12602785201338632513524973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401856800892421675683315 12602785201338632513524973)
                  ·
                    refine ⟨4726044450501987192571865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12602785201338632513524973 4726044450501987192571865)
                    ·
                      refine ⟨3544533337876490394428899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726044450501987192571865 3544533337876490394428899)
                      ·
                        rfl

theorem cell23_6902954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6902954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902954 prefixEnd_6902954 := by exact prefixLift 6902954
  have htrace : WordTrace (prefixWord ++ tailWord_6902954) baseStart_6902954 baseEnd_6902954 := by
    simpa [prefixWord, tailWord_6902954, baseEnd_6902954] using wordTrace_append hprefix tailTrace_6902954
  have hstable : (prefixWord ++ tailWord_6902954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902954).length < 2 ^ (prefixWord ++ tailWord_6902954).sum := by decide
  have hdescent : baseEnd_6902954 < baseStart_6902954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902973 : List Nat := [1, 4, 1, 2, 1, 1, 4, 4, 5]
def baseStart_6902973 : Nat := 118140960795 + 6902973 * 2 ^ 59
def prefixEnd_6902973 : Nat := 4983230072969 + 3 ^ 40 * 6902973 * 2
def baseEnd_6902973 : Nat := 393838121556547313343479

theorem tailTrace_6902973 : CollatzResearch.WordTrace tailWord_6902973 prefixEnd_6902973 393838121556547313343479 := by
  unfold tailWord_6902973
  simp only [CollatzResearch.WordTrace]
  refine ⟨251772109220715229773785573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167848072813810153182523715 251772109220715229773785573)
  ·
    refine ⟨47207270478884105582584795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251772109220715229773785573 47207270478884105582584795)
    ·
      refine ⟨70810905718326158373877193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47207270478884105582584795 70810905718326158373877193)
      ·
        refine ⟨53108179288744618780407895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70810905718326158373877193 53108179288744618780407895)
        ·
          refine ⟨79662268933116928170611843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53108179288744618780407895 79662268933116928170611843)
          ·
            refine ⟨119493403399675392255917765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79662268933116928170611843 119493403399675392255917765)
            ·
              refine ⟨22405013137439136047984581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119493403399675392255917765 22405013137439136047984581)
              ·
                refine ⟨4200939963269838008997109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22405013137439136047984581 4200939963269838008997109)
                ·
                  refine ⟨393838121556547313343479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4200939963269838008997109 393838121556547313343479)
                  ·
                    rfl

theorem cell23_6902973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_6902973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902973 prefixEnd_6902973 := by exact prefixLift 6902973
  have htrace : WordTrace (prefixWord ++ tailWord_6902973) baseStart_6902973 baseEnd_6902973 := by
    simpa [prefixWord, tailWord_6902973, baseEnd_6902973] using wordTrace_append hprefix tailTrace_6902973
  have hstable : (prefixWord ++ tailWord_6902973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902973).length < 2 ^ (prefixWord ++ tailWord_6902973).sum := by decide
  have hdescent : baseEnd_6902973 < baseStart_6902973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6902986 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_6902986 : Nat := 118140960795 + 6902986 * 2 ^ 59
def prefixEnd_6902986 : Nat := 4983230072969 + 3 ^ 40 * 6902986 * 2
def baseEnd_6902986 : Nat := 1181516589752478089742917

theorem tailTrace_6902986 : CollatzResearch.WordTrace tailWord_6902986 prefixEnd_6902986 1181516589752478089742917 := by
  unfold tailWord_6902986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62943145842417033248502203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167848388913112088662672541 62943145842417033248502203)
  ·
    refine ⟨94414718763625549872753305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62943145842417033248502203 94414718763625549872753305)
    ·
      refine ⟨70811039072719162404564979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94414718763625549872753305 70811039072719162404564979)
      ·
        refine ⟨106216558609078743606847469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70811039072719162404564979 106216558609078743606847469)
        ·
          refine ⟨39831209478404528852567801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106216558609078743606847469 39831209478404528852567801)
          ·
            refine ⟨29873407108803396639425851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39831209478404528852567801 29873407108803396639425851)
            ·
              refine ⟨44810110663205094959138777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29873407108803396639425851 44810110663205094959138777)
              ·
                refine ⟨33607582997403821219354083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44810110663205094959138777 33607582997403821219354083)
                ·
                  refine ⟨50411374496105731829031125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33607582997403821219354083 50411374496105731829031125)
                  ·
                    refine ⟨1181516589752478089742917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50411374496105731829031125 1181516589752478089742917)
                    ·
                      rfl

theorem cell23_6902986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_6902986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6902986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6902986 prefixEnd_6902986 := by exact prefixLift 6902986
  have htrace : WordTrace (prefixWord ++ tailWord_6902986) baseStart_6902986 baseEnd_6902986 := by
    simpa [prefixWord, tailWord_6902986, baseEnd_6902986] using wordTrace_append hprefix tailTrace_6902986
  have hstable : (prefixWord ++ tailWord_6902986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6902986).length < 2 ^ (prefixWord ++ tailWord_6902986).sum := by decide
  have hdescent : baseEnd_6902986 < baseStart_6902986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6902986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903080 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 6]
def baseStart_6903080 : Nat := 118140960795 + 6903080 * 2 ^ 59
def prefixEnd_6903080 : Nat := 4983230072969 + 3 ^ 40 * 6903080 * 2
def baseEnd_6903080 : Nat := 393844226270995211272591

theorem tailTrace_6903080 : CollatzResearch.WordTrace tailWord_6903080 prefixEnd_6903080 393844226270995211272591 := by
  unfold tailWord_6903080
  simp only [CollatzResearch.WordTrace]
  refine ⟨125888005915663793523965347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167850674554218391365287129 125888005915663793523965347)
  ·
    refine ⟨188832008873495690285948021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125888005915663793523965347 188832008873495690285948021)
    ·
      refine ⟨17703000831890220964307627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188832008873495690285948021 17703000831890220964307627)
      ·
        refine ⟨26554501247835331446461441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17703000831890220964307627 26554501247835331446461441)
        ·
          refine ⟨19915875935876498584846081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26554501247835331446461441 19915875935876498584846081)
          ·
            refine ⟨14936906951907373938634561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19915875935876498584846081 14936906951907373938634561)
            ·
              refine ⟨11202680213930530453975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14936906951907373938634561 11202680213930530453975921)
              ·
                refine ⟨8402010160447897840481941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11202680213930530453975921 8402010160447897840481941)
                ·
                  refine ⟨393844226270995211272591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8402010160447897840481941 393844226270995211272591)
                  ·
                    rfl

theorem cell23_6903080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_6903080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903080 prefixEnd_6903080 := by exact prefixLift 6903080
  have htrace : WordTrace (prefixWord ++ tailWord_6903080) baseStart_6903080 baseEnd_6903080 := by
    simpa [prefixWord, tailWord_6903080, baseEnd_6903080] using wordTrace_append hprefix tailTrace_6903080
  have hstable : (prefixWord ++ tailWord_6903080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903080).length < 2 ^ (prefixWord ++ tailWord_6903080).sum := by decide
  have hdescent : baseEnd_6903080 < baseStart_6903080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903093 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6903093 : Nat := 118140960795 + 6903093 * 2 ^ 59
def prefixEnd_6903093 : Nat := 4983230072969 + 3 ^ 40 * 6903093 * 2
def baseEnd_6903093 : Nat := 1181534903895821783530253

theorem tailTrace_6903093 : CollatzResearch.WordTrace tailWord_6903093 prefixEnd_6903093 1181534903895821783530253 := by
  unfold tailWord_6903093
  simp only [CollatzResearch.WordTrace]
  refine ⟨251776485980280490268153933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167850990653520326845435955 251776485980280490268153933)
  ·
    refine ⟨94416182242605183850557725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251776485980280490268153933 94416182242605183850557725)
    ·
      refine ⟨35406068340976943943959147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94416182242605183850557725 35406068340976943943959147)
      ·
        refine ⟨53109102511465415915938721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35406068340976943943959147 53109102511465415915938721)
        ·
          refine ⟨39831826883599061936954041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53109102511465415915938721 39831826883599061936954041)
          ·
            refine ⟨29873870162699296452715531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39831826883599061936954041 29873870162699296452715531)
            ·
              refine ⟨44810805244048944679073297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29873870162699296452715531 44810805244048944679073297)
              ·
                refine ⟨33608103933036708509304973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44810805244048944679073297 33608103933036708509304973)
                ·
                  refine ⟨12603038974888765690989365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33608103933036708509304973 12603038974888765690989365)
                  ·
                    refine ⟨1181534903895821783530253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12603038974888765690989365 1181534903895821783530253)
                    ·
                      rfl

theorem cell23_6903093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6903093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903093 prefixEnd_6903093 := by exact prefixLift 6903093
  have htrace : WordTrace (prefixWord ++ tailWord_6903093) baseStart_6903093 baseEnd_6903093 := by
    simpa [prefixWord, tailWord_6903093, baseEnd_6903093] using wordTrace_append hprefix tailTrace_6903093
  have hstable : (prefixWord ++ tailWord_6903093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903093).length < 2 ^ (prefixWord ++ tailWord_6903093).sum := by decide
  have hdescent : baseEnd_6903093 < baseStart_6903093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903113 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_6903113 : Nat := 118140960795 + 6903113 * 2 ^ 59
def prefixEnd_6903113 : Nat := 4983230072969 + 3 ^ 40 * 6903113 * 2
def baseEnd_6903113 : Nat := 3544614981300555272340667

theorem tailTrace_6903113 : CollatzResearch.WordTrace tailWord_6903113 prefixEnd_6903113 3544614981300555272340667 := by
  unfold tailWord_6903113
  simp only [CollatzResearch.WordTrace]
  refine ⟨251777215440208033683881993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167851476960138689122587995 251777215440208033683881993)
  ·
    refine ⟨188832911580156025262911495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251777215440208033683881993 188832911580156025262911495)
    ·
      refine ⟨283249367370234037894367243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188832911580156025262911495 283249367370234037894367243)
      ·
        refine ⟨424874051055351056841550865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283249367370234037894367243 424874051055351056841550865)
        ·
          refine ⟨318655538291513292631163149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424874051055351056841550865 318655538291513292631163149)
          ·
            refine ⟨119495826859317484736686181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318655538291513292631163149 119495826859317484736686181)
            ·
              refine ⟨22405467536122028388128659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119495826859317484736686181 22405467536122028388128659)
              ·
                refine ⟨33608201304183042582192989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22405467536122028388128659 33608201304183042582192989)
                ·
                  refine ⟨12603075489068640968322371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33608201304183042582192989 12603075489068640968322371)
                  ·
                    refine ⟨18904613233602961452483557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12603075489068640968322371 18904613233602961452483557)
                    ·
                      refine ⟨3544614981300555272340667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18904613233602961452483557 3544614981300555272340667)
                      ·
                        rfl

theorem cell23_6903113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_6903113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903113 prefixEnd_6903113 := by exact prefixLift 6903113
  have htrace : WordTrace (prefixWord ++ tailWord_6903113) baseStart_6903113 baseEnd_6903113 := by
    simpa [prefixWord, tailWord_6903113, baseEnd_6903113] using wordTrace_append hprefix tailTrace_6903113
  have hstable : (prefixWord ++ tailWord_6903113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903113).length < 2 ^ (prefixWord ++ tailWord_6903113).sum := by decide
  have hdescent : baseEnd_6903113 < baseStart_6903113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903123 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 4, 4]
def baseStart_6903123 : Nat := 118140960795 + 6903123 * 2 ^ 59
def prefixEnd_6903123 : Nat := 4983230072969 + 3 ^ 40 * 6903123 * 2
def baseEnd_6903123 : Nat := 1181540038702366744405207

theorem tailTrace_6903123 : CollatzResearch.WordTrace tailWord_6903123 prefixEnd_6903123 1181540038702366744405207 := by
  unfold tailWord_6903123
  simp only [CollatzResearch.WordTrace]
  refine ⟨251777580170171805391746023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167851720113447870261164015 251777580170171805391746023)
  ·
    refine ⟨377666370255257708087619035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251777580170171805391746023 377666370255257708087619035)
    ·
      refine ⟨566499555382886562131428553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377666370255257708087619035 566499555382886562131428553)
      ·
        refine ⟨424874666537164921598571415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566499555382886562131428553 424874666537164921598571415)
        ·
          refine ⟨637311999805747382397857123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424874666537164921598571415 637311999805747382397857123)
          ·
            refine ⟨955967999708621073596785685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637311999805747382397857123 955967999708621073596785685)
            ·
              refine ⟨44810999986341612824849329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 955967999708621073596785685 44810999986341612824849329)
              ·
                refine ⟨33608249989756209618636997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44810999986341612824849329 33608249989756209618636997)
                ·
                  refine ⟨6301546873079289303494437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33608249989756209618636997 6301546873079289303494437)
                  ·
                    refine ⟨1181540038702366744405207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301546873079289303494437 1181540038702366744405207)
                    ·
                      rfl

theorem cell23_6903123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 4].length) (baseStart_6903123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903123 prefixEnd_6903123 := by exact prefixLift 6903123
  have htrace : WordTrace (prefixWord ++ tailWord_6903123) baseStart_6903123 baseEnd_6903123 := by
    simpa [prefixWord, tailWord_6903123, baseEnd_6903123] using wordTrace_append hprefix tailTrace_6903123
  have hstable : (prefixWord ++ tailWord_6903123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903123).length < 2 ^ (prefixWord ++ tailWord_6903123).sum := by decide
  have hdescent : baseEnd_6903123 < baseStart_6903123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903124 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_6903124 : Nat := 118140960795 + 6903124 * 2 ^ 59
def prefixEnd_6903124 : Nat := 4983230072969 + 3 ^ 40 * 6903124 * 2
def baseEnd_6903124 : Nat := 3544620629587754729303117

theorem tailTrace_6903124 : CollatzResearch.WordTrace tailWord_6903124 prefixEnd_6903124 3544620629587754729303117 := by
  unfold tailWord_6903124
  simp only [CollatzResearch.WordTrace]
  refine ⟨125888808321584091281266213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167851744428778788375021617 125888808321584091281266213)
  ·
    refine ⟨23604151560297017115237415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125888808321584091281266213 23604151560297017115237415)
    ·
      refine ⟨35406227340445525672856123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23604151560297017115237415 35406227340445525672856123)
      ·
        refine ⟨53109341010668288509284185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35406227340445525672856123 53109341010668288509284185)
        ·
          refine ⟨39832005758001216381963139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53109341010668288509284185 39832005758001216381963139)
          ·
            refine ⟨59748008637001824572944709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39832005758001216381963139 59748008637001824572944709)
            ·
              refine ⟨11202751619437842107427133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59748008637001824572944709 11202751619437842107427133)
              ·
                refine ⟨4201031857289190790285175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11202751619437842107427133 4201031857289190790285175)
                ·
                  refine ⟨6301547785933786185427763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201031857289190790285175 6301547785933786185427763)
                  ·
                    refine ⟨9452321678900679278141645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6301547785933786185427763 9452321678900679278141645)
                    ·
                      refine ⟨3544620629587754729303117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9452321678900679278141645 3544620629587754729303117)
                      ·
                        rfl

theorem cell23_6903124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_6903124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903124 prefixEnd_6903124 := by exact prefixLift 6903124
  have htrace : WordTrace (prefixWord ++ tailWord_6903124) baseStart_6903124 baseEnd_6903124 := by
    simpa [prefixWord, tailWord_6903124, baseEnd_6903124] using wordTrace_append hprefix tailTrace_6903124
  have hstable : (prefixWord ++ tailWord_6903124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903124).length < 2 ^ (prefixWord ++ tailWord_6903124).sum := by decide
  have hdescent : baseEnd_6903124 < baseStart_6903124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903127 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 1, 5]
def baseStart_6903127 : Nat := 118140960795 + 6903127 * 2 ^ 59
def prefixEnd_6903127 : Nat := 4983230072969 + 3 ^ 40 * 6903127 * 2
def baseEnd_6903127 : Nat := 1181540723343239405855201

theorem tailTrace_6903127 : CollatzResearch.WordTrace tailWord_6903127 prefixEnd_6903127 1181540723343239405855201 := by
  unfold tailWord_6903127
  simp only [CollatzResearch.WordTrace]
  refine ⟨251777726062157314074891635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167851817374771542716594423 251777726062157314074891635)
  ·
    refine ⟨377666589093235971112337453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251777726062157314074891635 377666589093235971112337453)
    ·
      refine ⟨141624970909963489167126545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377666589093235971112337453 141624970909963489167126545)
      ·
        refine ⟨106218728182472616875344909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141624970909963489167126545 106218728182472616875344909)
        ·
          refine ⟨39832023068427231328254341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106218728182472616875344909 39832023068427231328254341)
          ·
            refine ⟨7468504325330105874047689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39832023068427231328254341 7468504325330105874047689)
            ·
              refine ⟨5601378243997579405535767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7468504325330105874047689 5601378243997579405535767)
              ·
                refine ⟨8402067365996369108303651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601378243997579405535767 8402067365996369108303651)
                ·
                  refine ⟨12603101048994553662455477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8402067365996369108303651 12603101048994553662455477)
                  ·
                    refine ⟨1181540723343239405855201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12603101048994553662455477 1181540723343239405855201)
                    ·
                      rfl

theorem cell23_6903127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_6903127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903127 prefixEnd_6903127 := by exact prefixLift 6903127
  have htrace : WordTrace (prefixWord ++ tailWord_6903127) baseStart_6903127 baseEnd_6903127 := by
    simpa [prefixWord, tailWord_6903127, baseEnd_6903127] using wordTrace_append hprefix tailTrace_6903127
  have hstable : (prefixWord ++ tailWord_6903127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903127).length < 2 ^ (prefixWord ++ tailWord_6903127).sum := by decide
  have hdescent : baseEnd_6903127 < baseStart_6903127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903140 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_6903140 : Nat := 118140960795 + 6903140 * 2 ^ 59
def prefixEnd_6903140 : Nat := 4983230072969 + 3 ^ 40 * 6903140 * 2
def baseEnd_6903140 : Nat := 1181542948426075555567681

theorem tailTrace_6903140 : CollatzResearch.WordTrace tailWord_6903140 prefixEnd_6903140 1181542948426075555567681 := by
  unfold tailWord_6903140
  simp only [CollatzResearch.WordTrace]
  refine ⟨125889100105555108647557437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167852133474073478196743249 125889100105555108647557437)
  ·
    refine ⟨47208412539583165742834039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125889100105555108647557437 47208412539583165742834039)
    ·
      refine ⟨70812618809374748614251059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47208412539583165742834039 70812618809374748614251059)
      ·
        refine ⟨106218928214062122921376589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70812618809374748614251059 106218928214062122921376589)
        ·
          refine ⟨39832098080273296095516221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106218928214062122921376589 39832098080273296095516221)
          ·
            refine ⟨14937036780102486035818583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39832098080273296095516221 14937036780102486035818583)
            ·
              refine ⟨22405555170153729053727875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14937036780102486035818583 22405555170153729053727875)
              ·
                refine ⟨33608332755230593580591813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22405555170153729053727875 33608332755230593580591813)
                ·
                  refine ⟨6301562391605736296360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33608332755230593580591813 6301562391605736296360965)
                  ·
                    refine ⟨1181542948426075555567681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301562391605736296360965 1181542948426075555567681)
                    ·
                      rfl

theorem cell23_6903140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_6903140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903140 prefixEnd_6903140 := by exact prefixLift 6903140
  have htrace : WordTrace (prefixWord ++ tailWord_6903140) baseStart_6903140 baseEnd_6903140 := by
    simpa [prefixWord, tailWord_6903140, baseEnd_6903140] using wordTrace_append hprefix tailTrace_6903140
  have hstable : (prefixWord ++ tailWord_6903140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903140).length < 2 ^ (prefixWord ++ tailWord_6903140).sum := by decide
  have hdescent : baseEnd_6903140 < baseStart_6903140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903157 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6903157 : Nat := 118140960795 + 6903157 * 2 ^ 59
def prefixEnd_6903157 : Nat := 4983230072969 + 3 ^ 40 * 6903157 * 2
def baseEnd_6903157 : Nat := 1181545858149784366730155

theorem tailTrace_6903157 : CollatzResearch.WordTrace tailWord_6903157 prefixEnd_6903157 1181545858149784366730155 := by
  unfold tailWord_6903157
  simp only [CollatzResearch.WordTrace]
  refine ⟨251778820252048629198483725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167852546834699086132322483 251778820252048629198483725)
  ·
    refine ⟨94417057594518235949431397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251778820252048629198483725 94417057594518235949431397)
    ·
      refine ⟨17703198298972169240518387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94417057594518235949431397 17703198298972169240518387)
      ·
        refine ⟨26554797448458253860777581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17703198298972169240518387 26554797448458253860777581)
        ·
          refine ⟨9958049043171845197791593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26554797448458253860777581 9958049043171845197791593)
          ·
            refine ⟨7468536782378883898343695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958049043171845197791593 7468536782378883898343695)
            ·
              refine ⟨11202805173568325847515543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468536782378883898343695 11202805173568325847515543)
              ·
                refine ⟨16804207760352488771273315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202805173568325847515543 16804207760352488771273315)
                ·
                  refine ⟨25206311640528733156909973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16804207760352488771273315 25206311640528733156909973)
                  ·
                    refine ⟨1181545858149784366730155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25206311640528733156909973 1181545858149784366730155)
                    ·
                      rfl

theorem cell23_6903157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6903157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903157 prefixEnd_6903157 := by exact prefixLift 6903157
  have htrace : WordTrace (prefixWord ++ tailWord_6903157) baseStart_6903157 baseEnd_6903157 := by
    simpa [prefixWord, tailWord_6903157, baseEnd_6903157] using wordTrace_append hprefix tailTrace_6903157
  have hstable : (prefixWord ++ tailWord_6903157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903157).length < 2 ^ (prefixWord ++ tailWord_6903157).sum := by decide
  have hdescent : baseEnd_6903157 < baseStart_6903157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903180 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_6903180 : Nat := 118140960795 + 6903180 * 2 ^ 59
def prefixEnd_6903180 : Nat := 4983230072969 + 3 ^ 40 * 6903180 * 2
def baseEnd_6903180 : Nat := 3544649384504406510202859

theorem tailTrace_6903180 : CollatzResearch.WordTrace tailWord_6903180 prefixEnd_6903180 3544649384504406510202859 := by
  unfold tailWord_6903180
  simp only [CollatzResearch.WordTrace]
  refine ⟨125889829565482652063285497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167853106087310202751047329 125889829565482652063285497)
  ·
    refine ⟨94417372174111989047464123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125889829565482652063285497 94417372174111989047464123)
    ·
      refine ⟨141626058261167983571196185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94417372174111989047464123 141626058261167983571196185)
      ·
        refine ⟨106219543695875987678397139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141626058261167983571196185 106219543695875987678397139)
        ·
          refine ⟨159329315543813981517595709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106219543695875987678397139 159329315543813981517595709)
          ·
            refine ⟨59748493328930243069098391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159329315543813981517595709 59748493328930243069098391)
            ·
              refine ⟨89622739993395364603647587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59748493328930243069098391 89622739993395364603647587)
              ·
                refine ⟨134434109990093046905471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89622739993395364603647587 134434109990093046905471381)
                ·
                  refine ⟨6301598905785611573693971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134434109990093046905471381 6301598905785611573693971)
                  ·
                    refine ⟨9452398358678417360540957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6301598905785611573693971 9452398358678417360540957)
                    ·
                      refine ⟨3544649384504406510202859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9452398358678417360540957 3544649384504406510202859)
                      ·
                        rfl

theorem cell23_6903180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_6903180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903180 prefixEnd_6903180 := by exact prefixLift 6903180
  have htrace : WordTrace (prefixWord ++ tailWord_6903180) baseStart_6903180 baseEnd_6903180 := by
    simpa [prefixWord, tailWord_6903180, baseEnd_6903180] using wordTrace_append hprefix tailTrace_6903180
  have hstable : (prefixWord ++ tailWord_6903180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903180).length < 2 ^ (prefixWord ++ tailWord_6903180).sum := by decide
  have hdescent : baseEnd_6903180 < baseStart_6903180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903197 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_6903197 : Nat := 118140960795 + 6903197 * 2 ^ 59
def prefixEnd_6903197 : Nat := 4983230072969 + 3 ^ 40 * 6903197 * 2
def baseEnd_6903197 : Nat := 3544658113675532943690281

theorem tailTrace_6903197 : CollatzResearch.WordTrace tailWord_6903197 prefixEnd_6903197 3544658113675532943690281 := by
  unfold tailWord_6903197
  simp only [CollatzResearch.WordTrace]
  refine ⟨251780279171903716029939845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167853519447935810686626563 251780279171903716029939845)
  ·
    refine ⟨47208802344731946755613721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251780279171903716029939845 47208802344731946755613721)
    ·
      refine ⟨35406601758548960066710291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47208802344731946755613721 35406601758548960066710291)
      ·
        refine ⟨53109902637823440100065437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35406601758548960066710291 53109902637823440100065437)
        ·
          refine ⟨19916213489183790037524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53109902637823440100065437 19916213489183790037524539)
          ·
            refine ⟨29874320233775685056286809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19916213489183790037524539 29874320233775685056286809)
            ·
              refine ⟨22405740175331763792215107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29874320233775685056286809 22405740175331763792215107)
              ·
                refine ⟨33608610262997645688322661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22405740175331763792215107 33608610262997645688322661)
                ·
                  refine ⟨6301614424312058566560499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33608610262997645688322661 6301614424312058566560499)
                  ·
                    refine ⟨9452421636468087849840749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6301614424312058566560499 9452421636468087849840749)
                    ·
                      refine ⟨3544658113675532943690281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9452421636468087849840749 3544658113675532943690281)
                      ·
                        rfl

theorem cell23_6903197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_6903197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903197 prefixEnd_6903197 := by exact prefixLift 6903197
  have htrace : WordTrace (prefixWord ++ tailWord_6903197) baseStart_6903197 baseEnd_6903197 := by
    simpa [prefixWord, tailWord_6903197, baseEnd_6903197] using wordTrace_append hprefix tailTrace_6903197
  have hstable : (prefixWord ++ tailWord_6903197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903197).length < 2 ^ (prefixWord ++ tailWord_6903197).sum := by decide
  have hdescent : baseEnd_6903197 < baseStart_6903197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903198 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6903198 : Nat := 118140960795 + 6903198 * 2 ^ 59
def prefixEnd_6903198 : Nat := 4983230072969 + 3 ^ 40 * 6903198 * 2
def baseEnd_6903198 : Nat := 3544658627156187439777777

theorem tailTrace_6903198 : CollatzResearch.WordTrace tailWord_6903198 prefixEnd_6903198 3544658627156187439777777 := by
  unfold tailWord_6903198
  simp only [CollatzResearch.WordTrace]
  refine ⟨31472539455612511650090781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167853543763266728800484165 31472539455612511650090781)
  ·
    refine ⟨11802202295854691868784043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31472539455612511650090781 11802202295854691868784043)
    ·
      refine ⟨17703303443782037803176065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802202295854691868784043 17703303443782037803176065)
      ·
        refine ⟨13277477582836528352382049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17703303443782037803176065 13277477582836528352382049)
        ·
          refine ⟨9958108187127396264286537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13277477582836528352382049 9958108187127396264286537)
          ·
            refine ⟨7468581140345547198214903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958108187127396264286537 7468581140345547198214903)
            ·
              refine ⟨11202871710518320797322355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468581140345547198214903 11202871710518320797322355)
              ·
                refine ⟨16804307565777481195983533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202871710518320797322355 16804307565777481195983533)
                ·
                  refine ⟨6301615337166555448493825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16804307565777481195983533 6301615337166555448493825)
                  ·
                    refine ⟨4726211502874916586370369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6301615337166555448493825 4726211502874916586370369)
                    ·
                      refine ⟨3544658627156187439777777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726211502874916586370369 3544658627156187439777777)
                      ·
                        rfl

theorem cell23_6903198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6903198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903198 prefixEnd_6903198 := by exact prefixLift 6903198
  have htrace : WordTrace (prefixWord ++ tailWord_6903198) baseStart_6903198 baseEnd_6903198 := by
    simpa [prefixWord, tailWord_6903198, baseEnd_6903198] using wordTrace_append hprefix tailTrace_6903198
  have hstable : (prefixWord ++ tailWord_6903198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903198).length < 2 ^ (prefixWord ++ tailWord_6903198).sum := by decide
  have hdescent : baseEnd_6903198 < baseStart_6903198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903203 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6903203 : Nat := 118140960795 + 6903203 * 2 ^ 59
def prefixEnd_6903203 : Nat := 4983230072969 + 3 ^ 40 * 6903203 * 2
def baseEnd_6903203 : Nat := 3544661194559459920215253

theorem tailTrace_6903203 : CollatzResearch.WordTrace tailWord_6903203 prefixEnd_6903203 3544661194559459920215253 := by
  unfold tailWord_6903203
  simp only [CollatzResearch.WordTrace]
  refine ⟨251780498009881979054658263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167853665339921319369772175 251780498009881979054658263)
  ·
    refine ⟨377670747014822968581987395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251780498009881979054658263 377670747014822968581987395)
    ·
      refine ⟨566506120522234452872981093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377670747014822968581987395 566506120522234452872981093)
      ·
        refine ⟨106219897597918959913683955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566506120522234452872981093 106219897597918959913683955)
        ·
          refine ⟨159329846396878439870525933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106219897597918959913683955 159329846396878439870525933)
          ·
            refine ⟨59748692398829414951447225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159329846396878439870525933 59748692398829414951447225)
            ·
              refine ⟨44811519299122061213585419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59748692398829414951447225 44811519299122061213585419)
              ·
                refine ⟨67217278948683091820378129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44811519299122061213585419 67217278948683091820378129)
                ·
                  refine ⟨50412959211512318865283597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67217278948683091820378129 50412959211512318865283597)
                  ·
                    refine ⟨18904859704317119574481349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50412959211512318865283597 18904859704317119574481349)
                    ·
                      refine ⟨3544661194559459920215253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18904859704317119574481349 3544661194559459920215253)
                      ·
                        rfl

theorem cell23_6903203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6903203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903203 prefixEnd_6903203 := by exact prefixLift 6903203
  have htrace : WordTrace (prefixWord ++ tailWord_6903203) baseStart_6903203 baseEnd_6903203 := by
    simpa [prefixWord, tailWord_6903203, baseEnd_6903203] using wordTrace_append hprefix tailTrace_6903203
  have hstable : (prefixWord ++ tailWord_6903203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903203).length < 2 ^ (prefixWord ++ tailWord_6903203).sum := by decide
  have hdescent : baseEnd_6903203 < baseStart_6903203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903207 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6903207 : Nat := 118140960795 + 6903207 * 2 ^ 59
def prefixEnd_6903207 : Nat := 4983230072969 + 3 ^ 40 * 6903207 * 2
def baseEnd_6903207 : Nat := 3544663248482077904565235

theorem tailTrace_6903207 : CollatzResearch.WordTrace tailWord_6903207 prefixEnd_6903207 3544663248482077904565235 := by
  unfold tailWord_6903207
  simp only [CollatzResearch.WordTrace]
  refine ⟨251780643901867487737803875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167853762601244991825202583 251780643901867487737803875)
  ·
    refine ⟨377670965852801231606705813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251780643901867487737803875 377670965852801231606705813)
    ·
      refine ⟨17703326524350057731564335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 377670965852801231606705813 17703326524350057731564335)
      ·
        refine ⟨26554989786525086597346503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17703326524350057731564335 26554989786525086597346503)
        ·
          refine ⟨39832484679787629896019755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26554989786525086597346503 39832484679787629896019755)
          ·
            refine ⟨59748727019681444844029633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39832484679787629896019755 59748727019681444844029633)
            ·
              refine ⟨44811545264761083633022225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59748727019681444844029633 44811545264761083633022225)
              ·
                refine ⟨33608658948570812724766669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44811545264761083633022225 33608658948570812724766669)
                ·
                  refine ⟨12603247105714054771787501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33608658948570812724766669 12603247105714054771787501)
                  ·
                    refine ⟨4726217664642770539420313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12603247105714054771787501 4726217664642770539420313)
                    ·
                      refine ⟨3544663248482077904565235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726217664642770539420313 3544663248482077904565235)
                      ·
                        rfl

theorem cell23_6903207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6903207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903207 prefixEnd_6903207 := by exact prefixLift 6903207
  have htrace : WordTrace (prefixWord ++ tailWord_6903207) baseStart_6903207 baseEnd_6903207 := by
    simpa [prefixWord, tailWord_6903207, baseEnd_6903207] using wordTrace_append hprefix tailTrace_6903207
  have hstable : (prefixWord ++ tailWord_6903207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903207).length < 2 ^ (prefixWord ++ tailWord_6903207).sum := by decide
  have hdescent : baseEnd_6903207 < baseStart_6903207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903208 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6903208 : Nat := 118140960795 + 6903208 * 2 ^ 59
def prefixEnd_6903208 : Nat := 4983230072969 + 3 ^ 40 * 6903208 * 2
def baseEnd_6903208 : Nat := 1181554587320910800217577

theorem tailTrace_6903208 : CollatzResearch.WordTrace tailWord_6903208 prefixEnd_6903208 1181554587320910800217577 := by
  unfold tailWord_6903208
  simp only [CollatzResearch.WordTrace]
  refine ⟨125890340187431932454295139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167853786916575909939060185 125890340187431932454295139)
  ·
    refine ⟨188835510281147898681442709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125890340187431932454295139 188835510281147898681442709)
    ·
      refine ⟨8851664544428807750692627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188835510281147898681442709 8851664544428807750692627)
      ·
        refine ⟨13277496816643211626038941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851664544428807750692627 13277496816643211626038941)
        ·
          refine ⟨4979061306241204359764603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13277496816643211626038941 4979061306241204359764603)
          ·
            refine ⟨7468591959361806539646905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979061306241204359764603 7468591959361806539646905)
            ·
              refine ⟨5601443969521354904735179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7468591959361806539646905 5601443969521354904735179)
              ·
                refine ⟨8402165954282032357102769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601443969521354904735179 8402165954282032357102769)
                ·
                  refine ⟨6301624465711524267827077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402165954282032357102769 6301624465711524267827077)
                  ·
                    refine ⟨1181554587320910800217577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301624465711524267827077 1181554587320910800217577)
                    ·
                      rfl

theorem cell23_6903208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6903208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903208 prefixEnd_6903208 := by exact prefixLift 6903208
  have htrace : WordTrace (prefixWord ++ tailWord_6903208) baseStart_6903208 baseEnd_6903208 := by
    simpa [prefixWord, tailWord_6903208, baseEnd_6903208] using wordTrace_append hprefix tailTrace_6903208
  have hstable : (prefixWord ++ tailWord_6903208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903208).length < 2 ^ (prefixWord ++ tailWord_6903208).sum := by decide
  have hdescent : baseEnd_6903208 < baseStart_6903208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903223 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_6903223 : Nat := 118140960795 + 6903223 * 2 ^ 59
def prefixEnd_6903223 : Nat := 4983230072969 + 3 ^ 40 * 6903223 * 2
def baseEnd_6903223 : Nat := 3544671464172549841965161

theorem tailTrace_6903223 : CollatzResearch.WordTrace tailWord_6903223 prefixEnd_6903223 3544671464172549841965161 := by
  unfold tailWord_6903223
  simp only [CollatzResearch.WordTrace]
  refine ⟨251781227469809522470386323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167854151646539681646924215 251781227469809522470386323)
  ·
    refine ⟨377671841204714283705579485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251781227469809522470386323 377671841204714283705579485)
    ·
      refine ⟨141626940451767856389592307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377671841204714283705579485 141626940451767856389592307)
      ·
        refine ⟨212440410677651784584388461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141626940451767856389592307 212440410677651784584388461)
        ·
          refine ⟨79665154004119419219145673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212440410677651784584388461 79665154004119419219145673)
          ·
            refine ⟨59748865503089564414359255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79665154004119419219145673 59748865503089564414359255)
            ·
              refine ⟨89623298254634346621538883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59748865503089564414359255 89623298254634346621538883)
              ·
                refine ⟨134434947381951519932308325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89623298254634346621538883 134434947381951519932308325)
                ·
                  refine ⟨25206552634115909987307811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134434947381951519932308325 25206552634115909987307811)
                  ·
                    refine ⟨37809828951173864980961717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25206552634115909987307811 37809828951173864980961717)
                    ·
                      refine ⟨3544671464172549841965161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37809828951173864980961717 3544671464172549841965161)
                      ·
                        rfl

theorem cell23_6903223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_6903223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903223 prefixEnd_6903223 := by exact prefixLift 6903223
  have htrace : WordTrace (prefixWord ++ tailWord_6903223) baseStart_6903223 baseEnd_6903223 := by
    simpa [prefixWord, tailWord_6903223, baseEnd_6903223] using wordTrace_append hprefix tailTrace_6903223
  have hstable : (prefixWord ++ tailWord_6903223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903223).length < 2 ^ (prefixWord ++ tailWord_6903223).sum := by decide
  have hdescent : baseEnd_6903223 < baseStart_6903223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903277 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 7]
def baseStart_6903277 : Nat := 118140960795 + 6903277 * 2 ^ 59
def prefixEnd_6903277 : Nat := 4983230072969 + 3 ^ 40 * 6903277 * 2
def baseEnd_6903277 : Nat := 393855465791988070076657

theorem tailTrace_6903277 : CollatzResearch.WordTrace tailWord_6903277 prefixEnd_6903277 393855465791988070076657 := by
  unfold tailWord_6903277
  simp only [CollatzResearch.WordTrace]
  refine ⟨251783197011613889692852085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167855464674409259795234723 251783197011613889692852085)
  ·
    refine ⟨23604674719838802158704883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251783197011613889692852085 23604674719838802158704883)
    ·
      refine ⟨35407012079758203238057325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23604674719838802158704883 35407012079758203238057325)
      ·
        refine ⟨13277629529909326214271497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35407012079758203238057325 13277629529909326214271497)
        ·
          refine ⟨9958222147431994660703623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13277629529909326214271497 9958222147431994660703623)
          ·
            refine ⟨14937333221147991991055435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958222147431994660703623 14937333221147991991055435)
            ·
              refine ⟨22405999831721987986583153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14937333221147991991055435 22405999831721987986583153)
              ·
                refine ⟨16804499873791490989937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22405999831721987986583153 16804499873791490989937365)
                ·
                  refine ⟨393855465791988070076657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16804499873791490989937365 393855465791988070076657)
                  ·
                    rfl

theorem cell23_6903277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_6903277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903277 prefixEnd_6903277 := by exact prefixLift 6903277
  have htrace : WordTrace (prefixWord ++ tailWord_6903277) baseStart_6903277 baseEnd_6903277 := by
    simpa [prefixWord, tailWord_6903277, baseEnd_6903277] using wordTrace_append hprefix tailTrace_6903277
  have hstable : (prefixWord ++ tailWord_6903277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903277).length < 2 ^ (prefixWord ++ tailWord_6903277).sum := by decide
  have hdescent : baseEnd_6903277 < baseStart_6903277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903283 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_6903283 : Nat := 118140960795 + 6903283 * 2 ^ 59
def prefixEnd_6903283 : Nat := 4983230072969 + 3 ^ 40 * 6903283 * 2
def baseEnd_6903283 : Nat := 3544702273011819607214885

theorem tailTrace_6903283 : CollatzResearch.WordTrace tailWord_6903283 prefixEnd_6903283 3544702273011819607214885 := by
  unfold tailWord_6903283
  simp only [CollatzResearch.WordTrace]
  refine ⟨251783415849592152717570503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167855610566394768478380335 251783415849592152717570503)
  ·
    refine ⟨377675123774388229076355755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251783415849592152717570503 377675123774388229076355755)
    ·
      refine ⟨566512685661582343614533633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377675123774388229076355755 566512685661582343614533633)
      ·
        refine ⟨424884514246186757710900225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566512685661582343614533633 424884514246186757710900225)
        ·
          refine ⟨318663385684640068283175169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424884514246186757710900225 318663385684640068283175169)
          ·
            refine ⟨238997539263480051212381377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318663385684640068283175169 238997539263480051212381377)
            ·
              refine ⟨179248154447610038409286033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238997539263480051212381377 179248154447610038409286033)
              ·
                refine ⟨134436115835707528806964525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179248154447610038409286033 134436115835707528806964525)
                ·
                  refine ⟨50413543438390323302611697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134436115835707528806964525 50413543438390323302611697)
                  ·
                    refine ⟨37810157578792742476958773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50413543438390323302611697 37810157578792742476958773)
                    ·
                      refine ⟨3544702273011819607214885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37810157578792742476958773 3544702273011819607214885)
                      ·
                        rfl

theorem cell23_6903283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_6903283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903283 prefixEnd_6903283 := by exact prefixLift 6903283
  have htrace : WordTrace (prefixWord ++ tailWord_6903283) baseStart_6903283 baseEnd_6903283 := by
    simpa [prefixWord, tailWord_6903283, baseEnd_6903283] using wordTrace_append hprefix tailTrace_6903283
  have hstable : (prefixWord ++ tailWord_6903283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903283).length < 2 ^ (prefixWord ++ tailWord_6903283).sum := by decide
  have hdescent : baseEnd_6903283 < baseStart_6903283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903327 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 4, 2]
def baseStart_6903327 : Nat := 118140960795 + 6903327 * 2 ^ 59
def prefixEnd_6903327 : Nat := 4983230072969 + 3 ^ 40 * 6903327 * 2
def baseEnd_6903327 : Nat := 3544724866160617435064683

theorem tailTrace_6903327 : CollatzResearch.WordTrace tailWord_6903327 prefixEnd_6903327 3544724866160617435064683 := by
  unfold tailWord_6903327
  simp only [CollatzResearch.WordTrace]
  refine ⟨251785020661432748232172235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167856680440955165488114823 251785020661432748232172235)
  ·
    refine ⟨377677530992149122348258353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251785020661432748232172235 377677530992149122348258353)
    ·
      refine ⟨283258148244111841761193765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377677530992149122348258353 283258148244111841761193765)
      ·
        refine ⟨53110902795770970330223831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283258148244111841761193765 53110902795770970330223831)
        ·
          refine ⟨79666354193656455495335747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53110902795770970330223831 79666354193656455495335747)
          ·
            refine ⟨119499531290484683243003621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79666354193656455495335747 119499531290484683243003621)
            ·
              refine ⟨22406162116965878108063179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119499531290484683243003621 22406162116965878108063179)
              ·
                refine ⟨33609243175448817162094769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22406162116965878108063179 33609243175448817162094769)
                ·
                  refine ⟨25206932381586612871571077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33609243175448817162094769 25206932381586612871571077)
                  ·
                    refine ⟨4726299821547489913419577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25206932381586612871571077 4726299821547489913419577)
                    ·
                      refine ⟨3544724866160617435064683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726299821547489913419577 3544724866160617435064683)
                      ·
                        rfl

theorem cell23_6903327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_6903327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903327 prefixEnd_6903327 := by exact prefixLift 6903327
  have htrace : WordTrace (prefixWord ++ tailWord_6903327) baseStart_6903327 baseEnd_6903327 := by
    simpa [prefixWord, tailWord_6903327, baseEnd_6903327] using wordTrace_append hprefix tailTrace_6903327
  have hstable : (prefixWord ++ tailWord_6903327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903327).length < 2 ^ (prefixWord ++ tailWord_6903327).sum := by decide
  have hdescent : baseEnd_6903327 < baseStart_6903327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903343 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_6903343 : Nat := 118140960795 + 6903343 * 2 ^ 59
def prefixEnd_6903343 : Nat := 4983230072969 + 3 ^ 40 * 6903343 * 2
def baseEnd_6903343 : Nat := 3544733081851089372464609

theorem tailTrace_6903343 : CollatzResearch.WordTrace tailWord_6903343 prefixEnd_6903343 3544733081851089372464609 := by
  unfold tailWord_6903343
  simp only [CollatzResearch.WordTrace]
  refine ⟨251785604229374782964754683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167857069486249855309836455 251785604229374782964754683)
  ·
    refine ⟨377678406344062174447132025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251785604229374782964754683 377678406344062174447132025)
    ·
      refine ⟨283258804758046630835349019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377678406344062174447132025 283258804758046630835349019)
      ·
        refine ⟨424888207137069946253023529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283258804758046630835349019 424888207137069946253023529)
        ·
          refine ⟨318666155352802459689767647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424888207137069946253023529 318666155352802459689767647)
          ·
            refine ⟨477999233029203689534651471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318666155352802459689767647 477999233029203689534651471)
            ·
              refine ⟨716998849543805534301977207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477999233029203689534651471 716998849543805534301977207)
              ·
                refine ⟨1075498274315708301452965811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716998849543805534301977207 1075498274315708301452965811)
                ·
                  refine ⟨1613247411473562452179448717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075498274315708301452965811 1613247411473562452179448717)
                  ·
                    refine ⟨604967779302585919567293269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1613247411473562452179448717 604967779302585919567293269)
                    ·
                      refine ⟨3544733081851089372464609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 604967779302585919567293269 3544733081851089372464609)
                      ·
                        rfl

theorem cell23_6903343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_6903343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903343 prefixEnd_6903343 := by exact prefixLift 6903343
  have htrace : WordTrace (prefixWord ++ tailWord_6903343) baseStart_6903343 baseEnd_6903343 := by
    simpa [prefixWord, tailWord_6903343, baseEnd_6903343] using wordTrace_append hprefix tailTrace_6903343
  have hstable : (prefixWord ++ tailWord_6903343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903343).length < 2 ^ (prefixWord ++ tailWord_6903343).sum := by decide
  have hdescent : baseEnd_6903343 < baseStart_6903343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903397 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_6903397 : Nat := 118140960795 + 6903397 * 2 ^ 59
def prefixEnd_6903397 : Nat := 4983230072969 + 3 ^ 40 * 6903397 * 2
def baseEnd_6903397 : Nat := 1181586936602144053729787

theorem tailTrace_6903397 : CollatzResearch.WordTrace tailWord_6903397 prefixEnd_6903397 1181586936602144053729787 := by
  unfold tailWord_6903397
  simp only [CollatzResearch.WordTrace]
  refine ⟨251787573771179150187220445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167858382514119433458146963 251787573771179150187220445)
  ·
    refine ⟨94420340164192181320207667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251787573771179150187220445 94420340164192181320207667)
    ·
      refine ⟨141630510246288271980311501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94420340164192181320207667 141630510246288271980311501)
      ·
        refine ⟨53111441342358101992616813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141630510246288271980311501 53111441342358101992616813)
        ·
          refine ⟨19916790503384288247231305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53111441342358101992616813 19916790503384288247231305)
          ·
            refine ⟨14937592877538216185423479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19916790503384288247231305 14937592877538216185423479)
            ·
              refine ⟨22406389316307324278135219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14937592877538216185423479 22406389316307324278135219)
              ·
                refine ⟨33609583974460986417202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22406389316307324278135219 33609583974460986417202829)
                ·
                  refine ⟨12603593990422869906451061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33609583974460986417202829 12603593990422869906451061)
                  ·
                    refine ⟨1181586936602144053729787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12603593990422869906451061 1181586936602144053729787)
                    ·
                      rfl

theorem cell23_6903397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_6903397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903397 prefixEnd_6903397 := by exact prefixLift 6903397
  have htrace : WordTrace (prefixWord ++ tailWord_6903397) baseStart_6903397 baseEnd_6903397 := by
    simpa [prefixWord, tailWord_6903397, baseEnd_6903397] using wordTrace_append hprefix tailTrace_6903397
  have hstable : (prefixWord ++ tailWord_6903397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903397).length < 2 ^ (prefixWord ++ tailWord_6903397).sum := by decide
  have hdescent : baseEnd_6903397 < baseStart_6903397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903428 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6903428 : Nat := 118140960795 + 6903428 * 2 ^ 59
def prefixEnd_6903428 : Nat := 4983230072969 + 3 ^ 40 * 6903428 * 2
def baseEnd_6903428 : Nat := 3544776727706721539901719

theorem tailTrace_6903428 : CollatzResearch.WordTrace tailWord_6903428 prefixEnd_6903428 3544776727706721539901719 := by
  unfold tailWord_6903428
  simp only [CollatzResearch.WordTrace]
  refine ⟨125894352217033421240799469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167859136289377894987732625 125894352217033421240799469)
  ·
    refine ⟨47210382081387532965299801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125894352217033421240799469 47210382081387532965299801)
    ·
      refine ⟨35407786561040649723974851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47210382081387532965299801 35407786561040649723974851)
      ·
        refine ⟨53111679841560974585962277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35407786561040649723974851 53111679841560974585962277)
        ·
          refine ⟨9958439970292682734867927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53111679841560974585962277 9958439970292682734867927)
          ·
            refine ⟨14937659955439024102301891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958439970292682734867927 14937659955439024102301891)
            ·
              refine ⟨22406489933158536153452837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14937659955439024102301891 22406489933158536153452837)
              ·
                refine ⟨4201216862467225528772407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22406489933158536153452837 4201216862467225528772407)
                ·
                  refine ⟨6301825293700838293158611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201216862467225528772407 6301825293700838293158611)
                  ·
                    refine ⟨9452737940551257439737917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6301825293700838293158611 9452737940551257439737917)
                    ·
                      refine ⟨3544776727706721539901719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9452737940551257439737917 3544776727706721539901719)
                      ·
                        rfl

theorem cell23_6903428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6903428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903428 prefixEnd_6903428 := by exact prefixLift 6903428
  have htrace : WordTrace (prefixWord ++ tailWord_6903428) baseStart_6903428 baseEnd_6903428 := by
    simpa [prefixWord, tailWord_6903428, baseEnd_6903428] using wordTrace_append hprefix tailTrace_6903428
  have hstable : (prefixWord ++ tailWord_6903428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903428).length < 2 ^ (prefixWord ++ tailWord_6903428).sum := by decide
  have hdescent : baseEnd_6903428 < baseStart_6903428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903447 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_6903447 : Nat := 118140960795 + 6903447 * 2 ^ 59
def prefixEnd_6903447 : Nat := 4983230072969 + 3 ^ 40 * 6903447 * 2
def baseEnd_6903447 : Nat := 3544786483839156965564131

theorem tailTrace_6903447 : CollatzResearch.WordTrace tailWord_6903447 prefixEnd_6903447 3544786483839156965564131 := by
  unfold tailWord_6903447
  simp only [CollatzResearch.WordTrace]
  refine ⟨251789397420998008726540595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167859598280665339151027063 251789397420998008726540595)
  ·
    refine ⟨377684096131497013089810893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251789397420998008726540595 377684096131497013089810893)
    ·
      refine ⟨141631536049311379908679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377684096131497013089810893 141631536049311379908679085)
      ·
        refine ⟨53111826018491767465754657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141631536049311379908679085 53111826018491767465754657)
        ·
          refine ⟨39833869513868825599315993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53111826018491767465754657 39833869513868825599315993)
          ·
            refine ⟨29875402135401619199486995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39833869513868825599315993 29875402135401619199486995)
            ·
              refine ⟨44813103203102428799230493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29875402135401619199486995 44813103203102428799230493)
              ·
                refine ⟨16804913701163410799711435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44813103203102428799230493 16804913701163410799711435)
                ·
                  refine ⟨25207370551745116199567153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16804913701163410799711435 25207370551745116199567153)
                  ·
                    refine ⟨18905527913808837149675365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25207370551745116199567153 18905527913808837149675365)
                    ·
                      refine ⟨3544786483839156965564131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18905527913808837149675365 3544786483839156965564131)
                      ·
                        rfl

theorem cell23_6903447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_6903447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903447 prefixEnd_6903447 := by exact prefixLift 6903447
  have htrace : WordTrace (prefixWord ++ tailWord_6903447) baseStart_6903447 baseEnd_6903447 := by
    simpa [prefixWord, tailWord_6903447, baseEnd_6903447] using wordTrace_append hprefix tailTrace_6903447
  have hstable : (prefixWord ++ tailWord_6903447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903447).length < 2 ^ (prefixWord ++ tailWord_6903447).sum := by decide
  have hdescent : baseEnd_6903447 < baseStart_6903447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903455 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6903455 : Nat := 118140960795 + 6903455 * 2 ^ 59
def prefixEnd_6903455 : Nat := 4983230072969 + 3 ^ 40 * 6903455 * 2
def baseEnd_6903455 : Nat := 3544790591684392934264095

theorem tailTrace_6903455 : CollatzResearch.WordTrace tailWord_6903455 prefixEnd_6903455 3544790591684392934264095 := by
  unfold tailWord_6903455
  simp only [CollatzResearch.WordTrace]
  refine ⟨251789689204969026092831819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167859792803312684061887879 251789689204969026092831819)
  ·
    refine ⟨377684533807453539139247729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251789689204969026092831819 377684533807453539139247729)
    ·
      refine ⟨283263400355590154354435797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377684533807453539139247729 283263400355590154354435797)
      ·
        refine ⟨6638985945834144242682089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 283263400355590154354435797 6638985945834144242682089)
        ·
          refine ⟨4979239459375608182011567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6638985945834144242682089 4979239459375608182011567)
          ·
            refine ⟨7468859189063412273017351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979239459375608182011567 7468859189063412273017351)
            ·
              refine ⟨11203288783595118409526027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468859189063412273017351 11203288783595118409526027)
              ·
                refine ⟨16804933175392677614289041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11203288783595118409526027 16804933175392677614289041)
                ·
                  refine ⟨12603699881544508210716781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16804933175392677614289041 12603699881544508210716781)
                  ·
                    refine ⟨4726387455579190579018793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12603699881544508210716781 4726387455579190579018793)
                    ·
                      refine ⟨3544790591684392934264095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726387455579190579018793 3544790591684392934264095)
                      ·
                        rfl

theorem cell23_6903455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6903455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903455 prefixEnd_6903455 := by exact prefixLift 6903455
  have htrace : WordTrace (prefixWord ++ tailWord_6903455) baseStart_6903455 baseEnd_6903455 := by
    simpa [prefixWord, tailWord_6903455, baseEnd_6903455] using wordTrace_append hprefix tailTrace_6903455
  have hstable : (prefixWord ++ tailWord_6903455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903455).length < 2 ^ (prefixWord ++ tailWord_6903455).sum := by decide
  have hdescent : baseEnd_6903455 < baseStart_6903455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903478 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6903478 : Nat := 118140960795 + 6903478 * 2 ^ 59
def prefixEnd_6903478 : Nat := 4983230072969 + 3 ^ 40 * 6903478 * 2
def baseEnd_6903478 : Nat := 1181600800579815448092163

theorem tailTrace_6903478 : CollatzResearch.WordTrace tailWord_6903478 prefixEnd_6903478 1181600800579815448092163 := by
  unfold tailWord_6903478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736908005242856313807443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167860352055923800680612725 15736908005242856313807443)
  ·
    refine ⟨23605362007864284470711165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736908005242856313807443 23605362007864284470711165)
    ·
      refine ⟨8852010752949106676516687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23605362007864284470711165 8852010752949106676516687)
      ·
        refine ⟨13278016129423660014775031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852010752949106676516687 13278016129423660014775031)
        ·
          refine ⟨19917024194135490022162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13278016129423660014775031 19917024194135490022162547)
          ·
            refine ⟨29875536291203235033243821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19917024194135490022162547 29875536291203235033243821)
            ·
              refine ⟨11203326109201213137466433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29875536291203235033243821 11203326109201213137466433)
              ·
                refine ⟨8402494581900909853099825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11203326109201213137466433 8402494581900909853099825)
                ·
                  refine ⟨6301870936425682389824869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402494581900909853099825 6301870936425682389824869)
                  ·
                    refine ⟨1181600800579815448092163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6301870936425682389824869 1181600800579815448092163)
                    ·
                      rfl

theorem cell23_6903478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6903478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903478 prefixEnd_6903478 := by exact prefixLift 6903478
  have htrace : WordTrace (prefixWord ++ tailWord_6903478) baseStart_6903478 baseEnd_6903478 := by
    simpa [prefixWord, tailWord_6903478, baseEnd_6903478] using wordTrace_append hprefix tailTrace_6903478
  have hstable : (prefixWord ++ tailWord_6903478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903478).length < 2 ^ (prefixWord ++ tailWord_6903478).sum := by decide
  have hdescent : baseEnd_6903478 < baseStart_6903478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903511 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 1, 3, 2]
def baseStart_6903511 : Nat := 118140960795 + 6903511 * 2 ^ 59
def prefixEnd_6903511 : Nat := 4983230072969 + 3 ^ 40 * 6903511 * 2
def baseEnd_6903511 : Nat := 3544819346601044715163837

theorem tailTrace_6903511 : CollatzResearch.WordTrace tailWord_6903511 prefixEnd_6903511 3544819346601044715163837 := by
  unfold tailWord_6903511
  simp only [CollatzResearch.WordTrace]
  refine ⟨251791731692766147656870387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167861154461844098437913591 251791731692766147656870387)
  ·
    refine ⟨377687597539149221485305581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251791731692766147656870387 377687597539149221485305581)
    ·
      refine ⟨141632849077180958056989593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377687597539149221485305581 141632849077180958056989593)
      ·
        refine ⟨106224636807885718542742195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141632849077180958056989593 106224636807885718542742195)
        ·
          refine ⟨159336955211828577814113293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106224636807885718542742195 159336955211828577814113293)
          ·
            refine ⟨59751358204435716680292485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159336955211828577814113293 59751358204435716680292485)
            ·
              refine ⟨11203379663331696877554841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59751358204435716680292485 11203379663331696877554841)
              ·
                refine ⟨8402534747498772658166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11203379663331696877554841 8402534747498772658166131)
                ·
                  refine ⟨12603802121248158987249197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8402534747498772658166131 12603802121248158987249197)
                  ·
                    refine ⟨4726425795468059620218449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12603802121248158987249197 4726425795468059620218449)
                    ·
                      refine ⟨3544819346601044715163837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726425795468059620218449 3544819346601044715163837)
                      ·
                        rfl

theorem cell23_6903511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 3, 2].length) (baseStart_6903511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903511 prefixEnd_6903511 := by exact prefixLift 6903511
  have htrace : WordTrace (prefixWord ++ tailWord_6903511) baseStart_6903511 baseEnd_6903511 := by
    simpa [prefixWord, tailWord_6903511, baseEnd_6903511] using wordTrace_append hprefix tailTrace_6903511
  have hstable : (prefixWord ++ tailWord_6903511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903511).length < 2 ^ (prefixWord ++ tailWord_6903511).sum := by decide
  have hdescent : baseEnd_6903511 < baseStart_6903511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903524 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_6903524 : Nat := 118140960795 + 6903524 * 2 ^ 59
def prefixEnd_6903524 : Nat := 4983230072969 + 3 ^ 40 * 6903524 * 2
def baseEnd_6903524 : Nat := 3544826021849553164301277

theorem tailTrace_6903524 : CollatzResearch.WordTrace tailWord_6903524 prefixEnd_6903524 3544826021849553164301277 := by
  unfold tailWord_6903524
  simp only [CollatzResearch.WordTrace]
  refine ⟨125896102920859525438546813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167861470561146033918062417 125896102920859525438546813)
  ·
    refine ⟨47211038595322322039455055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125896102920859525438546813 47211038595322322039455055)
    ·
      refine ⟨70816557892983483059182583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47211038595322322039455055 70816557892983483059182583)
      ·
        refine ⟨106224836839475224588773875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70816557892983483059182583 106224836839475224588773875)
        ·
          refine ⟨159337255259212836883160813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106224836839475224588773875 159337255259212836883160813)
          ·
            refine ⟨59751470722204813831185305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159337255259212836883160813 59751470722204813831185305)
            ·
              refine ⟨44813603041653610373388979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59751470722204813831185305 44813603041653610373388979)
              ·
                refine ⟨67220404562480415560083469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44813603041653610373388979 67220404562480415560083469)
                ·
                  refine ⟨25207651710930155835031301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67220404562480415560083469 25207651710930155835031301)
                  ·
                    refine ⟨4726434695799404219068369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25207651710930155835031301 4726434695799404219068369)
                    ·
                      refine ⟨3544826021849553164301277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726434695799404219068369 3544826021849553164301277)
                      ·
                        rfl

theorem cell23_6903524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_6903524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903524 prefixEnd_6903524 := by exact prefixLift 6903524
  have htrace : WordTrace (prefixWord ++ tailWord_6903524) baseStart_6903524 baseEnd_6903524 := by
    simpa [prefixWord, tailWord_6903524, baseEnd_6903524] using wordTrace_append hprefix tailTrace_6903524
  have hstable : (prefixWord ++ tailWord_6903524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903524).length < 2 ^ (prefixWord ++ tailWord_6903524).sum := by decide
  have hdescent : baseEnd_6903524 < baseStart_6903524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903554 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6903554 : Nat := 118140960795 + 6903554 * 2 ^ 59
def prefixEnd_6903554 : Nat := 4983230072969 + 3 ^ 40 * 6903554 * 2
def baseEnd_6903554 : Nat := 3544841426269188046926139

theorem tailTrace_6903554 : CollatzResearch.WordTrace tailWord_6903554 prefixEnd_6903554 3544841426269188046926139 := by
  unfold tailWord_6903554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62948325007902591500171429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167862200021073577333790477 62948325007902591500171429)
  ·
    refine ⟨11802810938981735906282143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62948325007902591500171429 11802810938981735906282143)
    ·
      refine ⟨17704216408472603859423215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802810938981735906282143 17704216408472603859423215)
      ·
        refine ⟨26556324612708905789134823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704216408472603859423215 26556324612708905789134823)
        ·
          refine ⟨39834486919063358683702235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26556324612708905789134823 39834486919063358683702235)
          ·
            refine ⟨59751730378595038025553353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39834486919063358683702235 59751730378595038025553353)
            ·
              refine ⟨44813797783946278519165015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59751730378595038025553353 44813797783946278519165015)
              ·
                refine ⟨67220696675919417778747523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44813797783946278519165015 67220696675919417778747523)
                ·
                  refine ⟨100831045013879126668121285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67220696675919417778747523 100831045013879126668121285)
                  ·
                    refine ⟨18905820940102336250272741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100831045013879126668121285 18905820940102336250272741)
                    ·
                      refine ⟨3544841426269188046926139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18905820940102336250272741 3544841426269188046926139)
                      ·
                        rfl

theorem cell23_6903554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6903554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903554 prefixEnd_6903554 := by exact prefixLift 6903554
  have htrace : WordTrace (prefixWord ++ tailWord_6903554) baseStart_6903554 baseEnd_6903554 := by
    simpa [prefixWord, tailWord_6903554, baseEnd_6903554] using wordTrace_append hprefix tailTrace_6903554
  have hstable : (prefixWord ++ tailWord_6903554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903554).length < 2 ^ (prefixWord ++ tailWord_6903554).sum := by decide
  have hdescent : baseEnd_6903554 < baseStart_6903554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903587 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6903587 : Nat := 118140960795 + 6903587 * 2 ^ 59
def prefixEnd_6903587 : Nat := 4983230072969 + 3 ^ 40 * 6903587 * 2
def baseEnd_6903587 : Nat := 3544858371130786417813487

theorem tailTrace_6903587 : CollatzResearch.WordTrace tailWord_6903587 prefixEnd_6903587 3544858371130786417813487 := by
  unfold tailWord_6903587
  simp only [CollatzResearch.WordTrace]
  refine ⟨251794503640490812636637015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167863002426993875091091343 251794503640490812636637015)
  ·
    refine ⟨377691755460736218954955523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251794503640490812636637015 377691755460736218954955523)
    ·
      refine ⟨566537633191104328432433285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377691755460736218954955523 566537633191104328432433285)
      ·
        refine ⟨106225806223332061581081241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 566537633191104328432433285 106225806223332061581081241)
        ·
          refine ⟨79669354667499046185810931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106225806223332061581081241 79669354667499046185810931)
          ·
            refine ⟨119504032001248569278716397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79669354667499046185810931 119504032001248569278716397)
            ·
              refine ⟨44814012000468213479518649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119504032001248569278716397 44814012000468213479518649)
              ·
                refine ⟨33610509000351160109638987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44814012000468213479518649 33610509000351160109638987)
                ·
                  refine ⟨50415763500526740164458481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33610509000351160109638987 50415763500526740164458481)
                  ·
                    refine ⟨37811822625395055123343861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50415763500526740164458481 37811822625395055123343861)
                    ·
                      refine ⟨3544858371130786417813487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37811822625395055123343861 3544858371130786417813487)
                      ·
                        rfl

theorem cell23_6903587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6903587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903587 prefixEnd_6903587 := by exact prefixLift 6903587
  have htrace : WordTrace (prefixWord ++ tailWord_6903587) baseStart_6903587 baseEnd_6903587 := by
    simpa [prefixWord, tailWord_6903587, baseEnd_6903587] using wordTrace_append hprefix tailTrace_6903587
  have hstable : (prefixWord ++ tailWord_6903587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903587).length < 2 ^ (prefixWord ++ tailWord_6903587).sum := by decide
  have hdescent : baseEnd_6903587 < baseStart_6903587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903598 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_6903598 : Nat := 118140960795 + 6903598 * 2 ^ 59
def prefixEnd_6903598 : Nat := 4983230072969 + 3 ^ 40 * 6903598 * 2
def baseEnd_6903598 : Nat := 393873779935331763863993

theorem tailTrace_6903598 : CollatzResearch.WordTrace tailWord_6903598 prefixEnd_6903598 393873779935331763863993 := by
  unfold tailWord_6903598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474363105431370189410931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167863269895633974343524965 31474363105431370189410931)
  ·
    refine ⟨47211544658147055284116397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31474363105431370189410931 47211544658147055284116397)
    ·
      refine ⟨17704329246805145731543649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47211544658147055284116397 17704329246805145731543649)
      ·
        refine ⟨13278246935103859298657737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17704329246805145731543649 13278246935103859298657737)
        ·
          refine ⟨9958685201327894473993303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13278246935103859298657737 9958685201327894473993303)
          ·
            refine ⟨14938027801991841710989955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958685201327894473993303 14938027801991841710989955)
            ·
              refine ⟨22407041702987762566484933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938027801991841710989955 22407041702987762566484933)
              ·
                refine ⟨4201320319310205481215925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22407041702987762566484933 4201320319310205481215925)
                ·
                  refine ⟨393873779935331763863993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4201320319310205481215925 393873779935331763863993)
                  ·
                    rfl

theorem cell23_6903598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_6903598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903598 prefixEnd_6903598 := by exact prefixLift 6903598
  have htrace : WordTrace (prefixWord ++ tailWord_6903598) baseStart_6903598 baseEnd_6903598 := by
    simpa [prefixWord, tailWord_6903598, baseEnd_6903598] using wordTrace_append hprefix tailTrace_6903598
  have hstable : (prefixWord ++ tailWord_6903598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903598).length < 2 ^ (prefixWord ++ tailWord_6903598).sum := by decide
  have hdescent : baseEnd_6903598 < baseStart_6903598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903624 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_6903624 : Nat := 118140960795 + 6903624 * 2 ^ 59
def prefixEnd_6903624 : Nat := 4983230072969 + 3 ^ 40 * 6903624 * 2
def baseEnd_6903624 : Nat := 1181625789971667591016939

theorem tailTrace_6903624 : CollatzResearch.WordTrace tailWord_6903624 prefixEnd_6903624 1181625789971667591016939 := by
  unfold tailWord_6903624
  simp only [CollatzResearch.WordTrace]
  refine ⟨125897926570678383977866963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167863902094237845303822617 125897926570678383977866963)
  ·
    refine ⟨188846889856017575966800445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125897926570678383977866963 188846889856017575966800445)
    ·
      refine ⟨70817583696006590987550167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188846889856017575966800445 70817583696006590987550167)
      ·
        refine ⟨106226375544009886481325251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70817583696006590987550167 106226375544009886481325251)
        ·
          refine ⟨159339563316014829721987877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106226375544009886481325251 159339563316014829721987877)
          ·
            refine ⟨29876168121752780572872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159339563316014829721987877 29876168121752780572872727)
            ·
              refine ⟨44814252182629170859309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29876168121752780572872727 44814252182629170859309091)
              ·
                refine ⟨67221378273943756288963637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44814252182629170859309091 67221378273943756288963637)
                ·
                  refine ⟨6302004213182227152090341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67221378273943756288963637 6302004213182227152090341)
                  ·
                    refine ⟨1181625789971667591016939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302004213182227152090341 1181625789971667591016939)
                    ·
                      rfl

theorem cell23_6903624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_6903624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903624 prefixEnd_6903624 := by exact prefixLift 6903624
  have htrace : WordTrace (prefixWord ++ tailWord_6903624) baseStart_6903624 baseEnd_6903624 := by
    simpa [prefixWord, tailWord_6903624, baseEnd_6903624] using wordTrace_append hprefix tailTrace_6903624
  have hstable : (prefixWord ++ tailWord_6903624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903624).length < 2 ^ (prefixWord ++ tailWord_6903624).sum := by decide
  have hdescent : baseEnd_6903624 < baseStart_6903624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903628 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_6903628 : Nat := 118140960795 + 6903628 * 2 ^ 59
def prefixEnd_6903628 : Nat := 4983230072969 + 3 ^ 40 * 6903628 * 2
def baseEnd_6903628 : Nat := 1181626474612540252466933

theorem tailTrace_6903628 : CollatzResearch.WordTrace tailWord_6903628 prefixEnd_6903628 1181626474612540252466933 := by
  unfold tailWord_6903628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125897999516671138319439769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167863999355561517759253025 125897999516671138319439769)
  ·
    refine ⟨94423499637503353739579827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125897999516671138319439769 94423499637503353739579827)
    ·
      refine ⟨141635249456255030609369741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94423499637503353739579827 141635249456255030609369741)
      ·
        refine ⟨53113218546095636478513653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141635249456255030609369741 53113218546095636478513653)
        ·
          refine ⟨4979364238696465919860655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53113218546095636478513653 4979364238696465919860655)
          ·
            refine ⟨7469046358044698879790983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979364238696465919860655 7469046358044698879790983)
            ·
              refine ⟨11203569537067048319686475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469046358044698879790983 11203569537067048319686475)
              ·
                refine ⟨16805354305600572479529713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11203569537067048319686475 16805354305600572479529713)
                ·
                  refine ⟨12604015729200429359647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16805354305600572479529713 12604015729200429359647285)
                  ·
                    refine ⟨1181626474612540252466933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12604015729200429359647285 1181626474612540252466933)
                    ·
                      rfl

theorem cell23_6903628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_6903628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903628 prefixEnd_6903628 := by exact prefixLift 6903628
  have htrace : WordTrace (prefixWord ++ tailWord_6903628) baseStart_6903628 baseEnd_6903628 := by
    simpa [prefixWord, tailWord_6903628, baseEnd_6903628] using wordTrace_append hprefix tailTrace_6903628
  have hstable : (prefixWord ++ tailWord_6903628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903628).length < 2 ^ (prefixWord ++ tailWord_6903628).sum := by decide
  have hdescent : baseEnd_6903628 < baseStart_6903628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903684 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6903684 : Nat := 118140960795 + 6903684 * 2 ^ 59
def prefixEnd_6903684 : Nat := 4983230072969 + 3 ^ 40 * 6903684 * 2
def baseEnd_6903684 : Nat := 1181636059584757512766847

theorem tailTrace_6903684 : CollatzResearch.WordTrace tailWord_6903684 prefixEnd_6903684 1181636059584757512766847 := by
  unfold tailWord_6903684
  simp only [CollatzResearch.WordTrace]
  refine ⟨125899020760569699101459053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167865361014092932135278737 125899020760569699101459053)
  ·
    refine ⟨47212132785213637163047145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125899020760569699101459053 47212132785213637163047145)
    ·
      refine ⟨35409099588910227872285359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47212132785213637163047145 35409099588910227872285359)
      ·
        refine ⟨53113649383365341808428039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35409099588910227872285359 53113649383365341808428039)
        ·
          refine ⟨79670474075048012712642059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53113649383365341808428039 79670474075048012712642059)
          ·
            refine ⟨119505711112572019068963089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79670474075048012712642059 119505711112572019068963089)
            ·
              refine ⟨89629283334429014301722317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119505711112572019068963089 89629283334429014301722317)
              ·
                refine ⟨33610981250410880363145869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89629283334429014301722317 33610981250410880363145869)
                ·
                  refine ⟨12604117968904080136179701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33610981250410880363145869 12604117968904080136179701)
                  ·
                    refine ⟨1181636059584757512766847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12604117968904080136179701 1181636059584757512766847)
                    ·
                      rfl

theorem cell23_6903684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6903684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903684 prefixEnd_6903684 := by exact prefixLift 6903684
  have htrace : WordTrace (prefixWord ++ tailWord_6903684) baseStart_6903684 baseEnd_6903684 := by
    simpa [prefixWord, tailWord_6903684, baseEnd_6903684] using wordTrace_append hprefix tailTrace_6903684
  have hstable : (prefixWord ++ tailWord_6903684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903684).length < 2 ^ (prefixWord ++ tailWord_6903684).sum := by decide
  have hdescent : baseEnd_6903684 < baseStart_6903684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903691 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 2, 3, 2]
def baseStart_6903691 : Nat := 118140960795 + 6903691 * 2 ^ 59
def prefixEnd_6903691 : Nat := 4983230072969 + 3 ^ 40 * 6903691 * 2
def baseEnd_6903691 : Nat := 3544911773118854010913009

theorem tailTrace_6903691 : CollatzResearch.WordTrace tailWord_6903691 prefixEnd_6903691 3544911773118854010913009 := by
  unfold tailWord_6903691
  simp only [CollatzResearch.WordTrace]
  refine ⟨251798296832114038398422927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167865531221409358932281951 251798296832114038398422927)
  ·
    refine ⟨377697445248171057597634391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251798296832114038398422927 377697445248171057597634391)
    ·
      refine ⟨566546167872256586396451587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377697445248171057597634391 566546167872256586396451587)
      ·
        refine ⟨849819251808384879594677381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566546167872256586396451587 849819251808384879594677381)
        ·
          refine ⟨159341109714072164924002009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 849819251808384879594677381 159341109714072164924002009)
          ·
            refine ⟨119505832285554123693001507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159341109714072164924002009 119505832285554123693001507)
            ·
              refine ⟨179258748428331185539502261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119505832285554123693001507 179258748428331185539502261)
              ·
                refine ⟨16805507665156048644328337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179258748428331185539502261 16805507665156048644328337)
                ·
                  refine ⟨12604130748867036483246253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16805507665156048644328337 12604130748867036483246253)
                  ·
                    refine ⟨4726549030825138681217345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12604130748867036483246253 4726549030825138681217345)
                    ·
                      refine ⟨3544911773118854010913009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726549030825138681217345 3544911773118854010913009)
                      ·
                        rfl

theorem cell23_6903691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 3, 2].length) (baseStart_6903691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903691 prefixEnd_6903691 := by exact prefixLift 6903691
  have htrace : WordTrace (prefixWord ++ tailWord_6903691) baseStart_6903691 baseEnd_6903691 := by
    simpa [prefixWord, tailWord_6903691, baseEnd_6903691] using wordTrace_append hprefix tailTrace_6903691
  have hstable : (prefixWord ++ tailWord_6903691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903691).length < 2 ^ (prefixWord ++ tailWord_6903691).sum := by decide
  have hdescent : baseEnd_6903691 < baseStart_6903691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903702 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6903702 : Nat := 118140960795 + 6903702 * 2 ^ 59
def prefixEnd_6903702 : Nat := 4983230072969 + 3 ^ 40 * 6903702 * 2
def baseEnd_6903702 : Nat := 3544917421406053467875459

theorem tailTrace_6903702 : CollatzResearch.WordTrace tailWord_6903702 prefixEnd_6903702 3544917421406053467875459 := by
  unfold tailWord_6903702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737418627192136704817085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167865798690049458184715573 15737418627192136704817085)
  ·
    refine ⟨5901531985197051264306407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15737418627192136704817085 5901531985197051264306407)
    ·
      refine ⟨8852297977795576896459611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901531985197051264306407 8852297977795576896459611)
      ·
        refine ⟨13278446966693365344689417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852297977795576896459611 13278446966693365344689417)
        ·
          refine ⟨9958835225020024008517063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13278446966693365344689417 9958835225020024008517063)
          ·
            refine ⟨14938252837530036012775595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958835225020024008517063 14938252837530036012775595)
            ·
              refine ⟨22407379256295054019163393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938252837530036012775595 22407379256295054019163393)
              ·
                refine ⟨16805534442221290514372545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22407379256295054019163393 16805534442221290514372545)
                ·
                  refine ⟨12604150831665967885779409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16805534442221290514372545 12604150831665967885779409)
                  ·
                    refine ⟨9453113123749475914334557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12604150831665967885779409 9453113123749475914334557)
                    ·
                      refine ⟨3544917421406053467875459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453113123749475914334557 3544917421406053467875459)
                      ·
                        rfl

theorem cell23_6903702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6903702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903702 prefixEnd_6903702 := by exact prefixLift 6903702
  have htrace : WordTrace (prefixWord ++ tailWord_6903702) baseStart_6903702 baseEnd_6903702 := by
    simpa [prefixWord, tailWord_6903702, baseEnd_6903702] using wordTrace_append hprefix tailTrace_6903702
  have hstable : (prefixWord ++ tailWord_6903702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903702).length < 2 ^ (prefixWord ++ tailWord_6903702).sum := by decide
  have hdescent : baseEnd_6903702 < baseStart_6903702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903708 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6903708 : Nat := 118140960795 + 6903708 * 2 ^ 59
def prefixEnd_6903708 : Nat := 4983230072969 + 3 ^ 40 * 6903708 * 2
def baseEnd_6903708 : Nat := 3544920502289980444400431

theorem tailTrace_6903708 : CollatzResearch.WordTrace tailWord_6903708 prefixEnd_6903708 3544920502289980444400431 := by
  unfold tailWord_6903708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125899458436526225150895889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167865944582034966867861185 125899458436526225150895889)
  ·
    refine ⟨94424593827394668863171917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125899458436526225150895889 94424593827394668863171917)
    ·
      refine ⟨35409222685273000823689469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94424593827394668863171917 35409222685273000823689469)
      ·
        refine ⟨13278458506977375308883551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35409222685273000823689469 13278458506977375308883551)
        ·
          refine ⟨19917687760466062963325327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13278458506977375308883551 19917687760466062963325327)
          ·
            refine ⟨29876531640699094444987991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19917687760466062963325327 29876531640699094444987991)
            ·
              refine ⟨44814797461048641667481987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29876531640699094444987991 44814797461048641667481987)
              ·
                refine ⟨67222196191572962501222981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44814797461048641667481987 67222196191572962501222981)
                ·
                  refine ⟨12604161785919930468979309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67222196191572962501222981 12604161785919930468979309)
                  ·
                    refine ⟨4726560669719973925867241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12604161785919930468979309 4726560669719973925867241)
                    ·
                      refine ⟨3544920502289980444400431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726560669719973925867241 3544920502289980444400431)
                      ·
                        rfl

theorem cell23_6903708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6903708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903708 prefixEnd_6903708 := by exact prefixLift 6903708
  have htrace : WordTrace (prefixWord ++ tailWord_6903708) baseStart_6903708 baseEnd_6903708 := by
    simpa [prefixWord, tailWord_6903708, baseEnd_6903708] using wordTrace_append hprefix tailTrace_6903708
  have hstable : (prefixWord ++ tailWord_6903708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903708).length < 2 ^ (prefixWord ++ tailWord_6903708).sum := by decide
  have hdescent : baseEnd_6903708 < baseStart_6903708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903731 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 2, 4]
def baseStart_6903731 : Nat := 118140960795 + 6903731 * 2 ^ 59
def prefixEnd_6903731 : Nat := 4983230072969 + 3 ^ 40 * 6903731 * 2
def baseEnd_6903731 : Nat := 1181644104115011284804275

theorem tailTrace_6903731 : CollatzResearch.WordTrace tailWord_6903731 prefixEnd_6903731 1181644104115011284804275 := by
  unfold tailWord_6903731
  simp only [CollatzResearch.WordTrace]
  refine ⟨251799755751969125229879047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167866503834646083486586031 251799755751969125229879047)
  ·
    refine ⟨377699633627953687844818571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251799755751969125229879047 377699633627953687844818571)
    ·
      refine ⟨566549450441930531767227857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377699633627953687844818571 566549450441930531767227857)
      ·
        refine ⟨424912087831447898825420893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566549450441930531767227857 424912087831447898825420893)
        ·
          refine ⟨159342032936792962059532835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424912087831447898825420893 159342032936792962059532835)
          ·
            refine ⟨239013049405189443089299253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159342032936792962059532835 239013049405189443089299253)
            ·
              refine ⟨22407473381736510289621805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239013049405189443089299253 22407473381736510289621805)
              ·
                refine ⟨8402802518151191358608177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22407473381736510289621805 8402802518151191358608177)
                ·
                  refine ⟨6302101888613393518956133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402802518151191358608177 6302101888613393518956133)
                  ·
                    refine ⟨1181644104115011284804275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302101888613393518956133 1181644104115011284804275)
                    ·
                      rfl

theorem cell23_6903731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 4].length) (baseStart_6903731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903731 prefixEnd_6903731 := by exact prefixLift 6903731
  have htrace : WordTrace (prefixWord ++ tailWord_6903731) baseStart_6903731 baseEnd_6903731 := by
    simpa [prefixWord, tailWord_6903731, baseEnd_6903731] using wordTrace_append hprefix tailTrace_6903731
  have hstable : (prefixWord ++ tailWord_6903731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903731).length < 2 ^ (prefixWord ++ tailWord_6903731).sum := by decide
  have hdescent : baseEnd_6903731 < baseStart_6903731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903755 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 1, 2, 2]
def baseStart_6903755 : Nat := 118140960795 + 6903755 * 2 ^ 59
def prefixEnd_6903755 : Nat := 4983230072969 + 3 ^ 40 * 6903755 * 2
def baseEnd_6903755 : Nat := 3544944635880741760512715

theorem tailTrace_6903755 : CollatzResearch.WordTrace tailWord_6903755 prefixEnd_6903755 3544944635880741760512715 := by
  unfold tailWord_6903755
  simp only [CollatzResearch.WordTrace]
  refine ⟨251800631103882177328752719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167867087402588118219168479 251800631103882177328752719)
  ·
    refine ⟨377700946655823265993129079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251800631103882177328752719 377700946655823265993129079)
    ·
      refine ⟨566551419983734898989693619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377700946655823265993129079 566551419983734898989693619)
      ·
        refine ⟨849827129975602348484540429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566551419983734898989693619 849827129975602348484540429)
        ·
          refine ⟨318685173740850880681702661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849827129975602348484540429 318685173740850880681702661)
          ·
            refine ⟨59753470076409540127819249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318685173740850880681702661 59753470076409540127819249)
            ·
              refine ⟨44815102557307155095864437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59753470076409540127819249 44815102557307155095864437)
              ·
                refine ⟨4201415864747545790237291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44815102557307155095864437 4201415864747545790237291)
                ·
                  refine ⟨6302123797121318685355937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201415864747545790237291 6302123797121318685355937)
                  ·
                    refine ⟨4726592847840989014016953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302123797121318685355937 4726592847840989014016953)
                    ·
                      refine ⟨3544944635880741760512715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726592847840989014016953 3544944635880741760512715)
                      ·
                        rfl

theorem cell23_6903755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 2, 2].length) (baseStart_6903755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903755 prefixEnd_6903755 := by exact prefixLift 6903755
  have htrace : WordTrace (prefixWord ++ tailWord_6903755) baseStart_6903755 baseEnd_6903755 := by
    simpa [prefixWord, tailWord_6903755, baseEnd_6903755] using wordTrace_append hprefix tailTrace_6903755
  have hstable : (prefixWord ++ tailWord_6903755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903755).length < 2 ^ (prefixWord ++ tailWord_6903755).sum := by decide
  have hdescent : baseEnd_6903755 < baseStart_6903755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903766 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6903766 : Nat := 118140960795 + 6903766 * 2 ^ 59
def prefixEnd_6903766 : Nat := 4983230072969 + 3 ^ 40 * 6903766 * 2
def baseEnd_6903766 : Nat := 3544950284167941217475165

theorem tailTrace_6903766 : CollatzResearch.WordTrace tailWord_6903766 prefixEnd_6903766 3544950284167941217475165 := by
  unfold tailWord_6903766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737564519177645387962697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167867354871228217471602101 15737564519177645387962697)
  ·
    refine ⟨11803173389383234040972023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15737564519177645387962697 11803173389383234040972023)
    ·
      refine ⟨17704760084074851061458035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11803173389383234040972023 17704760084074851061458035)
      ·
        refine ⟨26557140126112276592187053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704760084074851061458035 26557140126112276592187053)
        ·
          refine ⟨9958927547292103722070145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26557140126112276592187053 9958927547292103722070145)
          ·
            refine ⟨7469195660469077791552609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958927547292103722070145 7469195660469077791552609)
            ·
              refine ⟨5601896745351808343664457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469195660469077791552609 5601896745351808343664457)
              ·
                refine ⟨4201422559013856257748343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5601896745351808343664457 4201422559013856257748343)
                ·
                  refine ⟨6302133838520784386622515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201422559013856257748343 6302133838520784386622515)
                  ·
                    refine ⟨9453200757781176579933773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6302133838520784386622515 9453200757781176579933773)
                    ·
                      refine ⟨3544950284167941217475165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453200757781176579933773 3544950284167941217475165)
                      ·
                        rfl

theorem cell23_6903766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6903766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903766 prefixEnd_6903766 := by exact prefixLift 6903766
  have htrace : WordTrace (prefixWord ++ tailWord_6903766) baseStart_6903766 baseEnd_6903766 := by
    simpa [prefixWord, tailWord_6903766, baseEnd_6903766] using wordTrace_append hprefix tailTrace_6903766
  have hstable : (prefixWord ++ tailWord_6903766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903766).length < 2 ^ (prefixWord ++ tailWord_6903766).sum := by decide
  have hdescent : baseEnd_6903766 < baseStart_6903766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903784 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6903784 : Nat := 118140960795 + 6903784 * 2 ^ 59
def prefixEnd_6903784 : Nat := 4983230072969 + 3 ^ 40 * 6903784 * 2
def baseEnd_6903784 : Nat := 3544959526819722147050081

theorem tailTrace_6903784 : CollatzResearch.WordTrace tailWord_6903784 prefixEnd_6903784 3544959526819722147050081 := by
  unfold tailWord_6903784
  simp only [CollatzResearch.WordTrace]
  refine ⟨125900844410388557640779203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167867792547184743521038937 125900844410388557640779203)
  ·
    refine ⟨188851266615582836461168805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125900844410388557640779203 188851266615582836461168805)
    ·
      refine ⟨35409612490421781836469151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188851266615582836461168805 35409612490421781836469151)
      ·
        refine ⟨53114418735632672754703727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35409612490421781836469151 53114418735632672754703727)
        ·
          refine ⟨79671628103449009132055591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53114418735632672754703727 79671628103449009132055591)
          ·
            refine ⟨119507442155173513698083387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79671628103449009132055591 119507442155173513698083387)
            ·
              refine ⟨179261163232760270547125081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119507442155173513698083387 179261163232760270547125081)
              ·
                refine ⟨134445872424570202910343811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179261163232760270547125081 134445872424570202910343811)
                ·
                  refine ⟨201668808636855304365515717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134445872424570202910343811 201668808636855304365515717)
                  ·
                    refine ⟨37812901619410369568534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201668808636855304365515717 37812901619410369568534197)
                    ·
                      refine ⟨3544959526819722147050081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37812901619410369568534197 3544959526819722147050081)
                      ·
                        rfl

theorem cell23_6903784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6903784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903784 prefixEnd_6903784 := by exact prefixLift 6903784
  have htrace : WordTrace (prefixWord ++ tailWord_6903784) baseStart_6903784 baseEnd_6903784 := by
    simpa [prefixWord, tailWord_6903784, baseEnd_6903784] using wordTrace_append hprefix tailTrace_6903784
  have hstable : (prefixWord ++ tailWord_6903784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903784).length < 2 ^ (prefixWord ++ tailWord_6903784).sum := by decide
  have hdescent : baseEnd_6903784 < baseStart_6903784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903804 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6903804 : Nat := 118140960795 + 6903804 * 2 ^ 59
def prefixEnd_6903804 : Nat := 4983230072969 + 3 ^ 40 * 6903804 * 2
def baseEnd_6903804 : Nat := 1181656598810937356266663

theorem tailTrace_6903804 : CollatzResearch.WordTrace tailWord_6903804 prefixEnd_6903804 1181656598810937356266663 := by
  unfold tailWord_6903804
  simp only [CollatzResearch.WordTrace]
  refine ⟨125901209140352329348643233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167868278853803105798190977 125901209140352329348643233)
  ·
    refine ⟨94425906855264247011482425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125901209140352329348643233 94425906855264247011482425)
    ·
      refine ⟨70819430141448185258611819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94425906855264247011482425 70819430141448185258611819)
      ·
        refine ⟨106229145212172277887917729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70819430141448185258611819 106229145212172277887917729)
        ·
          refine ⟨79671858909129208415938297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106229145212172277887917729 79671858909129208415938297)
          ·
            refine ⟨59753894181846906311953723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79671858909129208415938297 59753894181846906311953723)
            ·
              refine ⟨89630841272770359467930585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59753894181846906311953723 89630841272770359467930585)
              ·
                refine ⟨67223130954577769600947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89630841272770359467930585 67223130954577769600947939)
                ·
                  refine ⟨100834696431866654401421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67223130954577769600947939 100834696431866654401421909)
                  ·
                    refine ⟨1181656598810937356266663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100834696431866654401421909 1181656598810937356266663)
                    ·
                      rfl

theorem cell23_6903804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6903804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903804 prefixEnd_6903804 := by exact prefixLift 6903804
  have htrace : WordTrace (prefixWord ++ tailWord_6903804) baseStart_6903804 baseEnd_6903804 := by
    simpa [prefixWord, tailWord_6903804, baseEnd_6903804] using wordTrace_append hprefix tailTrace_6903804
  have hstable : (prefixWord ++ tailWord_6903804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903804).length < 2 ^ (prefixWord ++ tailWord_6903804).sum := by decide
  have hdescent : baseEnd_6903804 < baseStart_6903804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903815 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6903815 : Nat := 118140960795 + 6903815 * 2 ^ 59
def prefixEnd_6903815 : Nat := 4983230072969 + 3 ^ 40 * 6903815 * 2
def baseEnd_6903815 : Nat := 3544975444720011525762439

theorem tailTrace_6903815 : CollatzResearch.WordTrace tailWord_6903815 prefixEnd_6903815 3544975444720011525762439 := by
  unfold tailWord_6903815
  simp only [CollatzResearch.WordTrace]
  refine ⟨251802819483664807575936899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167868546322443205050624599 251802819483664807575936899)
  ·
    refine ⟨377704229225497211363905349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251802819483664807575936899 377704229225497211363905349)
    ·
      refine ⟨70819542979780727130732253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377704229225497211363905349 70819542979780727130732253)
      ·
        refine ⟨26557328617417772674024595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70819542979780727130732253 26557328617417772674024595)
        ·
          refine ⟨39835992926126659011036893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26557328617417772674024595 39835992926126659011036893)
          ·
            refine ⟨14938497347297497129138835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39835992926126659011036893 14938497347297497129138835)
            ·
              refine ⟨22407746020946245693708253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938497347297497129138835 22407746020946245693708253)
              ·
                refine ⟨8402904757854842135140595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22407746020946245693708253 8402904757854842135140595)
                ·
                  refine ⟨12604357136782263202710893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8402904757854842135140595 12604357136782263202710893)
                  ·
                    refine ⟨4726633926293348701016585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12604357136782263202710893 4726633926293348701016585)
                    ·
                      refine ⟨3544975444720011525762439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726633926293348701016585 3544975444720011525762439)
                      ·
                        rfl

theorem cell23_6903815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6903815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903815 prefixEnd_6903815 := by exact prefixLift 6903815
  have htrace : WordTrace (prefixWord ++ tailWord_6903815) baseStart_6903815 baseEnd_6903815 := by
    simpa [prefixWord, tailWord_6903815, baseEnd_6903815] using wordTrace_append hprefix tailTrace_6903815
  have hstable : (prefixWord ++ tailWord_6903815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903815).length < 2 ^ (prefixWord ++ tailWord_6903815).sum := by decide
  have hdescent : baseEnd_6903815 < baseStart_6903815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903824 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_6903824 : Nat := 118140960795 + 6903824 * 2 ^ 59
def prefixEnd_6903824 : Nat := 4983230072969 + 3 ^ 40 * 6903824 * 2
def baseEnd_6903824 : Nat := 3544980066045901990549897

theorem tailTrace_6903824 : CollatzResearch.WordTrace tailWord_6903824 prefixEnd_6903824 3544980066045901990549897 := by
  unfold tailWord_6903824
  simp only [CollatzResearch.WordTrace]
  refine ⟨125901573870316101056507263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167868765160421468075343017 125901573870316101056507263)
  ·
    refine ⟨188852360805474151584760895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125901573870316101056507263 188852360805474151584760895)
    ·
      refine ⟨283278541208211227377141343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188852360805474151584760895 283278541208211227377141343)
      ·
        refine ⟨424917811812316841065712015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283278541208211227377141343 424917811812316841065712015)
        ·
          refine ⟨637376717718475261598568023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424917811812316841065712015 637376717718475261598568023)
          ·
            refine ⟨956065076577712892397852035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637376717718475261598568023 956065076577712892397852035)
            ·
              refine ⟨1434097614866569338596778053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956065076577712892397852035 1434097614866569338596778053)
              ·
                refine ⟨268893302787481750986895885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1434097614866569338596778053 268893302787481750986895885)
                ·
                  refine ⟨100834988545305656620085957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268893302787481750986895885 100834988545305656620085957)
                  ·
                    refine ⟨18906560352244810616266117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100834988545305656620085957 18906560352244810616266117)
                    ·
                      refine ⟨3544980066045901990549897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18906560352244810616266117 3544980066045901990549897)
                      ·
                        rfl

theorem cell23_6903824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_6903824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903824 prefixEnd_6903824 := by exact prefixLift 6903824
  have htrace : WordTrace (prefixWord ++ tailWord_6903824) baseStart_6903824 baseEnd_6903824 := by
    simpa [prefixWord, tailWord_6903824, baseEnd_6903824] using wordTrace_append hprefix tailTrace_6903824
  have hstable : (prefixWord ++ tailWord_6903824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903824).length < 2 ^ (prefixWord ++ tailWord_6903824).sum := by decide
  have hdescent : baseEnd_6903824 < baseStart_6903824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903845 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_6903845 : Nat := 118140960795 + 6903845 * 2 ^ 59
def prefixEnd_6903845 : Nat := 4983230072969 + 3 ^ 40 * 6903845 * 2
def baseEnd_6903845 : Nat := 3544990849139646408387301

theorem tailTrace_6903845 : CollatzResearch.WordTrace tailWord_6903845 prefixEnd_6903845 3544990849139646408387301 := by
  unfold tailWord_6903845
  simp only [CollatzResearch.WordTrace]
  refine ⟨251803913673556122699528989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167869275782370748466352659 251803913673556122699528989)
  ·
    refine ⟨94426467627583546012323371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251803913673556122699528989 94426467627583546012323371)
    ·
      refine ⟨141639701441375319018485057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94426467627583546012323371 141639701441375319018485057)
      ·
        refine ⟨106229776081031489263863793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141639701441375319018485057 106229776081031489263863793)
        ·
          refine ⟨79672332060773616947897845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106229776081031489263863793 79672332060773616947897845)
          ·
            refine ⟨7469281130697526588865423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79672332060773616947897845 7469281130697526588865423)
            ·
              refine ⟨11203921696046289883298135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469281130697526588865423 11203921696046289883298135)
              ·
                refine ⟨16805882544069434824947203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11203921696046289883298135 16805882544069434824947203)
                ·
                  refine ⟨25208823816104152237420805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16805882544069434824947203 25208823816104152237420805)
                  ·
                    refine ⟨4726654465519528544516401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25208823816104152237420805 4726654465519528544516401)
                    ·
                      refine ⟨3544990849139646408387301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726654465519528544516401 3544990849139646408387301)
                      ·
                        rfl

theorem cell23_6903845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_6903845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903845 prefixEnd_6903845 := by exact prefixLift 6903845
  have htrace : WordTrace (prefixWord ++ tailWord_6903845) baseStart_6903845 baseEnd_6903845 := by
    simpa [prefixWord, tailWord_6903845, baseEnd_6903845] using wordTrace_append hprefix tailTrace_6903845
  have hstable : (prefixWord ++ tailWord_6903845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903845).length < 2 ^ (prefixWord ++ tailWord_6903845).sum := by decide
  have hdescent : baseEnd_6903845 < baseStart_6903845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903861 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_6903861 : Nat := 118140960795 + 6903861 * 2 ^ 59
def prefixEnd_6903861 : Nat := 4983230072969 + 3 ^ 40 * 6903861 * 2
def baseEnd_6903861 : Nat := 3544999064830118345787227

theorem tailTrace_6903861 : CollatzResearch.WordTrace tailWord_6903861 prefixEnd_6903861 3544999064830118345787227 := by
  unfold tailWord_6903861
  simp only [CollatzResearch.WordTrace]
  refine ⟨251804497241498157432111437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167869664827665438288074291 251804497241498157432111437)
  ·
    refine ⟨94426686465561809037041789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251804497241498157432111437 94426686465561809037041789)
    ·
      refine ⟨35410007424585678388890671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94426686465561809037041789 35410007424585678388890671)
      ·
        refine ⟨53115011136878517583336007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35410007424585678388890671 53115011136878517583336007)
        ·
          refine ⟨79672516705317776375004011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53115011136878517583336007 79672516705317776375004011)
          ·
            refine ⟨119508775057976664562506017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79672516705317776375004011 119508775057976664562506017)
            ·
              refine ⟨89631581293482498421879513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119508775057976664562506017 89631581293482498421879513)
              ·
                refine ⟨67223685970111873816409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89631581293482498421879513 67223685970111873816409635)
                ·
                  refine ⟨100835528955167810724614453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67223685970111873816409635 100835528955167810724614453)
                  ·
                    refine ⟨9453330839546982255432605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100835528955167810724614453 9453330839546982255432605)
                    ·
                      refine ⟨3544999064830118345787227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453330839546982255432605 3544999064830118345787227)
                      ·
                        rfl

theorem cell23_6903861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_6903861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903861 prefixEnd_6903861 := by exact prefixLift 6903861
  have htrace : WordTrace (prefixWord ++ tailWord_6903861) baseStart_6903861 baseEnd_6903861 := by
    simpa [prefixWord, tailWord_6903861, baseEnd_6903861] using wordTrace_append hprefix tailTrace_6903861
  have hstable : (prefixWord ++ tailWord_6903861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903861).length < 2 ^ (prefixWord ++ tailWord_6903861).sum := by decide
  have hdescent : baseEnd_6903861 < baseStart_6903861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903878 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6903878 : Nat := 118140960795 + 6903878 * 2 ^ 59
def prefixEnd_6903878 : Nat := 4983230072969 + 3 ^ 40 * 6903878 * 2
def baseEnd_6903878 : Nat := 3545007794001244779274649

theorem tailTrace_6903878 : CollatzResearch.WordTrace tailWord_6903878 prefixEnd_6903878 3545007794001244779274649 := by
  unfold tailWord_6903878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868909915076142791733759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167870078188291046223653525 7868909915076142791733759)
  ·
    refine ⟨11803364872614214187600639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7868909915076142791733759 11803364872614214187600639)
    ·
      refine ⟨17705047308921321281400959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11803364872614214187600639 17705047308921321281400959)
      ·
        refine ⟨26557570963381981922101439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17705047308921321281400959 26557570963381981922101439)
        ·
          refine ⟨39836356445072972883152159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26557570963381981922101439 39836356445072972883152159)
          ·
            refine ⟨59754534667609459324728239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39836356445072972883152159 59754534667609459324728239)
            ·
              refine ⟨89631802001414188987092359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59754534667609459324728239 89631802001414188987092359)
              ·
                refine ⟨134447703002121283480638539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89631802001414188987092359 134447703002121283480638539)
                ·
                  refine ⟨201671554503181925220957809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134447703002121283480638539 201671554503181925220957809)
                  ·
                    refine ⟨151253665877386443915718357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201671554503181925220957809 151253665877386443915718357)
                    ·
                      refine ⟨3545007794001244779274649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151253665877386443915718357 3545007794001244779274649)
                      ·
                        rfl

theorem cell23_6903878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6903878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903878 prefixEnd_6903878 := by exact prefixLift 6903878
  have htrace : WordTrace (prefixWord ++ tailWord_6903878) baseStart_6903878 baseEnd_6903878 := by
    simpa [prefixWord, tailWord_6903878, baseEnd_6903878] using wordTrace_append hprefix tailTrace_6903878
  have hstable : (prefixWord ++ tailWord_6903878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903878).length < 2 ^ (prefixWord ++ tailWord_6903878).sum := by decide
  have hdescent : baseEnd_6903878 < baseStart_6903878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903881 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_6903881 : Nat := 118140960795 + 6903881 * 2 ^ 59
def prefixEnd_6903881 : Nat := 4983230072969 + 3 ^ 40 * 6903881 * 2
def baseEnd_6903881 : Nat := 1181669778147736089179045

theorem tailTrace_6903881 : CollatzResearch.WordTrace tailWord_6903881 prefixEnd_6903881 1181669778147736089179045 := by
  unfold tailWord_6903881
  simp only [CollatzResearch.WordTrace]
  refine ⟨251805226701425700847839497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167870151134283800565226331 251805226701425700847839497)
  ·
    refine ⟨188853920026069275635879623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251805226701425700847839497 188853920026069275635879623)
    ·
      refine ⟨283280880039103913453819435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188853920026069275635879623 283280880039103913453819435)
      ·
        refine ⟨424921320058655870180729153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283280880039103913453819435 424921320058655870180729153)
        ·
          refine ⟨318690990043991902635546865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424921320058655870180729153 318690990043991902635546865)
          ·
            refine ⟨239018242532993926976660149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318690990043991902635546865 239018242532993926976660149)
            ·
              refine ⟨22407960237468180654061889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239018242532993926976660149 22407960237468180654061889)
              ·
                refine ⟨16805970178101135490546417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22407960237468180654061889 16805970178101135490546417)
                ·
                  refine ⟨12604477633575851617909813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16805970178101135490546417 12604477633575851617909813)
                  ·
                    refine ⟨1181669778147736089179045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12604477633575851617909813 1181669778147736089179045)
                    ·
                      rfl

theorem cell23_6903881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_6903881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903881 prefixEnd_6903881 := by exact prefixLift 6903881
  have htrace : WordTrace (prefixWord ++ tailWord_6903881) baseStart_6903881 baseEnd_6903881 := by
    simpa [prefixWord, tailWord_6903881, baseEnd_6903881] using wordTrace_append hprefix tailTrace_6903881
  have hstable : (prefixWord ++ tailWord_6903881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903881).length < 2 ^ (prefixWord ++ tailWord_6903881).sum := by decide
  have hdescent : baseEnd_6903881 < baseStart_6903881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903945 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 1, 4]
def baseStart_6903945 : Nat := 118140960795 + 6903945 * 2 ^ 59
def prefixEnd_6903945 : Nat := 4983230072969 + 3 ^ 40 * 6903945 * 2
def baseEnd_6903945 : Nat := 1181680732401698672378947

theorem tailTrace_6903945 : CollatzResearch.WordTrace tailWord_6903945 prefixEnd_6903945 1181680732401698672378947 := by
  unfold tailWord_6903945
  simp only [CollatzResearch.WordTrace]
  refine ⟨251807560973193839778169289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167871707315462559852112859 251807560973193839778169289)
  ·
    refine ⟨188855670729895379833626967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251807560973193839778169289 188855670729895379833626967)
    ·
      refine ⟨283283506094843069750440451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188855670729895379833626967 283283506094843069750440451)
      ·
        refine ⟨424925259142264604625660677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283283506094843069750440451 424925259142264604625660677)
        ·
          refine ⟨79673486089174613367311377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424925259142264604625660677 79673486089174613367311377)
          ·
            refine ⟨59755114566880960025483533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79673486089174613367311377 59755114566880960025483533)
            ·
              refine ⟨22408167962580360009556325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59755114566880960025483533 22408167962580360009556325)
              ·
                refine ⟨4201531492983817501791811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22408167962580360009556325 4201531492983817501791811)
                ·
                  refine ⟨6302297239475726252687717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201531492983817501791811 6302297239475726252687717)
                  ·
                    refine ⟨1181680732401698672378947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302297239475726252687717 1181680732401698672378947)
                    ·
                      rfl

theorem cell23_6903945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_6903945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903945 prefixEnd_6903945 := by exact prefixLift 6903945
  have htrace : WordTrace (prefixWord ++ tailWord_6903945) baseStart_6903945 baseEnd_6903945 := by
    simpa [prefixWord, tailWord_6903945, baseEnd_6903945] using wordTrace_append hprefix tailTrace_6903945
  have hstable : (prefixWord ++ tailWord_6903945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903945).length < 2 ^ (prefixWord ++ tailWord_6903945).sum := by decide
  have hdescent : baseEnd_6903945 < baseStart_6903945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6903972 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_6903972 : Nat := 118140960795 + 6903972 * 2 ^ 59
def prefixEnd_6903972 : Nat := 4983230072969 + 3 ^ 40 * 6903972 * 2
def baseEnd_6903972 : Nat := 3545056061182767411499217

theorem tailTrace_6903972 : CollatzResearch.WordTrace tailWord_6903972 prefixEnd_6903972 3545056061182767411499217 := by
  unfold tailWord_6903972
  simp only [CollatzResearch.WordTrace]
  refine ⟨125904272872048011694701085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167872363829397348926268113 125904272872048011694701085)
  ·
    refine ⟨47214102327018004385512907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125904272872048011694701085 47214102327018004385512907)
    ·
      refine ⟨70821153490527006578269361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47214102327018004385512907 70821153490527006578269361)
      ·
        refine ⟨53115865117895254933702021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70821153490527006578269361 53115865117895254933702021)
        ·
          refine ⟨9959224709605360300069129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53115865117895254933702021 9959224709605360300069129)
          ·
            refine ⟨7469418532204020225051847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959224709605360300069129 7469418532204020225051847)
            ·
              refine ⟨11204127798306030337577771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469418532204020225051847 11204127798306030337577771)
              ·
                refine ⟨16806191697459045506366657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204127798306030337577771 16806191697459045506366657)
                ·
                  refine ⟨12604643773094284129774993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16806191697459045506366657 12604643773094284129774993)
                  ·
                    refine ⟨9453482829820713097331245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12604643773094284129774993 9453482829820713097331245)
                    ·
                      refine ⟨3545056061182767411499217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453482829820713097331245 3545056061182767411499217)
                      ·
                        rfl

theorem cell23_6903972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_6903972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6903972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6903972 prefixEnd_6903972 := by exact prefixLift 6903972
  have htrace : WordTrace (prefixWord ++ tailWord_6903972) baseStart_6903972 baseEnd_6903972 := by
    simpa [prefixWord, tailWord_6903972, baseEnd_6903972] using wordTrace_append hprefix tailTrace_6903972
  have hstable : (prefixWord ++ tailWord_6903972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6903972).length < 2 ^ (prefixWord ++ tailWord_6903972).sum := by decide
  have hdescent : baseEnd_6903972 < baseStart_6903972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6903972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904022 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6904022 : Nat := 118140960795 + 6904022 * 2 ^ 59
def prefixEnd_6904022 : Nat := 4983230072969 + 3 ^ 40 * 6904022 * 2
def baseEnd_6904022 : Nat := 1181693911738497405291329

theorem tailTrace_6904022 : CollatzResearch.WordTrace tailWord_6904022 prefixEnd_6904022 1181693911738497405291329 := by
  unfold tailWord_6904022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15738148087119680120545145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167873579595943254619148213 15738148087119680120545145)
  ·
    refine ⟨11803611065339760090408859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15738148087119680120545145 11803611065339760090408859)
    ·
      refine ⟨17705416598009640135613289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11803611065339760090408859 17705416598009640135613289)
      ·
        refine ⟨13279062448507230101709967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17705416598009640135613289 13279062448507230101709967)
        ·
          refine ⟨19918593672760845152564951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13279062448507230101709967 19918593672760845152564951)
          ·
            refine ⟨29877890509141267728847427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19918593672760845152564951 29877890509141267728847427)
            ·
              refine ⟨44816835763711901593271141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29877890509141267728847427 44816835763711901593271141)
              ·
                refine ⟨8403156705695981548738339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44816835763711901593271141 8403156705695981548738339)
                ·
                  refine ⟨12604735058543972323107509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8403156705695981548738339 12604735058543972323107509)
                  ·
                    refine ⟨1181693911738497405291329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12604735058543972323107509 1181693911738497405291329)
                    ·
                      rfl

theorem cell23_6904022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6904022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904022 prefixEnd_6904022 := by exact prefixLift 6904022
  have htrace : WordTrace (prefixWord ++ tailWord_6904022) baseStart_6904022 baseEnd_6904022 := by
    simpa [prefixWord, tailWord_6904022, baseEnd_6904022] using wordTrace_append hprefix tailTrace_6904022
  have hstable : (prefixWord ++ tailWord_6904022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904022).length < 2 ^ (prefixWord ++ tailWord_6904022).sum := by decide
  have hdescent : baseEnd_6904022 < baseStart_6904022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904115 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 4, 2]
def baseStart_6904115 : Nat := 118140960795 + 6904115 * 2 ^ 59
def prefixEnd_6904115 : Nat := 4983230072969 + 3 ^ 40 * 6904115 * 2
def baseEnd_6904115 : Nat := 3545129488916360352011059

theorem tailTrace_6904115 : CollatzResearch.WordTrace tailWord_6904115 prefixEnd_6904115 3545129488916360352011059 := by
  unfold tailWord_6904115
  simp only [CollatzResearch.WordTrace]
  refine ⟨251813761382577958811857799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167875840921718639207905199 251813761382577958811857799)
  ·
    refine ⟨377720642073866938217786699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251813761382577958811857799 377720642073866938217786699)
    ·
      refine ⟨566580963110800407326680049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377720642073866938217786699 566580963110800407326680049)
      ·
        refine ⟨424935722333100305495010037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566580963110800407326680049 424935722333100305495010037)
        ·
          refine ⟨39837723968728153640157191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 424935722333100305495010037 39837723968728153640157191)
          ·
            refine ⟨59756585953092230460235787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39837723968728153640157191 59756585953092230460235787)
            ·
              refine ⟨89634878929638345690353681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59756585953092230460235787 89634878929638345690353681)
              ·
                refine ⟨67226159197228759267765261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89634878929638345690353681 67226159197228759267765261)
                ·
                  refine ⟨25209809698960784725411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67226159197228759267765261 25209809698960784725411973)
                  ·
                    refine ⟨4726839318555147136014745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25209809698960784725411973 4726839318555147136014745)
                    ·
                      refine ⟨3545129488916360352011059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726839318555147136014745 3545129488916360352011059)
                      ·
                        rfl

theorem cell23_6904115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4, 2].length) (baseStart_6904115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904115 prefixEnd_6904115 := by exact prefixLift 6904115
  have htrace : WordTrace (prefixWord ++ tailWord_6904115) baseStart_6904115 baseEnd_6904115 := by
    simpa [prefixWord, tailWord_6904115, baseEnd_6904115] using wordTrace_append hprefix tailTrace_6904115
  have hstable : (prefixWord ++ tailWord_6904115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904115).length < 2 ^ (prefixWord ++ tailWord_6904115).sum := by decide
  have hdescent : baseEnd_6904115 < baseStart_6904115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904165 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_6904165 : Nat := 118140960795 + 6904165 * 2 ^ 59
def prefixEnd_6904165 : Nat := 4983230072969 + 3 ^ 40 * 6904165 * 2
def baseEnd_6904165 : Nat := 3545155162949085156385829

theorem tailTrace_6904165 : CollatzResearch.WordTrace tailWord_6904165 prefixEnd_6904165 3545155162949085156385829 := by
  unfold tailWord_6904165
  simp only [CollatzResearch.WordTrace]
  refine ⟨251815585032396817351177949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167877056688264544900785299 251815585032396817351177949)
  ·
    refine ⟨94430844387148806506691731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251815585032396817351177949 94430844387148806506691731)
    ·
      refine ⟨141646266580723209760037597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94430844387148806506691731 141646266580723209760037597)
      ·
        refine ⟨53117349967771203660014099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141646266580723209760037597 53117349967771203660014099)
        ·
          refine ⟨79676024951656805490021149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53117349967771203660014099 79676024951656805490021149)
          ·
            refine ⟨29878509356871302058757931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79676024951656805490021149 29878509356871302058757931)
            ·
              refine ⟨44817764035306953088136897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29878509356871302058757931 44817764035306953088136897)
              ·
                refine ⟨33613323026480214816102673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44817764035306953088136897 33613323026480214816102673)
                ·
                  refine ⟨25209992269860161112077005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33613323026480214816102673 25209992269860161112077005)
                  ·
                    refine ⟨9453747101197560417028877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25209992269860161112077005 9453747101197560417028877)
                    ·
                      refine ⟨3545155162949085156385829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453747101197560417028877 3545155162949085156385829)
                      ·
                        rfl

theorem cell23_6904165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_6904165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904165 prefixEnd_6904165 := by exact prefixLift 6904165
  have htrace : WordTrace (prefixWord ++ tailWord_6904165) baseStart_6904165 baseEnd_6904165 := by
    simpa [prefixWord, tailWord_6904165, baseEnd_6904165] using wordTrace_append hprefix tailTrace_6904165
  have hstable : (prefixWord ++ tailWord_6904165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904165).length < 2 ^ (prefixWord ++ tailWord_6904165).sum := by decide
  have hdescent : baseEnd_6904165 < baseStart_6904165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904175 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 5, 2]
def baseStart_6904175 : Nat := 118140960795 + 6904175 * 2 ^ 59
def prefixEnd_6904175 : Nat := 4983230072969 + 3 ^ 40 * 6904175 * 2
def baseEnd_6904175 : Nat := 3545160297755630117260783

theorem tailTrace_6904175 : CollatzResearch.WordTrace tailWord_6904175 prefixEnd_6904175 3545160297755630117260783 := by
  unfold tailWord_6904175
  simp only [CollatzResearch.WordTrace]
  refine ⟨251815949762360589059041979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167877299841573726039361319 251815949762360589059041979)
  ·
    refine ⟨377723924643540883588562969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251815949762360589059041979 377723924643540883588562969)
    ·
      refine ⟨283292943482655662691422227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377723924643540883588562969 283292943482655662691422227)
      ·
        refine ⟨424939415223983494037133341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283292943482655662691422227 424939415223983494037133341)
        ·
          refine ⟨159352280708993810263925003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424939415223983494037133341 159352280708993810263925003)
          ·
            refine ⟨239028421063490715395887505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159352280708993810263925003 239028421063490715395887505)
            ·
              refine ⟨179271315797618036546915629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239028421063490715395887505 179271315797618036546915629)
              ·
                refine ⟨67226743424106763705093361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179271315797618036546915629 67226743424106763705093361)
                ·
                  refine ⟨50420057568080072778820021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67226743424106763705093361 50420057568080072778820021)
                  ·
                    refine ⟨4726880397007506823014377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50420057568080072778820021 4726880397007506823014377)
                    ·
                      refine ⟨3545160297755630117260783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726880397007506823014377 3545160297755630117260783)
                      ·
                        rfl

theorem cell23_6904175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5, 2].length) (baseStart_6904175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904175 prefixEnd_6904175 := by exact prefixLift 6904175
  have htrace : WordTrace (prefixWord ++ tailWord_6904175) baseStart_6904175 baseEnd_6904175 := by
    simpa [prefixWord, tailWord_6904175, baseEnd_6904175] using wordTrace_append hprefix tailTrace_6904175
  have hstable : (prefixWord ++ tailWord_6904175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904175).length < 2 ^ (prefixWord ++ tailWord_6904175).sum := by decide
  have hdescent : baseEnd_6904175 < baseStart_6904175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904215 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 5, 4]
def baseStart_6904215 : Nat := 118140960795 + 6904215 * 2 ^ 59
def prefixEnd_6904215 : Nat := 4983230072969 + 3 ^ 40 * 6904215 * 2
def baseEnd_6904215 : Nat := 1181726945660603320253533

theorem tailTrace_6904215 : CollatzResearch.WordTrace tailWord_6904215 prefixEnd_6904215 1181726945660603320253533 := by
  unfold tailWord_6904215
  simp only [CollatzResearch.WordTrace]
  refine ⟨251817408682215675890498099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167878272454810450593665399 251817408682215675890498099)
  ·
    refine ⟨377726113023323513835747149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251817408682215675890498099 377726113023323513835747149)
    ·
      refine ⟨141647292383746317688405181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377726113023323513835747149 141647292383746317688405181)
      ·
        refine ⟨53117734643904869133151943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141647292383746317688405181 53117734643904869133151943)
        ·
          refine ⟨79676601965857303699727915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53117734643904869133151943 79676601965857303699727915)
          ·
            refine ⟨119514902948785955549591873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79676601965857303699727915 119514902948785955549591873)
            ·
              refine ⟨89636177211589466662193905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119514902948785955549591873 89636177211589466662193905)
              ·
                refine ⟨67227132908692099996645429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89636177211589466662193905 67227132908692099996645429)
                ·
                  refine ⟨6302543710189884374685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67227132908692099996645429 6302543710189884374685509)
                  ·
                    refine ⟨1181726945660603320253533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302543710189884374685509 1181726945660603320253533)
                    ·
                      rfl

theorem cell23_6904215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_6904215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904215 prefixEnd_6904215 := by exact prefixLift 6904215
  have htrace : WordTrace (prefixWord ++ tailWord_6904215) baseStart_6904215 baseEnd_6904215 := by
    simpa [prefixWord, tailWord_6904215, baseEnd_6904215] using wordTrace_append hprefix tailTrace_6904215
  have hstable : (prefixWord ++ tailWord_6904215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904215).length < 2 ^ (prefixWord ++ tailWord_6904215).sum := by decide
  have hdescent : baseEnd_6904215 < baseStart_6904215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904234 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6904234 : Nat := 118140960795 + 6904234 * 2 ^ 59
def prefixEnd_6904234 : Nat := 4983230072969 + 3 ^ 40 * 6904234 * 2
def baseEnd_6904234 : Nat := 3545190593114245386423013

theorem tailTrace_6904234 : CollatzResearch.WordTrace tailWord_6904234 prefixEnd_6904234 3545190593114245386423013 := by
  unfold tailWord_6904234
  simp only [CollatzResearch.WordTrace]
  refine ⟨62954525417286710533859939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167878734446097894756959837 62954525417286710533859939)
  ·
    refine ⟨94431788125930065800789909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62954525417286710533859939 94431788125930065800789909)
    ·
      refine ⟨4426490068402971834412027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94431788125930065800789909 4426490068402971834412027)
      ·
        refine ⟨6639735102604457751618041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426490068402971834412027 6639735102604457751618041)
        ·
          refine ⟨4979801326953343313713531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639735102604457751618041 4979801326953343313713531)
          ·
            refine ⟨7469701990430014970570297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979801326953343313713531 7469701990430014970570297)
            ·
              refine ⟨5602276492822511227927723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469701990430014970570297 5602276492822511227927723)
              ·
                refine ⟨8403414739233766841891585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602276492822511227927723 8403414739233766841891585)
                ·
                  refine ⟨6302561054425325131418689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403414739233766841891585 6302561054425325131418689)
                  ·
                    refine ⟨4726920790818993848564017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302561054425325131418689 4726920790818993848564017)
                    ·
                      refine ⟨3545190593114245386423013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4726920790818993848564017 3545190593114245386423013)
                      ·
                        rfl

theorem cell23_6904234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6904234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904234 prefixEnd_6904234 := by exact prefixLift 6904234
  have htrace : WordTrace (prefixWord ++ tailWord_6904234) baseStart_6904234 baseEnd_6904234 := by
    simpa [prefixWord, tailWord_6904234, baseEnd_6904234] using wordTrace_append hprefix tailTrace_6904234
  have hstable : (prefixWord ++ tailWord_6904234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904234).length < 2 ^ (prefixWord ++ tailWord_6904234).sum := by decide
  have hdescent : baseEnd_6904234 < baseStart_6904234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904306 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6904306 : Nat := 118140960795 + 6904306 * 2 ^ 59
def prefixEnd_6904306 : Nat := 4983230072969 + 3 ^ 40 * 6904306 * 2
def baseEnd_6904306 : Nat := 3545227563721369104722681

theorem tailTrace_6904306 : CollatzResearch.WordTrace tailWord_6904306 prefixEnd_6904306 3545227563721369104722681 := by
  unfold tailWord_6904306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62955181931221499608015193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167880485149923998954707181 62955181931221499608015193)
  ·
    refine ⟨47216386448416124706011395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62955181931221499608015193 47216386448416124706011395)
    ·
      refine ⟨70824579672624187059017093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47216386448416124706011395 70824579672624187059017093)
      ·
        refine ⟨13279608688617035073565705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70824579672624187059017093 13279608688617035073565705)
        ·
          refine ⟨9959706516462776305174279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13279608688617035073565705 9959706516462776305174279)
          ·
            refine ⟨14939559774694164457761419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9959706516462776305174279 14939559774694164457761419)
            ·
              refine ⟨22409339662041246686642129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14939559774694164457761419 22409339662041246686642129)
              ·
                refine ⟨16807004746530935014981597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22409339662041246686642129 16807004746530935014981597)
                ·
                  refine ⟨6302626779949100630618099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16807004746530935014981597 6302626779949100630618099)
                  ·
                    refine ⟨9453940169923650945927149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6302626779949100630618099 9453940169923650945927149)
                    ·
                      refine ⟨3545227563721369104722681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9453940169923650945927149 3545227563721369104722681)
                      ·
                        rfl

theorem cell23_6904306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6904306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904306 prefixEnd_6904306 := by exact prefixLift 6904306
  have htrace : WordTrace (prefixWord ++ tailWord_6904306) baseStart_6904306 baseEnd_6904306 := by
    simpa [prefixWord, tailWord_6904306, baseEnd_6904306] using wordTrace_append hprefix tailTrace_6904306
  have hstable : (prefixWord ++ tailWord_6904306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904306).length < 2 ^ (prefixWord ++ tailWord_6904306).sum := by decide
  have hdescent : baseEnd_6904306 < baseStart_6904306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904312 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_6904312 : Nat := 118140960795 + 6904312 * 2 ^ 59
def prefixEnd_6904312 : Nat := 4983230072969 + 3 ^ 40 * 6904312 * 2
def baseEnd_6904312 : Nat := 3545230644605296081247653

theorem tailTrace_6904312 : CollatzResearch.WordTrace tailWord_6904312 prefixEnd_6904312 3545230644605296081247653 := by
  unfold tailWord_6904312
  simp only [CollatzResearch.WordTrace]
  refine ⟨125910473281432130728389595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167880631041909507637852793 125910473281432130728389595)
  ·
    refine ⟨188865709922148196092584393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125910473281432130728389595 188865709922148196092584393)
    ·
      refine ⟨141649282441611147069438295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188865709922148196092584393 141649282441611147069438295)
      ·
        refine ⟨212473923662416720604157443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141649282441611147069438295 212473923662416720604157443)
        ·
          refine ⟨318710885493625080906236165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212473923662416720604157443 318710885493625080906236165)
          ·
            refine ⟨59758291030054702669919281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318710885493625080906236165 59758291030054702669919281)
            ·
              refine ⟨44818718272541027002439461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59758291030054702669919281 44818718272541027002439461)
              ·
                refine ⟨8403509676101442562957399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44818718272541027002439461 8403509676101442562957399)
                ·
                  refine ⟨12605264514152163844436099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8403509676101442562957399 12605264514152163844436099)
                  ·
                    refine ⟨18907896771228245766654149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12605264514152163844436099 18907896771228245766654149)
                    ·
                      refine ⟨3545230644605296081247653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18907896771228245766654149 3545230644605296081247653)
                      ·
                        rfl

theorem cell23_6904312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_6904312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904312 prefixEnd_6904312 := by exact prefixLift 6904312
  have htrace : WordTrace (prefixWord ++ tailWord_6904312) baseStart_6904312 baseEnd_6904312 := by
    simpa [prefixWord, tailWord_6904312, baseEnd_6904312] using wordTrace_append hprefix tailTrace_6904312
  have hstable : (prefixWord ++ tailWord_6904312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904312).length < 2 ^ (prefixWord ++ tailWord_6904312).sum := by decide
  have hdescent : baseEnd_6904312 < baseStart_6904312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904356 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_6904356 : Nat := 118140960795 + 6904356 * 2 ^ 59
def prefixEnd_6904356 : Nat := 4983230072969 + 3 ^ 40 * 6904356 * 2
def baseEnd_6904356 : Nat := 1181751079251364636365817

theorem tailTrace_6904356 : CollatzResearch.WordTrace tailWord_6904356 prefixEnd_6904356 1181751079251364636365817 := by
  unfold tailWord_6904356
  simp only [CollatzResearch.WordTrace]
  refine ⟨125911275687352428485690461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167881700916469904647587281 125911275687352428485690461)
  ·
    refine ⟨47216728382757160682133923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125911275687352428485690461 47216728382757160682133923)
    ·
      refine ⟨70825092574135741023200885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47216728382757160682133923 70825092574135741023200885)
      ·
        refine ⟨6639852428825225720925083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70825092574135741023200885 6639852428825225720925083)
        ·
          refine ⟨9959778643237838581387625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639852428825225720925083 9959778643237838581387625)
          ·
            refine ⟨7469833982428378936040719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959778643237838581387625 7469833982428378936040719)
            ·
              refine ⟨11204750973642568404061079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469833982428378936040719 11204750973642568404061079)
              ·
                refine ⟨16807126460463852606091619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204750973642568404061079 16807126460463852606091619)
                ·
                  refine ⟨25210689690695778909137429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16807126460463852606091619 25210689690695778909137429)
                  ·
                    refine ⟨1181751079251364636365817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25210689690695778909137429 1181751079251364636365817)
                    ·
                      rfl

theorem cell23_6904356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_6904356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904356 prefixEnd_6904356 := by exact prefixLift 6904356
  have htrace : WordTrace (prefixWord ++ tailWord_6904356) baseStart_6904356 baseEnd_6904356 := by
    simpa [prefixWord, tailWord_6904356, baseEnd_6904356] using wordTrace_append hprefix tailTrace_6904356
  have hstable : (prefixWord ++ tailWord_6904356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904356).length < 2 ^ (prefixWord ++ tailWord_6904356).sum := by decide
  have hdescent : baseEnd_6904356 < baseStart_6904356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904375 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_6904375 : Nat := 118140960795 + 6904375 * 2 ^ 59
def prefixEnd_6904375 : Nat := 4983230072969 + 3 ^ 40 * 6904375 * 2
def baseEnd_6904375 : Nat := 3545262993886529334759863

theorem tailTrace_6904375 : CollatzResearch.WordTrace tailWord_6904375 prefixEnd_6904375 3545262993886529334759863 := by
  unfold tailWord_6904375
  simp only [CollatzResearch.WordTrace]
  refine ⟨251823244361636023216322579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167882162907757348810881719 251823244361636023216322579)
  ·
    refine ⟨377734866542454034824483869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251823244361636023216322579 377734866542454034824483869)
    ·
      refine ⟨141650574953420263059181451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377734866542454034824483869 141650574953420263059181451)
      ·
        refine ⟨212475862430130394588772177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141650574953420263059181451 212475862430130394588772177)
        ·
          refine ⟨159356896822597795941579133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212475862430130394588772177 159356896822597795941579133)
          ·
            refine ⟨59758836308474173478092175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159356896822597795941579133 59758836308474173478092175)
            ·
              refine ⟨89638254462711260217138263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59758836308474173478092175 89638254462711260217138263)
              ·
                refine ⟨134457381694066890325707395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89638254462711260217138263 134457381694066890325707395)
                ·
                  refine ⟨201686072541100335488561093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134457381694066890325707395 201686072541100335488561093)
                  ·
                    refine ⟨37816138601456312904105205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201686072541100335488561093 37816138601456312904105205)
                    ·
                      refine ⟨3545262993886529334759863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37816138601456312904105205 3545262993886529334759863)
                      ·
                        rfl

theorem cell23_6904375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_6904375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904375 prefixEnd_6904375 := by exact prefixLift 6904375
  have htrace : WordTrace (prefixWord ++ tailWord_6904375) baseStart_6904375 baseEnd_6904375 := by
    simpa [prefixWord, tailWord_6904375, baseEnd_6904375] using wordTrace_append hprefix tailTrace_6904375
  have hstable : (prefixWord ++ tailWord_6904375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904375).length < 2 ^ (prefixWord ++ tailWord_6904375).sum := by decide
  have hdescent : baseEnd_6904375 < baseStart_6904375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904380 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_6904380 : Nat := 118140960795 + 6904380 * 2 ^ 59
def prefixEnd_6904380 : Nat := 4983230072969 + 3 ^ 40 * 6904380 * 2
def baseEnd_6904380 : Nat := 3545265561289801815197341

theorem tailTrace_6904380 : CollatzResearch.WordTrace tailWord_6904380 prefixEnd_6904380 3545265561289801815197341 := by
  unfold tailWord_6904380
  simp only [CollatzResearch.WordTrace]
  refine ⟨125911713363308954535127297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167882284484411939380169729 125911713363308954535127297)
  ·
    refine ⟨94433785022481715901345473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125911713363308954535127297 94433785022481715901345473)
    ·
      refine ⟨70825338766861286926009105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94433785022481715901345473 70825338766861286926009105)
      ·
        refine ⟨53119004075145965194506829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70825338766861286926009105 53119004075145965194506829)
        ·
          refine ⟨19919626528179736947940061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53119004075145965194506829 19919626528179736947940061)
          ·
            refine ⟨7469859948067401355477523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19919626528179736947940061 7469859948067401355477523)
            ·
              refine ⟨11204789922101102033216285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469859948067401355477523 11204789922101102033216285)
              ·
                refine ⟨4201796220787913262456107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11204789922101102033216285 4201796220787913262456107)
                ·
                  refine ⟨6302694331181869893684161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201796220787913262456107 6302694331181869893684161)
                  ·
                    refine ⟨4727020748386402420263121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302694331181869893684161 4727020748386402420263121)
                    ·
                      refine ⟨3545265561289801815197341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727020748386402420263121 3545265561289801815197341)
                      ·
                        rfl

theorem cell23_6904380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_6904380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904380 prefixEnd_6904380 := by exact prefixLift 6904380
  have htrace : WordTrace (prefixWord ++ tailWord_6904380) baseStart_6904380 baseEnd_6904380 := by
    simpa [prefixWord, tailWord_6904380, baseEnd_6904380] using wordTrace_append hprefix tailTrace_6904380
  have hstable : (prefixWord ++ tailWord_6904380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904380).length < 2 ^ (prefixWord ++ tailWord_6904380).sum := by decide
  have hdescent : baseEnd_6904380 < baseStart_6904380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904395 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 6]
def baseStart_6904395 : Nat := 118140960795 + 6904395 * 2 ^ 59
def prefixEnd_6904395 : Nat := 4983230072969 + 3 ^ 40 * 6904395 * 2
def baseEnd_6904395 : Nat := 1181757754499873085503257

theorem tailTrace_6904395 : CollatzResearch.WordTrace tailWord_6904395 prefixEnd_6904395 1181757754499873085503257 := by
  unfold tailWord_6904395
  simp only [CollatzResearch.WordTrace]
  refine ⟨251823973821563566632050639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167882649214375711088033759 251823973821563566632050639)
  ·
    refine ⟨377735960732345349948075959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251823973821563566632050639 377735960732345349948075959)
    ·
      refine ⟨566603941098518024922113939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377735960732345349948075959 566603941098518024922113939)
      ·
        refine ⟨849905911647777037383170909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566603941098518024922113939 849905911647777037383170909)
        ·
          refine ⟨318714716867916389018689091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 849905911647777037383170909 318714716867916389018689091)
          ·
            refine ⟨478072075301874583528033637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318714716867916389018689091 478072075301874583528033637)
            ·
              refine ⟨89638514119101484411506307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 478072075301874583528033637 89638514119101484411506307)
              ·
                refine ⟨134457771178652226617259461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89638514119101484411506307 134457771178652226617259461)
                ·
                  refine ⟨25210832095997292490736149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134457771178652226617259461 25210832095997292490736149)
                  ·
                    refine ⟨1181757754499873085503257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25210832095997292490736149 1181757754499873085503257)
                    ·
                      rfl

theorem cell23_6904395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_6904395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904395 prefixEnd_6904395 := by exact prefixLift 6904395
  have htrace : WordTrace (prefixWord ++ tailWord_6904395) baseStart_6904395 baseEnd_6904395 := by
    simpa [prefixWord, tailWord_6904395, baseEnd_6904395] using wordTrace_append hprefix tailTrace_6904395
  have hstable : (prefixWord ++ tailWord_6904395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904395).length < 2 ^ (prefixWord ++ tailWord_6904395).sum := by decide
  have hdescent : baseEnd_6904395 < baseStart_6904395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904397 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_6904397 : Nat := 118140960795 + 6904397 * 2 ^ 59
def prefixEnd_6904397 : Nat := 4983230072969 + 3 ^ 40 * 6904397 * 2
def baseEnd_6904397 : Nat := 3545274290460928248684763

theorem tailTrace_6904397 : CollatzResearch.WordTrace tailWord_6904397 prefixEnd_6904397 3545274290460928248684763 := by
  unfold tailWord_6904397
  simp only [CollatzResearch.WordTrace]
  refine ⟨251824046767556320973623445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167882697845037547315748963 251824046767556320973623445)
  ·
    refine ⟨11804252192229202545638599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 251824046767556320973623445 11804252192229202545638599)
    ·
      refine ⟨17706378288343803818457899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11804252192229202545638599 17706378288343803818457899)
      ·
        refine ⟨26559567432515705727686849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17706378288343803818457899 26559567432515705727686849)
        ·
          refine ⟨19919675574386779295765137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26559567432515705727686849 19919675574386779295765137)
          ·
            refine ⟨14939756680790084471823853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19919675574386779295765137 14939756680790084471823853)
            ·
              refine ⟨5602408755296281676933945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14939756680790084471823853 5602408755296281676933945)
              ·
                refine ⟨4201806566472211257700459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602408755296281676933945 4201806566472211257700459)
                ·
                  refine ⟨6302709849708316886550689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201806566472211257700459 6302709849708316886550689)
                  ·
                    refine ⟨4727032387281237664913017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302709849708316886550689 4727032387281237664913017)
                    ·
                      refine ⟨3545274290460928248684763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727032387281237664913017 3545274290460928248684763)
                      ·
                        rfl

theorem cell23_6904397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_6904397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904397 prefixEnd_6904397 := by exact prefixLift 6904397
  have htrace : WordTrace (prefixWord ++ tailWord_6904397) baseStart_6904397 baseEnd_6904397 := by
    simpa [prefixWord, tailWord_6904397, baseEnd_6904397] using wordTrace_append hprefix tailTrace_6904397
  have hstable : (prefixWord ++ tailWord_6904397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904397).length < 2 ^ (prefixWord ++ tailWord_6904397).sum := by decide
  have hdescent : baseEnd_6904397 < baseStart_6904397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904402 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6904402 : Nat := 118140960795 + 6904402 * 2 ^ 59
def prefixEnd_6904402 : Nat := 4983230072969 + 3 ^ 40 * 6904402 * 2
def baseEnd_6904402 : Nat := 3545276857864200729122239

theorem tailTrace_6904402 : CollatzResearch.WordTrace tailWord_6904402 prefixEnd_6904402 3545276857864200729122239 := by
  unfold tailWord_6904402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62956057283134551706888865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167882819421692137885036973 62956057283134551706888865)
  ·
    refine ⟨47217042962350913780166649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62956057283134551706888865 47217042962350913780166649)
    ·
      refine ⟨35412782221763185335124987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47217042962350913780166649 35412782221763185335124987)
      ·
        refine ⟨53119173332644778002687481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35412782221763185335124987 53119173332644778002687481)
        ·
          refine ⟨39839379999483583502015611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53119173332644778002687481 39839379999483583502015611)
          ·
            refine ⟨59759069999225375253023417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39839379999483583502015611 59759069999225375253023417)
            ·
              refine ⟨44819302499419031439767563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59759069999225375253023417 44819302499419031439767563)
              ·
                refine ⟨67228953749128547159651345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44819302499419031439767563 67228953749128547159651345)
                ·
                  refine ⟨50421715311846410369738509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67228953749128547159651345 50421715311846410369738509)
                  ·
                    refine ⟨18908143241942403888651941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50421715311846410369738509 18908143241942403888651941)
                    ·
                      refine ⟨3545276857864200729122239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18908143241942403888651941 3545276857864200729122239)
                      ·
                        rfl

theorem cell23_6904402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6904402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904402 prefixEnd_6904402 := by exact prefixLift 6904402
  have htrace : WordTrace (prefixWord ++ tailWord_6904402) baseStart_6904402 baseEnd_6904402 := by
    simpa [prefixWord, tailWord_6904402, baseEnd_6904402] using wordTrace_append hprefix tailTrace_6904402
  have hstable : (prefixWord ++ tailWord_6904402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904402).length < 2 ^ (prefixWord ++ tailWord_6904402).sum := by decide
  have hdescent : baseEnd_6904402 < baseStart_6904402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904415 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_6904415 : Nat := 118140960795 + 6904415 * 2 ^ 59
def prefixEnd_6904415 : Nat := 4983230072969 + 3 ^ 40 * 6904415 * 2
def baseEnd_6904415 : Nat := 3545283533112709178259679

theorem tailTrace_6904415 : CollatzResearch.WordTrace tailWord_6904415 prefixEnd_6904415 3545283533112709178259679 := by
  unfold tailWord_6904415
  simp only [CollatzResearch.WordTrace]
  refine ⟨251824703281491110047778699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167883135520994073365185799 251824703281491110047778699)
  ·
    refine ⟨377737054922236665071668049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251824703281491110047778699 377737054922236665071668049)
    ·
      refine ⟨283302791191677498803751037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377737054922236665071668049 283302791191677498803751037)
      ·
        refine ⟨106238546696879062051406639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283302791191677498803751037 106238546696879062051406639)
        ·
          refine ⟨159357820045318593077109959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106238546696879062051406639 159357820045318593077109959)
          ·
            refine ⟨239036730067977889615664939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159357820045318593077109959 239036730067977889615664939)
            ·
              refine ⟨358555095101966834423497409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239036730067977889615664939 358555095101966834423497409)
              ·
                refine ⟨268916321326475125817623057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358555095101966834423497409 268916321326475125817623057)
                ·
                  refine ⟨201687240994856344363217293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268916321326475125817623057 201687240994856344363217293)
                  ·
                    refine ⟨75632715373071129136206485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201687240994856344363217293 75632715373071129136206485)
                    ·
                      refine ⟨3545283533112709178259679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75632715373071129136206485 3545283533112709178259679)
                      ·
                        rfl

theorem cell23_6904415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_6904415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904415 prefixEnd_6904415 := by exact prefixLift 6904415
  have htrace : WordTrace (prefixWord ++ tailWord_6904415) baseStart_6904415 baseEnd_6904415 := by
    simpa [prefixWord, tailWord_6904415, baseEnd_6904415] using wordTrace_append hprefix tailTrace_6904415
  have hstable : (prefixWord ++ tailWord_6904415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904415).length < 2 ^ (prefixWord ++ tailWord_6904415).sum := by decide
  have hdescent : baseEnd_6904415 < baseStart_6904415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904419 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 4, 2]
def baseStart_6904419 : Nat := 118140960795 + 6904419 * 2 ^ 59
def prefixEnd_6904419 : Nat := 4983230072969 + 3 ^ 40 * 6904419 * 2
def baseEnd_6904419 : Nat := 3545285587035327162609661

theorem tailTrace_6904419 : CollatzResearch.WordTrace tailWord_6904419 prefixEnd_6904419 3545285587035327162609661 := by
  unfold tailWord_6904419
  simp only [CollatzResearch.WordTrace]
  refine ⟨251824849173476618730924311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167883232782317745820616207 251824849173476618730924311)
  ·
    refine ⟨377737273760214928096386467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251824849173476618730924311 377737273760214928096386467)
    ·
      refine ⟨566605910640322392144579701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377737273760214928096386467 566605910640322392144579701)
      ·
        refine ⟨53119304122530224263554347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 566605910640322392144579701 53119304122530224263554347)
        ·
          refine ⟨79678956183795336395331521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53119304122530224263554347 79678956183795336395331521)
          ·
            refine ⟨59759217137846502296498641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79678956183795336395331521 59759217137846502296498641)
            ·
              refine ⟨44819412853384876722373981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59759217137846502296498641 44819412853384876722373981)
              ·
                refine ⟨16807279820019328770890243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44819412853384876722373981 16807279820019328770890243)
                ·
                  refine ⟨25210919730028993156335365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16807279820019328770890243 25210919730028993156335365)
                  ·
                    refine ⟨4727047449380436216812881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25210919730028993156335365 4727047449380436216812881)
                    ·
                      refine ⟨3545285587035327162609661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727047449380436216812881 3545285587035327162609661)
                      ·
                        rfl

theorem cell23_6904419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_6904419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904419 prefixEnd_6904419 := by exact prefixLift 6904419
  have htrace : WordTrace (prefixWord ++ tailWord_6904419) baseStart_6904419 baseEnd_6904419 := by
    simpa [prefixWord, tailWord_6904419, baseEnd_6904419] using wordTrace_append hprefix tailTrace_6904419
  have hstable : (prefixWord ++ tailWord_6904419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904419).length < 2 ^ (prefixWord ++ tailWord_6904419).sum := by decide
  have hdescent : baseEnd_6904419 < baseStart_6904419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904425 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 9]
def baseStart_6904425 : Nat := 118140960795 + 6904425 * 2 ^ 59
def prefixEnd_6904425 : Nat := 4983230072969 + 3 ^ 40 * 6904425 * 2
def baseEnd_6904425 : Nat := 393920963102139348792737

theorem tailTrace_6904425 : CollatzResearch.WordTrace tailWord_6904425 prefixEnd_6904425 393920963102139348792737 := by
  unfold tailWord_6904425
  simp only [CollatzResearch.WordTrace]
  refine ⟨251825068011454881755642729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167883378674303254503761819 251825068011454881755642729)
  ·
    refine ⟨188868801008591161316732047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251825068011454881755642729 188868801008591161316732047)
    ·
      refine ⟨283303201512886741975098071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188868801008591161316732047 283303201512886741975098071)
      ·
        refine ⟨424954802269330112962647107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283303201512886741975098071 424954802269330112962647107)
        ·
          refine ⟨637432203403995169443970661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424954802269330112962647107 637432203403995169443970661)
          ·
            refine ⟨119518538138249094270744499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637432203403995169443970661 119518538138249094270744499)
            ·
              refine ⟨179277807207373641406116749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119518538138249094270744499 179277807207373641406116749)
              ·
                refine ⟨67229177702765115527293781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179277807207373641406116749 67229177702765115527293781)
                ·
                  refine ⟨393920963102139348792737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67229177702765115527293781 393920963102139348792737)
                  ·
                    rfl

theorem cell23_6904425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_6904425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904425 prefixEnd_6904425 := by exact prefixLift 6904425
  have htrace : WordTrace (prefixWord ++ tailWord_6904425) baseStart_6904425 baseEnd_6904425 := by
    simpa [prefixWord, tailWord_6904425, baseEnd_6904425] using wordTrace_append hprefix tailTrace_6904425
  have hstable : (prefixWord ++ tailWord_6904425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904425).length < 2 ^ (prefixWord ++ tailWord_6904425).sum := by decide
  have hdescent : baseEnd_6904425 < baseStart_6904425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904435 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_6904435 : Nat := 118140960795 + 6904435 * 2 ^ 59
def prefixEnd_6904435 : Nat := 4983230072969 + 3 ^ 40 * 6904435 * 2
def baseEnd_6904435 : Nat := 3545293802725799100009587

theorem tailTrace_6904435 : CollatzResearch.WordTrace tailWord_6904435 prefixEnd_6904435 3545293802725799100009587 := by
  unfold tailWord_6904435
  simp only [CollatzResearch.WordTrace]
  refine ⟨251825432741418653463506759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167883621827612435642337839 251825432741418653463506759)
  ·
    refine ⟨377738149112127980195260139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251825432741418653463506759 377738149112127980195260139)
    ·
      refine ⟨566607223668191970292890209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377738149112127980195260139 566607223668191970292890209)
      ·
        refine ⟨424955417751143977719667657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566607223668191970292890209 424955417751143977719667657)
        ·
          refine ⟨318716563313357983289750743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424955417751143977719667657 318716563313357983289750743)
          ·
            refine ⟨478074844970036974934626115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318716563313357983289750743 478074844970036974934626115)
            ·
              refine ⟨717112267455055462401939173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478074844970036974934626115 717112267455055462401939173)
              ·
                refine ⟨134458550147822899200363595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717112267455055462401939173 134458550147822899200363595)
                ·
                  refine ⟨201687825221734348800545393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134458550147822899200363595 201687825221734348800545393)
                  ·
                    refine ⟨151265868916300761600409045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201687825221734348800545393 151265868916300761600409045)
                    ·
                      refine ⟨3545293802725799100009587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151265868916300761600409045 3545293802725799100009587)
                      ·
                        rfl

theorem cell23_6904435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_6904435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904435 prefixEnd_6904435 := by exact prefixLift 6904435
  have htrace : WordTrace (prefixWord ++ tailWord_6904435) baseStart_6904435 baseEnd_6904435 := by
    simpa [prefixWord, tailWord_6904435, baseEnd_6904435] using wordTrace_append hprefix tailTrace_6904435
  have hstable : (prefixWord ++ tailWord_6904435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904435).length < 2 ^ (prefixWord ++ tailWord_6904435).sum := by decide
  have hdescent : baseEnd_6904435 < baseStart_6904435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904453 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_6904453 : Nat := 118140960795 + 6904453 * 2 ^ 59
def prefixEnd_6904453 : Nat := 4983230072969 + 3 ^ 40 * 6904453 * 2
def baseEnd_6904453 : Nat := 3545303045377580029584505

theorem tailTrace_6904453 : CollatzResearch.WordTrace tailWord_6904453 prefixEnd_6904453 3545303045377580029584505 := by
  unfold tailWord_6904453
  simp only [CollatzResearch.WordTrace]
  refine ⟨251826089255353442537662013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167884059503568961691774675 251826089255353442537662013)
  ·
    refine ⟨94434783470757540951623255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251826089255353442537662013 94434783470757540951623255)
    ·
      refine ⟨141652175206136311427434883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94434783470757540951623255 141652175206136311427434883)
      ·
        refine ⟨212478262809204467141152325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141652175206136311427434883 212478262809204467141152325)
        ·
          refine ⟨39839674276725837588966061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212478262809204467141152325 39839674276725837588966061)
          ·
            refine ⟨14939877853772189095862273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39839674276725837588966061 14939877853772189095862273)
            ·
              refine ⟨11204908390329141821896705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14939877853772189095862273 11204908390329141821896705)
              ·
                refine ⟨8403681292746856366422529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11204908390329141821896705 8403681292746856366422529)
                ·
                  refine ⟨6302760969560142274816897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403681292746856366422529 6302760969560142274816897)
                  ·
                    refine ⟨4727070727170106706112673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302760969560142274816897 4727070727170106706112673)
                    ·
                      refine ⟨3545303045377580029584505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727070727170106706112673 3545303045377580029584505)
                      ·
                        rfl

theorem cell23_6904453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_6904453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904453 prefixEnd_6904453 := by exact prefixLift 6904453
  have htrace : WordTrace (prefixWord ++ tailWord_6904453) baseStart_6904453 baseEnd_6904453 := by
    simpa [prefixWord, tailWord_6904453, baseEnd_6904453] using wordTrace_append hprefix tailTrace_6904453
  have hstable : (prefixWord ++ tailWord_6904453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904453).length < 2 ^ (prefixWord ++ tailWord_6904453).sum := by decide
  have hdescent : baseEnd_6904453 < baseStart_6904453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904472 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_6904472 : Nat := 118140960795 + 6904472 * 2 ^ 59
def prefixEnd_6904472 : Nat := 4983230072969 + 3 ^ 40 * 6904472 * 2
def baseEnd_6904472 : Nat := 1181770933836671818415639

theorem tailTrace_6904472 : CollatzResearch.WordTrace tailWord_6904472 prefixEnd_6904472 1181770933836671818415639 := by
  unfold tailWord_6904472
  simp only [CollatzResearch.WordTrace]
  refine ⟨125913391121142304391301835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167884521494856405855069113 125913391121142304391301835)
  ·
    refine ⟨188870086681713456586952753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125913391121142304391301835 188870086681713456586952753)
    ·
      refine ⟨141652565011285092440214565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188870086681713456586952753 141652565011285092440214565)
      ·
        refine ⟨26559855939615954832540231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141652565011285092440214565 26559855939615954832540231)
        ·
          refine ⟨39839783909423932248810347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26559855939615954832540231 39839783909423932248810347)
          ·
            refine ⟨59759675864135898373215521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39839783909423932248810347 59759675864135898373215521)
            ·
              refine ⟨44819756898101923779911641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59759675864135898373215521 44819756898101923779911641)
              ·
                refine ⟨33614817673576442834933731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44819756898101923779911641 33614817673576442834933731)
                ·
                  refine ⟨50422226510364664252400597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33614817673576442834933731 50422226510364664252400597)
                  ·
                    refine ⟨1181770933836671818415639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50422226510364664252400597 1181770933836671818415639)
                    ·
                      rfl

theorem cell23_6904472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_6904472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904472 prefixEnd_6904472 := by exact prefixLift 6904472
  have htrace : WordTrace (prefixWord ++ tailWord_6904472) baseStart_6904472 baseEnd_6904472 := by
    simpa [prefixWord, tailWord_6904472, baseEnd_6904472] using wordTrace_append hprefix tailTrace_6904472
  have hstable : (prefixWord ++ tailWord_6904472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904472).length < 2 ^ (prefixWord ++ tailWord_6904472).sum := by decide
  have hdescent : baseEnd_6904472 < baseStart_6904472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904526 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_6904526 : Nat := 118140960795 + 6904526 * 2 ^ 59
def prefixEnd_6904526 : Nat := 4983230072969 + 3 ^ 40 * 6904526 * 2
def baseEnd_6904526 : Nat := 3545340529465358243971669

theorem tailTrace_6904526 : CollatzResearch.WordTrace tailWord_6904526 prefixEnd_6904526 3545340529465358243971669 := by
  unfold tailWord_6904526
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478593973011122000633679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167885834522725984003379621 31478593973011122000633679)
  ·
    refine ⟨47217890959516683000950519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31478593973011122000633679 47217890959516683000950519)
    ·
      refine ⟨70826836439275024501425779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47217890959516683000950519 70826836439275024501425779)
      ·
        refine ⟨106240254658912536752138669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70826836439275024501425779 106240254658912536752138669)
        ·
          refine ⟨39840095497092201282052001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106240254658912536752138669 39840095497092201282052001)
          ·
            refine ⟨29880071622819150961539001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39840095497092201282052001 29880071622819150961539001)
            ·
              refine ⟨22410053717114363221154251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29880071622819150961539001 22410053717114363221154251)
              ·
                refine ⟨33615080575671544831731377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22410053717114363221154251 33615080575671544831731377)
                ·
                  refine ⟨25211310431753658623798533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33615080575671544831731377 25211310431753658623798533)
                  ·
                    refine ⟨4727120705953810991962225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25211310431753658623798533 4727120705953810991962225)
                    ·
                      refine ⟨3545340529465358243971669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727120705953810991962225 3545340529465358243971669)
                      ·
                        rfl

theorem cell23_6904526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_6904526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904526 prefixEnd_6904526 := by exact prefixLift 6904526
  have htrace : WordTrace (prefixWord ++ tailWord_6904526) baseStart_6904526 baseEnd_6904526 := by
    simpa [prefixWord, tailWord_6904526, baseEnd_6904526] using wordTrace_append hprefix tailTrace_6904526
  have hstable : (prefixWord ++ tailWord_6904526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904526).length < 2 ^ (prefixWord ++ tailWord_6904526).sum := by decide
  have hdescent : baseEnd_6904526 < baseStart_6904526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904583 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 6]
def baseStart_6904583 : Nat := 118140960795 + 6904583 * 2 ^ 59
def prefixEnd_6904583 : Nat := 4983230072969 + 3 ^ 40 * 6904583 * 2
def baseEnd_6904583 : Nat := 393929977540296057884323

theorem tailTrace_6904583 : CollatzResearch.WordTrace tailWord_6904583 prefixEnd_6904583 393929977540296057884323 := by
  unfold tailWord_6904583
  simp only [CollatzResearch.WordTrace]
  refine ⟨251830830744882474739894403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167887220496588316493262935 251830830744882474739894403)
  ·
    refine ⟨377746246117323712109841605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251830830744882474739894403 377746246117323712109841605)
    ·
      refine ⟨70827421146998196020595301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 377746246117323712109841605 70827421146998196020595301)
      ·
        refine ⟨13280141465062161753861619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70827421146998196020595301 13280141465062161753861619)
        ·
          refine ⟨19920212197593242630792429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280141465062161753861619 19920212197593242630792429)
          ·
            refine ⟨7470079574097465986547161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19920212197593242630792429 7470079574097465986547161)
            ·
              refine ⟨5602559680573099489910371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470079574097465986547161 5602559680573099489910371)
              ·
                refine ⟨8403839520859649234865557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602559680573099489910371 8403839520859649234865557)
                ·
                  refine ⟨393929977540296057884323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8403839520859649234865557 393929977540296057884323)
                  ·
                    rfl

theorem cell23_6904583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 6].length) (baseStart_6904583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904583 prefixEnd_6904583 := by exact prefixLift 6904583
  have htrace : WordTrace (prefixWord ++ tailWord_6904583) baseStart_6904583 baseEnd_6904583 := by
    simpa [prefixWord, tailWord_6904583, baseEnd_6904583] using wordTrace_append hprefix tailTrace_6904583
  have hstable : (prefixWord ++ tailWord_6904583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904583).length < 2 ^ (prefixWord ++ tailWord_6904583).sum := by decide
  have hdescent : baseEnd_6904583 < baseStart_6904583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904586 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_6904586 : Nat := 118140960795 + 6904586 * 2 ^ 59
def prefixEnd_6904586 : Nat := 4983230072969 + 3 ^ 40 * 6904586 * 2
def baseEnd_6904586 : Nat := 3545371338304628009221393

theorem tailTrace_6904586 : CollatzResearch.WordTrace tailWord_6904586 prefixEnd_6904586 3545371338304628009221393 := by
  unfold tailWord_6904586
  simp only [CollatzResearch.WordTrace]
  refine ⟨62957735040967901563063403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167887293442581070834835741 62957735040967901563063403)
  ·
    refine ⟨94436602561451852344595105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62957735040967901563063403 94436602561451852344595105)
    ·
      refine ⟨70827451921088889258446329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94436602561451852344595105 70827451921088889258446329)
      ·
        refine ⟨53120588940816666943834747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70827451921088889258446329 53120588940816666943834747)
        ·
          refine ⟨79680883411225000415752121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53120588940816666943834747 79680883411225000415752121)
          ·
            refine ⟨59760662558418750311814091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79680883411225000415752121 59760662558418750311814091)
            ·
              refine ⟨89640993837628125467721137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59760662558418750311814091 89640993837628125467721137)
              ·
                refine ⟨67230745378221094100790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89640993837628125467721137 67230745378221094100790853)
                ·
                  refine ⟨12605764758416455143898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67230745378221094100790853 12605764758416455143898285)
                  ·
                    refine ⟨4727161784406170678961857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12605764758416455143898285 4727161784406170678961857)
                    ·
                      refine ⟨3545371338304628009221393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727161784406170678961857 3545371338304628009221393)
                      ·
                        rfl

theorem cell23_6904586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_6904586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904586 prefixEnd_6904586 := by exact prefixLift 6904586
  have htrace : WordTrace (prefixWord ++ tailWord_6904586) baseStart_6904586 baseEnd_6904586 := by
    simpa [prefixWord, tailWord_6904586, baseEnd_6904586] using wordTrace_append hprefix tailTrace_6904586
  have hstable : (prefixWord ++ tailWord_6904586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904586).length < 2 ^ (prefixWord ++ tailWord_6904586).sum := by decide
  have hdescent : baseEnd_6904586 < baseStart_6904586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904609 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_6904609 : Nat := 118140960795 + 6904609 * 2 ^ 59
def prefixEnd_6904609 : Nat := 4983230072969 + 3 ^ 40 * 6904609 * 2
def baseEnd_6904609 : Nat := 1181794382786560473077929

theorem tailTrace_6904609 : CollatzResearch.WordTrace tailWord_6904609 prefixEnd_6904609 1181794382786560473077929 := by
  unfold tailWord_6904609
  simp only [CollatzResearch.WordTrace]
  refine ⟨251831779042788281180340881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167887852695192187453560587 251831779042788281180340881)
  ·
    refine ⟨188873834282091210885255661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251831779042788281180340881 188873834282091210885255661)
    ·
      refine ⟨70827687855784204081970873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188873834282091210885255661 70827687855784204081970873)
      ·
        refine ⟨53120765891838153061478155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70827687855784204081970873 53120765891838153061478155)
        ·
          refine ⟨79681148837757229592217233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53120765891838153061478155 79681148837757229592217233)
          ·
            refine ⟨59760861628317922194162925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79681148837757229592217233 59760861628317922194162925)
            ·
              refine ⟨22410323110619220822811097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59760861628317922194162925 22410323110619220822811097)
              ·
                refine ⟨16807742332964415617108323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22410323110619220822811097 16807742332964415617108323)
                ·
                  refine ⟨25211613499446623425662485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16807742332964415617108323 25211613499446623425662485)
                  ·
                    refine ⟨1181794382786560473077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25211613499446623425662485 1181794382786560473077929)
                    ·
                      rfl

theorem cell23_6904609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_6904609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904609 prefixEnd_6904609 := by exact prefixLift 6904609
  have htrace : WordTrace (prefixWord ++ tailWord_6904609) baseStart_6904609 baseEnd_6904609 := by
    simpa [prefixWord, tailWord_6904609, baseEnd_6904609] using wordTrace_append hprefix tailTrace_6904609
  have hstable : (prefixWord ++ tailWord_6904609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904609).length < 2 ^ (prefixWord ++ tailWord_6904609).sum := by decide
  have hdescent : baseEnd_6904609 < baseStart_6904609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904619 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3]
def baseStart_6904619 : Nat := 118140960795 + 6904619 * 2 ^ 59
def prefixEnd_6904619 : Nat := 4983230072969 + 3 ^ 40 * 6904619 * 2
def baseEnd_6904619 : Nat := 3545388283166226380108741

theorem tailTrace_6904619 : CollatzResearch.WordTrace tailWord_6904619 prefixEnd_6904619 3545388283166226380108741 := by
  unfold tailWord_6904619
  simp only [CollatzResearch.WordTrace]
  refine ⟨251832143772752052888204911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167888095848501368592136607 251832143772752052888204911)
  ·
    refine ⟨377748215659128079332307367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251832143772752052888204911 377748215659128079332307367)
    ·
      refine ⟨566622323488692118998461051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377748215659128079332307367 566622323488692118998461051)
      ·
        refine ⟨849933485233038178497691577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566622323488692118998461051 849933485233038178497691577)
        ·
          refine ⟨637450113924778633873268683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849933485233038178497691577 637450113924778633873268683)
          ·
            refine ⟨956175170887167950809903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637450113924778633873268683 956175170887167950809903025)
            ·
              refine ⟨717131378165375963107427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956175170887167950809903025 717131378165375963107427269)
              ·
                refine ⟨134462133406007993082642613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717131378165375963107427269 134462133406007993082642613)
                ·
                  refine ⟨12605825006813249351497745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134462133406007993082642613 12605825006813249351497745)
                  ·
                    refine ⟨9454368755109937013623309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12605825006813249351497745 9454368755109937013623309)
                    ·
                      refine ⟨3545388283166226380108741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454368755109937013623309 3545388283166226380108741)
                      ·
                        rfl

theorem cell23_6904619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 3].length) (baseStart_6904619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904619 prefixEnd_6904619 := by exact prefixLift 6904619
  have htrace : WordTrace (prefixWord ++ tailWord_6904619) baseStart_6904619 baseEnd_6904619 := by
    simpa [prefixWord, tailWord_6904619, baseEnd_6904619] using wordTrace_append hprefix tailTrace_6904619
  have hstable : (prefixWord ++ tailWord_6904619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904619).length < 2 ^ (prefixWord ++ tailWord_6904619).sum := by decide
  have hdescent : baseEnd_6904619 < baseStart_6904619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904621 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_6904621 : Nat := 118140960795 + 6904621 * 2 ^ 59
def prefixEnd_6904621 : Nat := 4983230072969 + 3 ^ 40 * 6904621 * 2
def baseEnd_6904621 : Nat := 1181796436709178457427911

theorem tailTrace_6904621 : CollatzResearch.WordTrace tailWord_6904621 prefixEnd_6904621 1181796436709178457427911 := by
  unfold tailWord_6904621
  simp only [CollatzResearch.WordTrace]
  refine ⟨251832216718744807229777717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167888144479163204819851811 251832216718744807229777717)
  ·
    refine ⟨23609270317382325677791661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251832216718744807229777717 23609270317382325677791661)
    ·
      refine ⟨8853476369018372129171873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23609270317382325677791661 8853476369018372129171873)
      ·
        refine ⟨6640107276763779096878905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8853476369018372129171873 6640107276763779096878905)
        ·
          refine ⟨4980080457572834322659179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640107276763779096878905 4980080457572834322659179)
          ·
            refine ⟨7470120686359251483988769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980080457572834322659179 7470120686359251483988769)
            ·
              refine ⟨5602590514769438612991577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470120686359251483988769 5602590514769438612991577)
              ·
                refine ⟨4201942886077078959743683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602590514769438612991577 4201942886077078959743683)
                ·
                  refine ⟨6302914329115618439615525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201942886077078959743683 6302914329115618439615525)
                  ·
                    refine ⟨1181796436709178457427911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6302914329115618439615525 1181796436709178457427911)
                    ·
                      rfl

theorem cell23_6904621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_6904621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904621 prefixEnd_6904621 := by exact prefixLift 6904621
  have htrace : WordTrace (prefixWord ++ tailWord_6904621) baseStart_6904621 baseEnd_6904621 := by
    simpa [prefixWord, tailWord_6904621, baseEnd_6904621] using wordTrace_append hprefix tailTrace_6904621
  have hstable : (prefixWord ++ tailWord_6904621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904621).length < 2 ^ (prefixWord ++ tailWord_6904621).sum := by decide
  have hdescent : baseEnd_6904621 < baseStart_6904621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904627 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 1, 1, 3]
def baseStart_6904627 : Nat := 118140960795 + 6904627 * 2 ^ 59
def prefixEnd_6904627 : Nat := 4983230072969 + 3 ^ 40 * 6904627 * 2
def baseEnd_6904627 : Nat := 3545392391011462348808705

theorem tailTrace_6904627 : CollatzResearch.WordTrace tailWord_6904627 prefixEnd_6904627 3545392391011462348808705 := by
  unfold tailWord_6904627
  simp only [CollatzResearch.WordTrace]
  refine ⟨251832435556723070254496135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167888290371148713502997423 251832435556723070254496135)
  ·
    refine ⟨377748653335084605381744203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251832435556723070254496135 377748653335084605381744203)
    ·
      refine ⟨566622980002626908072616305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377748653335084605381744203 566622980002626908072616305)
      ·
        refine ⟨424967235001970181054462229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566622980002626908072616305 424967235001970181054462229)
        ·
          refine ⟨19920339140717352236927917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 424967235001970181054462229 19920339140717352236927917)
          ·
            refine ⟨7470127177769007088847969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19920339140717352236927917 7470127177769007088847969)
            ·
              refine ⟨5602595383326755316635977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470127177769007088847969 5602595383326755316635977)
              ·
                refine ⟨4201946537495066487476983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602595383326755316635977 4201946537495066487476983)
                ·
                  refine ⟨6302919806242599731215475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201946537495066487476983 6302919806242599731215475)
                  ·
                    refine ⟨9454379709363899596823213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6302919806242599731215475 9454379709363899596823213)
                    ·
                      refine ⟨3545392391011462348808705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454379709363899596823213 3545392391011462348808705)
                      ·
                        rfl

theorem cell23_6904627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 1, 1, 3].length) (baseStart_6904627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904627 prefixEnd_6904627 := by exact prefixLift 6904627
  have htrace : WordTrace (prefixWord ++ tailWord_6904627) baseStart_6904627 baseEnd_6904627 := by
    simpa [prefixWord, tailWord_6904627, baseEnd_6904627] using wordTrace_append hprefix tailTrace_6904627
  have hstable : (prefixWord ++ tailWord_6904627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904627).length < 2 ^ (prefixWord ++ tailWord_6904627).sum := by decide
  have hdescent : baseEnd_6904627 < baseStart_6904627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904639 : List Nat := [1, 1, 2, 2, 5, 1, 3, 8]
def baseStart_6904639 : Nat := 118140960795 + 6904639 * 2 ^ 59
def prefixEnd_6904639 : Nat := 4983230072969 + 3 ^ 40 * 6904639 * 2
def baseEnd_6904639 : Nat := 131311057510345048216987

theorem tailTrace_6904639 : CollatzResearch.WordTrace tailWord_6904639 prefixEnd_6904639 131311057510345048216987 := by
  unfold tailWord_6904639
  simp only [CollatzResearch.WordTrace]
  refine ⟨251832873232679596303932971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167888582155119730869288647 251832873232679596303932971)
  ·
    refine ⟨377749309849019394455899457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251832873232679596303932971 377749309849019394455899457)
    ·
      refine ⟨283311982386764545841924593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377749309849019394455899457 283311982386764545841924593)
      ·
        refine ⟨212483986790073409381443445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283311982386764545841924593 212483986790073409381443445)
        ·
          refine ⟨19920373761569382129510323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212483986790073409381443445 19920373761569382129510323)
          ·
            refine ⟨29880560642354073194265485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19920373761569382129510323 29880560642354073194265485)
            ·
              refine ⟨11205210240882777447849557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29880560642354073194265485 11205210240882777447849557)
              ·
                refine ⟨131311057510345048216987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11205210240882777447849557 131311057510345048216987)
                ·
                  rfl

theorem cell23_6904639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 8].length) (baseStart_6904639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904639 prefixEnd_6904639 := by exact prefixLift 6904639
  have htrace : WordTrace (prefixWord ++ tailWord_6904639) baseStart_6904639 baseEnd_6904639 := by
    simpa [prefixWord, tailWord_6904639, baseEnd_6904639] using wordTrace_append hprefix tailTrace_6904639
  have hstable : (prefixWord ++ tailWord_6904639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904639).length < 2 ^ (prefixWord ++ tailWord_6904639).sum := by decide
  have hdescent : baseEnd_6904639 < baseStart_6904639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904666 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_6904666 : Nat := 118140960795 + 6904666 * 2 ^ 59
def prefixEnd_6904666 : Nat := 4983230072969 + 3 ^ 40 * 6904666 * 2
def baseEnd_6904666 : Nat := 3545412416756987696221025

theorem tailTrace_6904666 : CollatzResearch.WordTrace tailWord_6904666 prefixEnd_6904666 3545412416756987696221025 := by
  unfold tailWord_6904666
  simp only [CollatzResearch.WordTrace]
  refine ⟨62958464500895444978791463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167889238669054519943443901 62958464500895444978791463)
  ·
    refine ⟨94437696751343167468187195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62958464500895444978791463 94437696751343167468187195)
    ·
      refine ⟨141656545127014751202280793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94437696751343167468187195 141656545127014751202280793)
      ·
        refine ⟨106242408845261063401710595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141656545127014751202280793 106242408845261063401710595)
        ·
          refine ⟨159363613267891595102565893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106242408845261063401710595 159363613267891595102565893)
          ·
            refine ⟨29880677487729674081731105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159363613267891595102565893 29880677487729674081731105)
            ·
              refine ⟨22410508115797255561298329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29880677487729674081731105 22410508115797255561298329)
              ·
                refine ⟨16807881086847941670973747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22410508115797255561298329 16807881086847941670973747)
                ·
                  refine ⟨25211821630271912506460621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16807881086847941670973747 25211821630271912506460621)
                  ·
                    refine ⟨9454433111351967189922733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25211821630271912506460621 9454433111351967189922733)
                    ·
                      refine ⟨3545412416756987696221025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454433111351967189922733 3545412416756987696221025)
                      ·
                        rfl

theorem cell23_6904666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_6904666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904666 prefixEnd_6904666 := by exact prefixLift 6904666
  have htrace : WordTrace (prefixWord ++ tailWord_6904666) baseStart_6904666 baseEnd_6904666 := by
    simpa [prefixWord, tailWord_6904666, baseEnd_6904666] using wordTrace_append hprefix tailTrace_6904666
  have hstable : (prefixWord ++ tailWord_6904666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904666).length < 2 ^ (prefixWord ++ tailWord_6904666).sum := by decide
  have hdescent : baseEnd_6904666 < baseStart_6904666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904683 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 3]
def baseStart_6904683 : Nat := 118140960795 + 6904683 * 2 ^ 59
def prefixEnd_6904683 : Nat := 4983230072969 + 3 ^ 40 * 6904683 * 2
def baseEnd_6904683 : Nat := 3545421145928114129708447

theorem tailTrace_6904683 : CollatzResearch.WordTrace tailWord_6904683 prefixEnd_6904683 3545421145928114129708447 := by
  unfold tailWord_6904683
  simp only [CollatzResearch.WordTrace]
  refine ⟨251834478044520191818534703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167889652029680127879023135 251834478044520191818534703)
  ·
    refine ⟨377751717066780287727802055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251834478044520191818534703 377751717066780287727802055)
    ·
      refine ⟨566627575600170431591703083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377751717066780287727802055 566627575600170431591703083)
      ·
        refine ⟨849941363400255647387554625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566627575600170431591703083 849941363400255647387554625)
        ·
          refine ⟨637456022550191735540665969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849941363400255647387554625 637456022550191735540665969)
          ·
            refine ⟨478092016912643801655499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637456022550191735540665969 478092016912643801655499477)
            ·
              refine ⟨11205281646390089101300769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 478092016912643801655499477 11205281646390089101300769)
              ·
                refine ⟨8403961234792566825975577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11205281646390089101300769 8403961234792566825975577)
                ·
                  refine ⟨6302970926094425119481683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403961234792566825975577 6302970926094425119481683)
                  ·
                    refine ⟨9454456389141637679222525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6302970926094425119481683 9454456389141637679222525)
                    ·
                      refine ⟨3545421145928114129708447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454456389141637679222525 3545421145928114129708447)
                      ·
                        rfl

theorem cell23_6904683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 3].length) (baseStart_6904683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904683 prefixEnd_6904683 := by exact prefixLift 6904683
  have htrace : WordTrace (prefixWord ++ tailWord_6904683) baseStart_6904683 baseEnd_6904683 := by
    simpa [prefixWord, tailWord_6904683, baseEnd_6904683] using wordTrace_append hprefix tailTrace_6904683
  have hstable : (prefixWord ++ tailWord_6904683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904683).length < 2 ^ (prefixWord ++ tailWord_6904683).sum := by decide
  have hdescent : baseEnd_6904683 < baseStart_6904683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904699 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 6]
def baseStart_6904699 : Nat := 118140960795 + 6904699 * 2 ^ 59
def prefixEnd_6904699 : Nat := 4983230072969 + 3 ^ 40 * 6904699 * 2
def baseEnd_6904699 : Nat := 1181809787206195355702791

theorem tailTrace_6904699 : CollatzResearch.WordTrace tailWord_6904699 prefixEnd_6904699 1181809787206195355702791 := by
  unfold tailWord_6904699
  simp only [CollatzResearch.WordTrace]
  refine ⟨251835061612462226551117151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167890041074974817700744767 251835061612462226551117151)
  ·
    refine ⟨377752592418693339826675727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251835061612462226551117151 377752592418693339826675727)
    ·
      refine ⟨566628888628040009740013591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377752592418693339826675727 566628888628040009740013591)
      ·
        refine ⟨849943332942060014610020387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566628888628040009740013591 849943332942060014610020387)
        ·
          refine ⟨1274914999413090021915030581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849943332942060014610020387 1274914999413090021915030581)
          ·
            refine ⟨119523281194977189554534117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1274914999413090021915030581 119523281194977189554534117)
            ·
              refine ⟨22410615224058223041475147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119523281194977189554534117 22410615224058223041475147)
              ·
                refine ⟨33615922836087334562212721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22410615224058223041475147 33615922836087334562212721)
                ·
                  refine ⟨25211942127065500921659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33615922836087334562212721 25211942127065500921659541)
                  ·
                    refine ⟨1181809787206195355702791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25211942127065500921659541 1181809787206195355702791)
                    ·
                      rfl

theorem cell23_6904699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_6904699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904699 prefixEnd_6904699 := by exact prefixLift 6904699
  have htrace : WordTrace (prefixWord ++ tailWord_6904699) baseStart_6904699 baseEnd_6904699 := by
    simpa [prefixWord, tailWord_6904699, baseEnd_6904699] using wordTrace_append hprefix tailTrace_6904699
  have hstable : (prefixWord ++ tailWord_6904699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904699).length < 2 ^ (prefixWord ++ tailWord_6904699).sum := by decide
  have hdescent : baseEnd_6904699 < baseStart_6904699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904740 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_6904740 : Nat := 118140960795 + 6904740 * 2 ^ 59
def prefixEnd_6904740 : Nat := 4983230072969 + 3 ^ 40 * 6904740 * 2
def baseEnd_6904740 : Nat := 3545450414325420406695685

theorem tailTrace_6904740 : CollatzResearch.WordTrace tailWord_6904740 prefixEnd_6904740 3545450414325420406695685 := by
  unfold tailWord_6904740
  simp only [CollatzResearch.WordTrace]
  refine ⟨125918278502656845276679837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167891038003542460368906449 125918278502656845276679837)
  ·
    refine ⟨47219354438496316978754939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125918278502656845276679837 47219354438496316978754939)
    ·
      refine ⟨70829031657744475468132409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47219354438496316978754939 70829031657744475468132409)
      ·
        refine ⟨53121773743308356601099307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70829031657744475468132409 53121773743308356601099307)
        ·
          refine ⟨79682660614962534901648961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53121773743308356601099307 79682660614962534901648961)
          ·
            refine ⟨59761995461221901176236721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79682660614962534901648961 59761995461221901176236721)
            ·
              refine ⟨44821496595916425882177541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59761995461221901176236721 44821496595916425882177541)
              ·
                refine ⟨8404030611734329852908289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44821496595916425882177541 8404030611734329852908289)
                ·
                  refine ⟨6303022958800747389681217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8404030611734329852908289 6303022958800747389681217)
                  ·
                    refine ⟨4727267219100560542260913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303022958800747389681217 4727267219100560542260913)
                    ·
                      refine ⟨3545450414325420406695685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727267219100560542260913 3545450414325420406695685)
                      ·
                        rfl

theorem cell23_6904740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_6904740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904740 prefixEnd_6904740 := by exact prefixLift 6904740
  have htrace : WordTrace (prefixWord ++ tailWord_6904740) baseStart_6904740 baseEnd_6904740 := by
    simpa [prefixWord, tailWord_6904740, baseEnd_6904740] using wordTrace_append hprefix tailTrace_6904740
  have hstable : (prefixWord ++ tailWord_6904740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904740).length < 2 ^ (prefixWord ++ tailWord_6904740).sum := by decide
  have hdescent : baseEnd_6904740 < baseStart_6904740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904759 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 7]
def baseStart_6904759 : Nat := 118140960795 + 6904759 * 2 ^ 59
def prefixEnd_6904759 : Nat := 4983230072969 + 3 ^ 40 * 6904759 * 2
def baseEnd_6904759 : Nat := 1181820056819285277452699

theorem tailTrace_6904759 : CollatzResearch.WordTrace tailWord_6904759 prefixEnd_6904759 1181820056819285277452699 := by
  unfold tailWord_6904759
  simp only [CollatzResearch.WordTrace]
  refine ⟨251837249992244856798301331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167891499994829904532200887 251837249992244856798301331)
  ·
    refine ⟨377755874988367285197451997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251837249992244856798301331 377755874988367285197451997)
    ·
      refine ⟨141658453120637731949044499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377755874988367285197451997 141658453120637731949044499)
      ·
        refine ⟨212487679680956597923566749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141658453120637731949044499 212487679680956597923566749)
        ·
          refine ⟨79682879880358724221337531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212487679680956597923566749 79682879880358724221337531)
          ·
            refine ⟨119524319820538086332006297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79682879880358724221337531 119524319820538086332006297)
            ·
              refine ⟨89643239865403564749004723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119524319820538086332006297 89643239865403564749004723)
              ·
                refine ⟨134464859798105347123507085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89643239865403564749004723 134464859798105347123507085)
                ·
                  refine ⟨50424322424289505171315157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134464859798105347123507085 50424322424289505171315157)
                  ·
                    refine ⟨1181820056819285277452699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50424322424289505171315157 1181820056819285277452699)
                    ·
                      rfl

theorem cell23_6904759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_6904759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904759 prefixEnd_6904759 := by exact prefixLift 6904759
  have htrace : WordTrace (prefixWord ++ tailWord_6904759) baseStart_6904759 baseEnd_6904759 := by
    simpa [prefixWord, tailWord_6904759, baseEnd_6904759] using wordTrace_append hprefix tailTrace_6904759
  have hstable : (prefixWord ++ tailWord_6904759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904759).length < 2 ^ (prefixWord ++ tailWord_6904759).sum := by decide
  have hdescent : baseEnd_6904759 < baseStart_6904759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904797 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 5]
def baseStart_6904797 : Nat := 118140960795 + 6904797 * 2 ^ 59
def prefixEnd_6904797 : Nat := 4983230072969 + 3 ^ 40 * 6904797 * 2
def baseEnd_6904797 : Nat := 393942186969191853742547

theorem tailTrace_6904797 : CollatzResearch.WordTrace tailWord_6904797 prefixEnd_6904797 393942186969191853742547 := by
  unfold tailWord_6904797
  simp only [CollatzResearch.WordTrace]
  refine ⟨251838635966107189288184645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167892423977404792858789763 251838635966107189288184645)
  ·
    refine ⟨47219744243645097991534621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251838635966107189288184645 47219744243645097991534621)
    ·
      refine ⟨17707404091366911746825483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47219744243645097991534621 17707404091366911746825483)
      ·
        refine ⟨26561106137050367620238225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17707404091366911746825483 26561106137050367620238225)
        ·
          refine ⟨19920829602787775715178669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26561106137050367620238225 19920829602787775715178669)
          ·
            refine ⟨7470311101045415893192001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19920829602787775715178669 7470311101045415893192001)
            ·
              refine ⟨5602733325784061919894001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470311101045415893192001 5602733325784061919894001)
              ·
                refine ⟨4202049994338046439920501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602733325784061919894001 4202049994338046439920501)
                ·
                  refine ⟨393942186969191853742547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202049994338046439920501 393942186969191853742547)
                  ·
                    rfl

theorem cell23_6904797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_6904797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904797 prefixEnd_6904797 := by exact prefixLift 6904797
  have htrace : WordTrace (prefixWord ++ tailWord_6904797) baseStart_6904797 baseEnd_6904797 := by
    simpa [prefixWord, tailWord_6904797, baseEnd_6904797] using wordTrace_append hprefix tailTrace_6904797
  have hstable : (prefixWord ++ tailWord_6904797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904797).length < 2 ^ (prefixWord ++ tailWord_6904797).sum := by decide
  have hdescent : baseEnd_6904797 < baseStart_6904797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904816 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_6904816 : Nat := 118140960795 + 6904816 * 2 ^ 59
def prefixEnd_6904816 : Nat := 4983230072969 + 3 ^ 40 * 6904816 * 2
def baseEnd_6904816 : Nat := 3545489438855162109345335

theorem tailTrace_6904816 : CollatzResearch.WordTrace tailWord_6904816 prefixEnd_6904816 3545489438855162109345335 := by
  unfold tailWord_6904816
  simp only [CollatzResearch.WordTrace]
  refine ⟨125919664476519177766563151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167892885968692237022084201 125919664476519177766563151)
  ·
    refine ⟨188879496714778766649844727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125919664476519177766563151 188879496714778766649844727)
    ·
      refine ⟨283319245072168149974767091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188879496714778766649844727 283319245072168149974767091)
      ·
        refine ⟨424978867608252224962150637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283319245072168149974767091 424978867608252224962150637)
        ·
          refine ⟨159367075353094584360806489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424978867608252224962150637 159367075353094584360806489)
          ·
            refine ⟨119525306514820938270604867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159367075353094584360806489 119525306514820938270604867)
            ·
              refine ⟨179287959772231407405907301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119525306514820938270604867 179287959772231407405907301)
              ·
                refine ⟨33616492457293388888607619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179287959772231407405907301 33616492457293388888607619)
                ·
                  refine ⟨50424738685940083332911429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33616492457293388888607619 50424738685940083332911429)
                  ·
                    refine ⟨9454638503613765624920893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50424738685940083332911429 9454638503613765624920893)
                    ·
                      refine ⟨3545489438855162109345335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454638503613765624920893 3545489438855162109345335)
                      ·
                        rfl

theorem cell23_6904816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_6904816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904816 prefixEnd_6904816 := by exact prefixLift 6904816
  have htrace : WordTrace (prefixWord ++ tailWord_6904816) baseStart_6904816 baseEnd_6904816 := by
    simpa [prefixWord, tailWord_6904816, baseEnd_6904816] using wordTrace_append hprefix tailTrace_6904816
  have hstable : (prefixWord ++ tailWord_6904816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904816).length < 2 ^ (prefixWord ++ tailWord_6904816).sum := by decide
  have hdescent : baseEnd_6904816 < baseStart_6904816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904819 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 12]
def baseStart_6904819 : Nat := 118140960795 + 6904819 * 2 ^ 59
def prefixEnd_6904819 : Nat := 4983230072969 + 3 ^ 40 * 6904819 * 2
def baseEnd_6904819 : Nat := 393943442144125066400869

theorem tailTrace_6904819 : CollatzResearch.WordTrace tailWord_6904819 prefixEnd_6904819 393943442144125066400869 := by
  unfold tailWord_6904819
  simp only [CollatzResearch.WordTrace]
  refine ⟨251839438372027487045485511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167892958914684991363657007 251839438372027487045485511)
  ·
    refine ⟨377759157558041230568228267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251839438372027487045485511 377759157558041230568228267)
    ·
      refine ⟨566638736337061845852342401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377759157558041230568228267 566638736337061845852342401)
      ·
        refine ⟨424979052252796384389256801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566638736337061845852342401 424979052252796384389256801)
        ·
          refine ⟨318734289189597288291942601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424979052252796384389256801 318734289189597288291942601)
          ·
            refine ⟨239050716892197966218956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318734289189597288291942601 239050716892197966218956951)
            ·
              refine ⟨358576075338296949328435427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239050716892197966218956951 358576075338296949328435427)
              ·
                refine ⟨537864113007445423992653141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358576075338296949328435427 537864113007445423992653141)
                ·
                  refine ⟨393943442144125066400869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 537864113007445423992653141 393943442144125066400869)
                  ·
                    rfl

theorem cell23_6904819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 12].length) (baseStart_6904819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904819 prefixEnd_6904819 := by exact prefixLift 6904819
  have htrace : WordTrace (prefixWord ++ tailWord_6904819) baseStart_6904819 baseEnd_6904819 := by
    simpa [prefixWord, tailWord_6904819, baseEnd_6904819] using wordTrace_append hprefix tailTrace_6904819
  have hstable : (prefixWord ++ tailWord_6904819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904819).length < 2 ^ (prefixWord ++ tailWord_6904819).sum := by decide
  have hdescent : baseEnd_6904819 < baseStart_6904819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904830 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6904830 : Nat := 118140960795 + 6904830 * 2 ^ 59
def prefixEnd_6904830 : Nat := 4983230072969 + 3 ^ 40 * 6904830 * 2
def baseEnd_6904830 : Nat := 3545496627584325054570271

theorem tailTrace_6904830 : CollatzResearch.WordTrace tailWord_6904830 prefixEnd_6904830 3545496627584325054570271 := by
  unfold tailWord_6904830
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479979946873454490516993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167893226383325090616090629 31479979946873454490516993)
  ·
    refine ⟨23609984960155090867887745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31479979946873454490516993 23609984960155090867887745)
    ·
      refine ⟨17707488720116318150915809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23609984960155090867887745 17707488720116318150915809)
      ·
        refine ⟨13280616540087238613186857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17707488720116318150915809 13280616540087238613186857)
        ·
          refine ⟨9960462405065428959890143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13280616540087238613186857 9960462405065428959890143)
          ·
            refine ⟨14940693607598143439835215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9960462405065428959890143 14940693607598143439835215)
            ·
              refine ⟨22411040411397215159752823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940693607598143439835215 22411040411397215159752823)
              ·
                refine ⟨33616560617095822739629235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22411040411397215159752823 33616560617095822739629235)
                ·
                  refine ⟨50424840925643734109443853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33616560617095822739629235 50424840925643734109443853)
                  ·
                    refine ⟨18909315347116400291041445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50424840925643734109443853 18909315347116400291041445)
                    ·
                      refine ⟨3545496627584325054570271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18909315347116400291041445 3545496627584325054570271)
                      ·
                        rfl

theorem cell23_6904830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6904830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904830 prefixEnd_6904830 := by exact prefixLift 6904830
  have htrace : WordTrace (prefixWord ++ tailWord_6904830) baseStart_6904830 baseEnd_6904830 := by
    simpa [prefixWord, tailWord_6904830, baseEnd_6904830] using wordTrace_append hprefix tailTrace_6904830
  have hstable : (prefixWord ++ tailWord_6904830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904830).length < 2 ^ (prefixWord ++ tailWord_6904830).sum := by decide
  have hdescent : baseEnd_6904830 < baseStart_6904830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904833 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_6904833 : Nat := 118140960795 + 6904833 * 2 ^ 59
def prefixEnd_6904833 : Nat := 4983230072969 + 3 ^ 40 * 6904833 * 2
def baseEnd_6904833 : Nat := 3545498168026288542832757

theorem tailTrace_6904833 : CollatzResearch.WordTrace tailWord_6904833 prefixEnd_6904833 3545498168026288542832757 := by
  unfold tailWord_6904833
  simp only [CollatzResearch.WordTrace]
  refine ⟨251839948993976767436495153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167893299329317844957663435 251839948993976767436495153)
  ·
    refine ⟨188879961745482575577371365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251839948993976767436495153 188879961745482575577371365)
    ·
      refine ⟨35414992827277982920757131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188879961745482575577371365 35414992827277982920757131)
      ·
        refine ⟨53122489240916974381135697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35414992827277982920757131 53122489240916974381135697)
        ·
          refine ⟨39841866930687730785851773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53122489240916974381135697 39841866930687730785851773)
          ·
            refine ⟨14940700099007899044694415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39841866930687730785851773 14940700099007899044694415)
            ·
              refine ⟨22411050148511848567041623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940700099007899044694415 22411050148511848567041623)
              ·
                refine ⟨33616575222767772850562435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22411050148511848567041623 33616575222767772850562435)
                ·
                  refine ⟨50424862834151659275843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33616575222767772850562435 50424862834151659275843653)
                  ·
                    refine ⟨9454661781403436114220685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50424862834151659275843653 9454661781403436114220685)
                    ·
                      refine ⟨3545498168026288542832757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454661781403436114220685 3545498168026288542832757)
                      ·
                        rfl

theorem cell23_6904833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_6904833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904833 prefixEnd_6904833 := by exact prefixLift 6904833
  have htrace : WordTrace (prefixWord ++ tailWord_6904833) baseStart_6904833 baseEnd_6904833 := by
    simpa [prefixWord, tailWord_6904833, baseEnd_6904833] using wordTrace_append hprefix tailTrace_6904833
  have hstable : (prefixWord ++ tailWord_6904833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904833).length < 2 ^ (prefixWord ++ tailWord_6904833).sum := by decide
  have hdescent : baseEnd_6904833 < baseStart_6904833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904840 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 1, 4]
def baseStart_6904840 : Nat := 118140960795 + 6904840 * 2 ^ 59
def prefixEnd_6904840 : Nat := 4983230072969 + 3 ^ 40 * 6904840 * 2
def baseEnd_6904840 : Nat := 1181833920796956671815075

theorem tailTrace_6904840 : CollatzResearch.WordTrace tailWord_6904840 prefixEnd_6904840 1181833920796956671815075 := by
  unfold tailWord_6904840
  simp only [CollatzResearch.WordTrace]
  refine ⟨125920102152475703815999987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167893469536634271754666649 125920102152475703815999987)
  ·
    refine ⟨188880153228713555723999981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125920102152475703815999987 188880153228713555723999981)
    ·
      refine ⟨70830057460767583396499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188880153228713555723999981 70830057460767583396499993)
      ·
        refine ⟨53122543095575687547374995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70830057460767583396499993 53122543095575687547374995)
        ·
          refine ⟨79683814643363531321062493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53122543095575687547374995 79683814643363531321062493)
          ·
            refine ⟨29881430491261324245398435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79683814643363531321062493 29881430491261324245398435)
            ·
              refine ⟨44822145736891986368097653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29881430491261324245398435 44822145736891986368097653)
              ·
                refine ⟨4202076162833623722009155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44822145736891986368097653 4202076162833623722009155)
                ·
                  refine ⟨6303114244250435583013733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202076162833623722009155 6303114244250435583013733)
                  ·
                    refine ⟨1181833920796956671815075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303114244250435583013733 1181833920796956671815075)
                    ·
                      rfl

theorem cell23_6904840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_6904840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904840 prefixEnd_6904840 := by exact prefixLift 6904840
  have htrace : WordTrace (prefixWord ++ tailWord_6904840) baseStart_6904840 baseEnd_6904840 := by
    simpa [prefixWord, tailWord_6904840, baseEnd_6904840] using wordTrace_append hprefix tailTrace_6904840
  have hstable : (prefixWord ++ tailWord_6904840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904840).length < 2 ^ (prefixWord ++ tailWord_6904840).sum := by decide
  have hdescent : baseEnd_6904840 < baseStart_6904840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904853 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 6]
def baseStart_6904853 : Nat := 118140960795 + 6904853 * 2 ^ 59
def prefixEnd_6904853 : Nat := 4983230072969 + 3 ^ 40 * 6904853 * 2
def baseEnd_6904853 : Nat := 393945381959930940509185

theorem tailTrace_6904853 : CollatzResearch.WordTrace tailWord_6904853 prefixEnd_6904853 393945381959930940509185 := by
  unfold tailWord_6904853
  simp only [CollatzResearch.WordTrace]
  refine ⟨251840678453904310852223213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167893785635936207234815475 251840678453904310852223213)
  ·
    refine ⟨94440254420214116569583705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251840678453904310852223213 94440254420214116569583705)
    ·
      refine ⟨70830190815160587427187779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94440254420214116569583705 70830190815160587427187779)
      ·
        refine ⟨106245286222740881140781669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70830190815160587427187779 106245286222740881140781669)
        ·
          refine ⟨19920991166763915213896563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106245286222740881140781669 19920991166763915213896563)
          ·
            refine ⟨29881486750145872820844845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19920991166763915213896563 29881486750145872820844845)
            ·
              refine ⟨11205557531304702307816817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29881486750145872820844845 11205557531304702307816817)
              ·
                refine ⟨8404168148478526730862613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11205557531304702307816817 8404168148478526730862613)
                ·
                  refine ⟨393945381959930940509185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8404168148478526730862613 393945381959930940509185)
                  ·
                    rfl

theorem cell23_6904853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_6904853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904853 prefixEnd_6904853 := by exact prefixLift 6904853
  have htrace : WordTrace (prefixWord ++ tailWord_6904853) baseStart_6904853 baseEnd_6904853 := by
    simpa [prefixWord, tailWord_6904853, baseEnd_6904853] using wordTrace_append hprefix tailTrace_6904853
  have hstable : (prefixWord ++ tailWord_6904853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904853).length < 2 ^ (prefixWord ++ tailWord_6904853).sum := by decide
  have hdescent : baseEnd_6904853 < baseStart_6904853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904856 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6904856 : Nat := 118140960795 + 6904856 * 2 ^ 59
def prefixEnd_6904856 : Nat := 4983230072969 + 3 ^ 40 * 6904856 * 2
def baseEnd_6904856 : Nat := 3545509978081341952845151

theorem tailTrace_6904856 : CollatzResearch.WordTrace tailWord_6904856 prefixEnd_6904856 3545509978081341952845151 := by
  unfold tailWord_6904856
  simp only [CollatzResearch.WordTrace]
  refine ⟨125920393936446721182291211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167893858581928961576388281 125920393936446721182291211)
  ·
    refine ⟨188880590904670081773436817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125920393936446721182291211 188880590904670081773436817)
    ·
      refine ⟨141660443178502561330077613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188880590904670081773436817 141660443178502561330077613)
      ·
        refine ⟨53122666191938460498779105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141660443178502561330077613 53122666191938460498779105)
        ·
          refine ⟨39841999643953845374084329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53122666191938460498779105 39841999643953845374084329)
          ·
            refine ⟨29881499732965384030563247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39841999643953845374084329 29881499732965384030563247)
            ·
              refine ⟨44822249599448076045844871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29881499732965384030563247 44822249599448076045844871)
              ·
                refine ⟨67233374399172114068767307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44822249599448076045844871 67233374399172114068767307)
                ·
                  refine ⟨100850061598758171103150961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67233374399172114068767307 100850061598758171103150961)
                  ·
                    refine ⟨75637546199068628327363221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100850061598758171103150961 75637546199068628327363221)
                    ·
                      refine ⟨3545509978081341952845151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75637546199068628327363221 3545509978081341952845151)
                      ·
                        rfl

theorem cell23_6904856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6904856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904856 prefixEnd_6904856 := by exact prefixLift 6904856
  have htrace : WordTrace (prefixWord ++ tailWord_6904856) baseStart_6904856 baseEnd_6904856 := by
    simpa [prefixWord, tailWord_6904856, baseEnd_6904856] using wordTrace_append hprefix tailTrace_6904856
  have hstable : (prefixWord ++ tailWord_6904856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904856).length < 2 ^ (prefixWord ++ tailWord_6904856).sum := by decide
  have hdescent : baseEnd_6904856 < baseStart_6904856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904896 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_6904896 : Nat := 118140960795 + 6904896 * 2 ^ 59
def prefixEnd_6904896 : Nat := 4983230072969 + 3 ^ 40 * 6904896 * 2
def baseEnd_6904896 : Nat := 1181843505769173932114989

theorem tailTrace_6904896 : CollatzResearch.WordTrace tailWord_6904896 prefixEnd_6904896 1181843505769173932114989 := by
  unfold tailWord_6904896
  simp only [CollatzResearch.WordTrace]
  refine ⟨125921123396374264598019271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167894831195165686130692361 125921123396374264598019271)
  ·
    refine ⟨188881685094561396897028907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125921123396374264598019271 188881685094561396897028907)
    ·
      refine ⟨283322527641842095345543361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188881685094561396897028907 283322527641842095345543361)
      ·
        refine ⟨212491895731381571509157521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283322527641842095345543361 212491895731381571509157521)
        ·
          refine ⟨159368921798536178631868141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212491895731381571509157521 159368921798536178631868141)
          ·
            refine ⟨59763345674451066986950553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159368921798536178631868141 59763345674451066986950553)
            ·
              refine ⟨44822509255838300240212915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59763345674451066986950553 44822509255838300240212915)
              ·
                refine ⟨67233763883757450360319373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44822509255838300240212915 67233763883757450360319373)
                ·
                  refine ⟨25212661456409043885119765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67233763883757450360319373 25212661456409043885119765)
                  ·
                    refine ⟨1181843505769173932114989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25212661456409043885119765 1181843505769173932114989)
                    ·
                      rfl

theorem cell23_6904896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_6904896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904896 prefixEnd_6904896 := by exact prefixLift 6904896
  have htrace : WordTrace (prefixWord ++ tailWord_6904896) baseStart_6904896 baseEnd_6904896 := by
    simpa [prefixWord, tailWord_6904896, baseEnd_6904896] using wordTrace_append hprefix tailTrace_6904896
  have hstable : (prefixWord ++ tailWord_6904896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904896).length < 2 ^ (prefixWord ++ tailWord_6904896).sum := by decide
  have hdescent : baseEnd_6904896 < baseStart_6904896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904913 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_6904913 : Nat := 118140960795 + 6904913 * 2 ^ 59
def prefixEnd_6904913 : Nat := 4983230072969 + 3 ^ 40 * 6904913 * 2
def baseEnd_6904913 : Nat := 1181846415492882743277463

theorem tailTrace_6904913 : CollatzResearch.WordTrace tailWord_6904913 prefixEnd_6904913 1181846415492882743277463 := by
  unfold tailWord_6904913
  simp only [CollatzResearch.WordTrace]
  refine ⟨251842866833686941099407393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167895244555791294066271595 251842866833686941099407393)
  ·
    refine ⟨188882150125265205824555545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251842866833686941099407393 188882150125265205824555545)
    ·
      refine ⟨141661612593948904368416659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188882150125265205824555545 141661612593948904368416659)
      ·
        refine ⟨212492418890923356552624989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141661612593948904368416659 212492418890923356552624989)
        ·
          refine ⟨79684657084096258707234371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212492418890923356552624989 79684657084096258707234371)
          ·
            refine ⟨119526985626144388060851557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79684657084096258707234371 119526985626144388060851557)
            ·
              refine ⟨22411309804902072761409667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119526985626144388060851557 22411309804902072761409667)
              ·
                refine ⟨33616964707353109142114501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22411309804902072761409667 33616964707353109142114501)
                ·
                  refine ⟨6303180882628707964146469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33616964707353109142114501 6303180882628707964146469)
                  ·
                    refine ⟨1181846415492882743277463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303180882628707964146469 1181846415492882743277463)
                    ·
                      rfl

theorem cell23_6904913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_6904913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904913 prefixEnd_6904913 := by exact prefixLift 6904913
  have htrace : WordTrace (prefixWord ++ tailWord_6904913) baseStart_6904913 baseEnd_6904913 := by
    simpa [prefixWord, tailWord_6904913, baseEnd_6904913] using wordTrace_append hprefix tailTrace_6904913
  have hstable : (prefixWord ++ tailWord_6904913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904913).length < 2 ^ (prefixWord ++ tailWord_6904913).sum := by decide
  have hdescent : baseEnd_6904913 < baseStart_6904913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904933 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_6904933 : Nat := 118140960795 + 6904933 * 2 ^ 59
def prefixEnd_6904933 : Nat := 4983230072969 + 3 ^ 40 * 6904933 * 2
def baseEnd_6904933 : Nat := 3545549516091738151582297

theorem tailTrace_6904933 : CollatzResearch.WordTrace tailWord_6904933 prefixEnd_6904933 3545549516091738151582297 := by
  unfold tailWord_6904933
  simp only [CollatzResearch.WordTrace]
  refine ⟨251843596293614484515135453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167895730862409656343423635 251843596293614484515135453)
  ·
    refine ⟨94441348610105431693175795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251843596293614484515135453 94441348610105431693175795)
    ·
      refine ⟨141662022915158147539763693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94441348610105431693175795 141662022915158147539763693)
      ·
        refine ⟨53123258593184305327411385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141662022915158147539763693 53123258593184305327411385)
        ·
          refine ⟨39842443944888228995558539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53123258593184305327411385 39842443944888228995558539)
          ·
            refine ⟨59763665917332343493337809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39842443944888228995558539 59763665917332343493337809)
            ·
              refine ⟨44822749437999257620003357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59763665917332343493337809 44822749437999257620003357)
              ·
                refine ⟨16808531039249721607501259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44822749437999257620003357 16808531039249721607501259)
                ·
                  refine ⟨25212796558874582411251889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16808531039249721607501259 25212796558874582411251889)
                  ·
                    refine ⟨18909597419155936808438917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25212796558874582411251889 18909597419155936808438917)
                    ·
                      refine ⟨3545549516091738151582297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18909597419155936808438917 3545549516091738151582297)
                      ·
                        rfl

theorem cell23_6904933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_6904933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904933 prefixEnd_6904933 := by exact prefixLift 6904933
  have htrace : WordTrace (prefixWord ++ tailWord_6904933) baseStart_6904933 baseEnd_6904933 := by
    simpa [prefixWord, tailWord_6904933, baseEnd_6904933] using wordTrace_append hprefix tailTrace_6904933
  have hstable : (prefixWord ++ tailWord_6904933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904933).length < 2 ^ (prefixWord ++ tailWord_6904933).sum := by decide
  have hdescent : baseEnd_6904933 < baseStart_6904933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904950 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6904950 : Nat := 118140960795 + 6904950 * 2 ^ 59
def prefixEnd_6904950 : Nat := 4983230072969 + 3 ^ 40 * 6904950 * 2
def baseEnd_6904950 : Nat := 3545558245262864585069719

theorem tailTrace_6904950 : CollatzResearch.WordTrace tailWord_6904950 prefixEnd_6904950 3545558245262864585069719 := by
  unfold tailWord_6904950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15740263520909556026156519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167896144223035264279002869 15740263520909556026156519)
  ·
    refine ⟨23610395281364334039234779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15740263520909556026156519 23610395281364334039234779)
    ·
      refine ⟨35415592922046501058852169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23610395281364334039234779 35415592922046501058852169)
      ·
        refine ⟨26561694691534875794139127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35415592922046501058852169 26561694691534875794139127)
        ·
          refine ⟨39842542037302313691208691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26561694691534875794139127 39842542037302313691208691)
          ·
            refine ⟨59763813055953470536813037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39842542037302313691208691 59763813055953470536813037)
            ·
              refine ⟨22411429895982551451304889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59763813055953470536813037 22411429895982551451304889)
              ·
                refine ⟨16808572421986913588478667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22411429895982551451304889 16808572421986913588478667)
                ·
                  refine ⟨25212858632980370382718001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16808572421986913588478667 25212858632980370382718001)
                  ·
                    refine ⟨18909643974735277787038501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25212858632980370382718001 18909643974735277787038501)
                    ·
                      refine ⟨3545558245262864585069719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18909643974735277787038501 3545558245262864585069719)
                      ·
                        rfl

theorem cell23_6904950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6904950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904950 prefixEnd_6904950 := by exact prefixLift 6904950
  have htrace : WordTrace (prefixWord ++ tailWord_6904950) baseStart_6904950 baseEnd_6904950 := by
    simpa [prefixWord, tailWord_6904950, baseEnd_6904950] using wordTrace_append hprefix tailTrace_6904950
  have hstable : (prefixWord ++ tailWord_6904950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904950).length < 2 ^ (prefixWord ++ tailWord_6904950).sum := by decide
  have hdescent : baseEnd_6904950 < baseStart_6904950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904957 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_6904957 : Nat := 118140960795 + 6904957 * 2 ^ 59
def prefixEnd_6904957 : Nat := 4983230072969 + 3 ^ 40 * 6904957 * 2
def baseEnd_6904957 : Nat := 3545561839627446057682187

theorem tailTrace_6904957 : CollatzResearch.WordTrace tailWord_6904957 prefixEnd_6904957 3545561839627446057682187 := by
  unfold tailWord_6904957
  simp only [CollatzResearch.WordTrace]
  refine ⟨251844471645527536614009125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167896314430351691076006083 251844471645527536614009125)
  ·
    refine ⟨47220838433536413115126711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251844471645527536614009125 47220838433536413115126711)
    ·
      refine ⟨70831257650304619672690067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47220838433536413115126711 70831257650304619672690067)
      ·
        refine ⟨106246886475456929509035101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70831257650304619672690067 106246886475456929509035101)
        ·
          refine ⟨39842582428296348565888163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106246886475456929509035101 39842582428296348565888163)
          ·
            refine ⟨59763873642444522848832245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39842582428296348565888163 59763873642444522848832245)
            ·
              refine ⟨5602863153979174017078023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59763873642444522848832245 5602863153979174017078023)
              ·
                refine ⟨8404294730968761025617035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602863153979174017078023 8404294730968761025617035)
                ·
                  refine ⟨12606442096453141538425553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404294730968761025617035 12606442096453141538425553)
                  ·
                    refine ⟨9454831572339856153819165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12606442096453141538425553 9454831572339856153819165)
                    ·
                      refine ⟨3545561839627446057682187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9454831572339856153819165 3545561839627446057682187)
                      ·
                        rfl

theorem cell23_6904957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_6904957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904957 prefixEnd_6904957 := by exact prefixLift 6904957
  have htrace : WordTrace (prefixWord ++ tailWord_6904957) baseStart_6904957 baseEnd_6904957 := by
    simpa [prefixWord, tailWord_6904957, baseEnd_6904957] using wordTrace_append hprefix tailTrace_6904957
  have hstable : (prefixWord ++ tailWord_6904957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904957).length < 2 ^ (prefixWord ++ tailWord_6904957).sum := by decide
  have hdescent : baseEnd_6904957 < baseStart_6904957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6904993 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6904993 : Nat := 118140960795 + 6904993 * 2 ^ 59
def prefixEnd_6904993 : Nat := 4983230072969 + 3 ^ 40 * 6904993 * 2
def baseEnd_6904993 : Nat := 3545580324931007916832021

theorem tailTrace_6904993 : CollatzResearch.WordTrace tailWord_6904993 prefixEnd_6904993 3545580324931007916832021 := by
  unfold tailWord_6904993
  simp only [CollatzResearch.WordTrace]
  refine ⟨251845784673397114762319633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167897189782264743174879755 251845784673397114762319633)
  ·
    refine ⟨188884338505047836071739725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251845784673397114762319633 188884338505047836071739725)
    ·
      refine ⟨70831626939392938526902397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188884338505047836071739725 70831626939392938526902397)
      ·
        refine ⟨26561860102272351947588399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70831626939392938526902397 26561860102272351947588399)
        ·
          refine ⟨39842790153408527921382599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26561860102272351947588399 39842790153408527921382599)
          ·
            refine ⟨59764185230112791882073899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39842790153408527921382599 59764185230112791882073899)
            ·
              refine ⟨89646277845169187823110849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59764185230112791882073899 89646277845169187823110849)
              ·
                refine ⟨67234708383876890867333137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89646277845169187823110849 67234708383876890867333137)
                ·
                  refine ⟨50426031287907668150499853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67234708383876890867333137 50426031287907668150499853)
                  ·
                    refine ⟨18909761732965375556437445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50426031287907668150499853 18909761732965375556437445)
                    ·
                      refine ⟨3545580324931007916832021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18909761732965375556437445 3545580324931007916832021)
                      ·
                        rfl

theorem cell23_6904993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6904993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6904993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6904993 prefixEnd_6904993 := by exact prefixLift 6904993
  have htrace : WordTrace (prefixWord ++ tailWord_6904993) baseStart_6904993 baseEnd_6904993 := by
    simpa [prefixWord, tailWord_6904993, baseEnd_6904993] using wordTrace_append hprefix tailTrace_6904993
  have hstable : (prefixWord ++ tailWord_6904993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6904993).length < 2 ^ (prefixWord ++ tailWord_6904993).sum := by decide
  have hdescent : baseEnd_6904993 < baseStart_6904993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6904993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905023 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_6905023 : Nat := 118140960795 + 6905023 * 2 ^ 59
def prefixEnd_6905023 : Nat := 4983230072969 + 3 ^ 40 * 6905023 * 2
def baseEnd_6905023 : Nat := 3545595729350642799456883

theorem tailTrace_6905023 : CollatzResearch.WordTrace tailWord_6905023 prefixEnd_6905023 3545595729350642799456883 := by
  unfold tailWord_6905023
  simp only [CollatzResearch.WordTrace]
  refine ⟨251846878863288429885911723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167897919242192286590607815 251846878863288429885911723)
  ·
    refine ⟨377770318294932644828867585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251846878863288429885911723 377770318294932644828867585)
    ·
      refine ⟨283327738721199483621650689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377770318294932644828867585 283327738721199483621650689)
      ·
        refine ⟨212495804040899612716238017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283327738721199483621650689 212495804040899612716238017)
        ·
          refine ⟨159371853030674709537178513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212495804040899612716238017 159371853030674709537178513)
          ·
            refine ⟨119528889773006032152883885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159371853030674709537178513 119528889773006032152883885)
            ·
              refine ⟨44823333664877262057331457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119528889773006032152883885 44823333664877262057331457)
              ·
                refine ⟨33617500248657946542998593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44823333664877262057331457 33617500248657946542998593)
                ·
                  refine ⟨25213125186493459907248945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33617500248657946542998593 25213125186493459907248945)
                  ·
                    refine ⟨18909843889870094930436709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25213125186493459907248945 18909843889870094930436709)
                    ·
                      refine ⟨3545595729350642799456883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18909843889870094930436709 3545595729350642799456883)
                      ·
                        rfl

theorem cell23_6905023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_6905023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905023 prefixEnd_6905023 := by exact prefixLift 6905023
  have htrace : WordTrace (prefixWord ++ tailWord_6905023) baseStart_6905023 baseEnd_6905023 := by
    simpa [prefixWord, tailWord_6905023, baseEnd_6905023] using wordTrace_append hprefix tailTrace_6905023
  have hstable : (prefixWord ++ tailWord_6905023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905023).length < 2 ^ (prefixWord ++ tailWord_6905023).sum := by decide
  have hdescent : baseEnd_6905023 < baseStart_6905023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905027 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 2, 2, 2]
def baseStart_6905027 : Nat := 118140960795 + 6905027 * 2 ^ 59
def prefixEnd_6905027 : Nat := 4983230072969 + 3 ^ 40 * 6905027 * 2
def baseEnd_6905027 : Nat := 3545597783273260783806865

theorem tailTrace_6905027 : CollatzResearch.WordTrace tailWord_6905027 prefixEnd_6905027 3545597783273260783806865 := by
  unfold tailWord_6905027
  simp only [CollatzResearch.WordTrace]
  refine ⟨251847024755273938569057335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167898016503515959046038223 251847024755273938569057335)
  ·
    refine ⟨377770537132910907853586003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251847024755273938569057335 377770537132910907853586003)
    ·
      refine ⟨566655805699366361780379005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377770537132910907853586003 566655805699366361780379005)
      ·
        refine ⟨212495927137262385667642127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566655805699366361780379005 212495927137262385667642127)
        ·
          refine ⟨318743890705893578501463191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212495927137262385667642127 318743890705893578501463191)
          ·
            refine ⟨478115836058840367752194787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318743890705893578501463191 478115836058840367752194787)
            ·
              refine ⟨717173754088260551628292181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478115836058840367752194787 717173754088260551628292181)
              ·
                refine ⟨8404379930721803339394049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 717173754088260551628292181 8404379930721803339394049)
                ·
                  refine ⟨6303284948041352504545537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8404379930721803339394049 6303284948041352504545537)
                  ·
                    refine ⟨4727463711031014378409153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303284948041352504545537 4727463711031014378409153)
                    ·
                      refine ⟨3545597783273260783806865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727463711031014378409153 3545597783273260783806865)
                      ·
                        rfl

theorem cell23_6905027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_6905027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905027 prefixEnd_6905027 := by exact prefixLift 6905027
  have htrace : WordTrace (prefixWord ++ tailWord_6905027) baseStart_6905027 baseEnd_6905027 := by
    simpa [prefixWord, tailWord_6905027, baseEnd_6905027] using wordTrace_append hprefix tailTrace_6905027
  have hstable : (prefixWord ++ tailWord_6905027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905027).length < 2 ^ (prefixWord ++ tailWord_6905027).sum := by decide
  have hdescent : baseEnd_6905027 < baseStart_6905027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905067 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 5]
def baseStart_6905067 : Nat := 118140960795 + 6905067 * 2 ^ 59
def prefixEnd_6905067 : Nat := 4983230072969 + 3 ^ 40 * 6905067 * 2
def baseEnd_6905067 : Nat := 393957591388826736367409

theorem tailTrace_6905067 : CollatzResearch.WordTrace tailWord_6905067 prefixEnd_6905067 393957591388826736367409 := by
  unfold tailWord_6905067
  simp only [CollatzResearch.WordTrace]
  refine ⟨251848483675129025400513455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167898989116752683600342303 251848483675129025400513455)
  ·
    refine ⟨377772725512693538100770183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251848483675129025400513455 377772725512693538100770183)
    ·
      refine ⟨566659088269040307151155275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377772725512693538100770183 566659088269040307151155275)
      ·
        refine ⟨849988632403560460726732913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566659088269040307151155275 849988632403560460726732913)
        ·
          refine ⟨637491474302670345545049685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849988632403560460726732913 637491474302670345545049685)
          ·
            refine ⟨7470603214484418111856051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 637491474302670345545049685 7470603214484418111856051)
            ·
              refine ⟨11205904821726627167784077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470603214484418111856051 11205904821726627167784077)
              ·
                refine ⟨4202214308147485187919029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11205904821726627167784077 4202214308147485187919029)
                ·
                  refine ⟨393957591388826736367409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202214308147485187919029 393957591388826736367409)
                  ·
                    rfl

theorem cell23_6905067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 5].length) (baseStart_6905067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905067 prefixEnd_6905067 := by exact prefixLift 6905067
  have htrace : WordTrace (prefixWord ++ tailWord_6905067) baseStart_6905067 baseEnd_6905067 := by
    simpa [prefixWord, tailWord_6905067, baseEnd_6905067] using wordTrace_append hprefix tailTrace_6905067
  have hstable : (prefixWord ++ tailWord_6905067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905067).length < 2 ^ (prefixWord ++ tailWord_6905067).sum := by decide
  have hdescent : baseEnd_6905067 < baseStart_6905067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905073 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_6905073 : Nat := 118140960795 + 6905073 * 2 ^ 59
def prefixEnd_6905073 : Nat := 4983230072969 + 3 ^ 40 * 6905073 * 2
def baseEnd_6905073 : Nat := 3545621403383367603831653

theorem tailTrace_6905073 : CollatzResearch.WordTrace tailWord_6905073 prefixEnd_6905073 3545621403383367603831653 := by
  unfold tailWord_6905073
  simp only [CollatzResearch.WordTrace]
  refine ⟨251848702513107288425231873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167899135008738192283487915 251848702513107288425231873)
  ·
    refine ⟨188886526884830466318923905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251848702513107288425231873 188886526884830466318923905)
    ·
      refine ⟨141664895163622849739192929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188886526884830466318923905 141664895163622849739192929)
      ·
        refine ⟨106248671372717137304394697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141664895163622849739192929 106248671372717137304394697)
        ·
          refine ⟨79686503529537852978296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106248671372717137304394697 79686503529537852978296023)
          ·
            refine ⟨119529755294306779467444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79686503529537852978296023 119529755294306779467444035)
            ·
              refine ⟨179294632941460169201166053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119529755294306779467444035 179294632941460169201166053)
              ·
                refine ⟨33617743676523781725218635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179294632941460169201166053 33617743676523781725218635)
                ·
                  refine ⟨50426615514785672587827953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33617743676523781725218635 50426615514785672587827953)
                  ·
                    refine ⟨37819961636089254440870965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50426615514785672587827953 37819961636089254440870965)
                    ·
                      refine ⟨3545621403383367603831653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37819961636089254440870965 3545621403383367603831653)
                      ·
                        rfl

theorem cell23_6905073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_6905073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905073 prefixEnd_6905073 := by exact prefixLift 6905073
  have htrace : WordTrace (prefixWord ++ tailWord_6905073) baseStart_6905073 baseEnd_6905073 := by
    simpa [prefixWord, tailWord_6905073, baseEnd_6905073] using wordTrace_append hprefix tailTrace_6905073
  have hstable : (prefixWord ++ tailWord_6905073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905073).length < 2 ^ (prefixWord ++ tailWord_6905073).sum := by decide
  have hdescent : baseEnd_6905073 < baseStart_6905073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905084 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 5]
def baseStart_6905084 : Nat := 118140960795 + 6905084 * 2 ^ 59
def prefixEnd_6905084 : Nat := 4983230072969 + 3 ^ 40 * 6905084 * 2
def baseEnd_6905084 : Nat := 393958561296729673421567

theorem tailTrace_6905084 : CollatzResearch.WordTrace tailWord_6905084 prefixEnd_6905084 393958561296729673421567 := by
  unfold tailWord_6905084
  simp only [CollatzResearch.WordTrace]
  refine ⟨125924551858033718651941153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167899402477378291535921537 125924551858033718651941153)
  ·
    refine ⟨94443413893525288988955865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125924551858033718651941153 94443413893525288988955865)
    ·
      refine ⟨70832560420143966741716899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94443413893525288988955865 70832560420143966741716899)
      ·
        refine ⟨106248840630215950112575349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70832560420143966741716899 106248840630215950112575349)
        ·
          refine ⟨9960828809082745323053939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106248840630215950112575349 9960828809082745323053939)
          ·
            refine ⟨14941243213624117984580909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9960828809082745323053939 14941243213624117984580909)
            ·
              refine ⟨5602966205109044244217841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14941243213624117984580909 5602966205109044244217841)
              ·
                refine ⟨4202224653831783183163381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602966205109044244217841 4202224653831783183163381)
                ·
                  refine ⟨393958561296729673421567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202224653831783183163381 393958561296729673421567)
                  ·
                    rfl

theorem cell23_6905084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_6905084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905084 prefixEnd_6905084 := by exact prefixLift 6905084
  have htrace : WordTrace (prefixWord ++ tailWord_6905084) baseStart_6905084 baseEnd_6905084 := by
    simpa [prefixWord, tailWord_6905084, baseEnd_6905084] using wordTrace_append hprefix tailTrace_6905084
  have hstable : (prefixWord ++ tailWord_6905084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905084).length < 2 ^ (prefixWord ++ tailWord_6905084).sum := by decide
  have hdescent : baseEnd_6905084 < baseStart_6905084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905117 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6905117 : Nat := 118140960795 + 6905117 * 2 ^ 59
def prefixEnd_6905117 : Nat := 4983230072969 + 3 ^ 40 * 6905117 * 2
def baseEnd_6905117 : Nat := 3545643996532165431681451

theorem tailTrace_6905117 : CollatzResearch.WordTrace tailWord_6905117 prefixEnd_6905117 3545643996532165431681451 := by
  unfold tailWord_6905117
  simp only [CollatzResearch.WordTrace]
  refine ⟨251850307324947883939833605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167900204883298589293222403 251850307324947883939833605)
  ·
    refine ⟨47221932623427728238718801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251850307324947883939833605 47221932623427728238718801)
    ·
      refine ⟨35416449467570796179039101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47221932623427728238718801 35416449467570796179039101)
      ·
        refine ⟨13281168550339048567139663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35416449467570796179039101 13281168550339048567139663)
        ·
          refine ⟨19921752825508572850709495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13281168550339048567139663 19921752825508572850709495)
          ·
            refine ⟨29882629238262859276064243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19921752825508572850709495 29882629238262859276064243)
            ·
              refine ⟨44823943857394288914096365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29882629238262859276064243 44823943857394288914096365)
              ·
                refine ⟨16808978946522858342786137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44823943857394288914096365 16808978946522858342786137)
                ·
                  refine ⟨12606734209892143757089603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16808978946522858342786137 12606734209892143757089603)
                  ·
                    refine ⟨18910101314838215635634405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12606734209892143757089603 18910101314838215635634405)
                    ·
                      refine ⟨3545643996532165431681451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18910101314838215635634405 3545643996532165431681451)
                      ·
                        rfl

theorem cell23_6905117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6905117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905117 prefixEnd_6905117 := by exact prefixLift 6905117
  have htrace : WordTrace (prefixWord ++ tailWord_6905117) baseStart_6905117 baseEnd_6905117 := by
    simpa [prefixWord, tailWord_6905117, baseEnd_6905117] using wordTrace_append hprefix tailTrace_6905117
  have hstable : (prefixWord ++ tailWord_6905117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905117).length < 2 ^ (prefixWord ++ tailWord_6905117).sum := by decide
  have hdescent : baseEnd_6905117 < baseStart_6905117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905137 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_6905137 : Nat := 118140960795 + 6905137 * 2 ^ 59
def prefixEnd_6905137 : Nat := 4983230072969 + 3 ^ 40 * 6905137 * 2
def baseEnd_6905137 : Nat := 3545654266145255353431359

theorem tailTrace_6905137 : CollatzResearch.WordTrace tailWord_6905137 prefixEnd_6905137 3545654266145255353431359 := by
  unfold tailWord_6905137
  simp only [CollatzResearch.WordTrace]
  refine ⟨251851036784875427355561665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167900691189916951570374443 251851036784875427355561665)
  ·
    refine ⟨188888277588656570516671249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251851036784875427355561665 188888277588656570516671249)
    ·
      refine ⟨141666208191492427887503437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188888277588656570516671249 141666208191492427887503437)
      ·
        refine ⟨53124828071809660457813789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141666208191492427887503437 53124828071809660457813789)
        ·
          refine ⟨19921810526928622671680171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53124828071809660457813789 19921810526928622671680171)
          ·
            refine ⟨29882715790392934007520257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19921810526928622671680171 29882715790392934007520257)
            ·
              refine ⟨22412036842794700505640193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29882715790392934007520257 22412036842794700505640193)
              ·
                refine ⟨16809027632096025379230145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22412036842794700505640193 16809027632096025379230145)
                ·
                  refine ⟨12606770724072019034422609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16809027632096025379230145 12606770724072019034422609)
                  ·
                    refine ⟨9455078043054014275816957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12606770724072019034422609 9455078043054014275816957)
                    ·
                      refine ⟨3545654266145255353431359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9455078043054014275816957 3545654266145255353431359)
                      ·
                        rfl

theorem cell23_6905137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_6905137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905137 prefixEnd_6905137 := by exact prefixLift 6905137
  have htrace : WordTrace (prefixWord ++ tailWord_6905137) baseStart_6905137 baseEnd_6905137 := by
    simpa [prefixWord, tailWord_6905137, baseEnd_6905137] using wordTrace_append hprefix tailTrace_6905137
  have hstable : (prefixWord ++ tailWord_6905137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905137).length < 2 ^ (prefixWord ++ tailWord_6905137).sum := by decide
  have hdescent : baseEnd_6905137 < baseStart_6905137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905163 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_6905163 : Nat := 118140960795 + 6905163 * 2 ^ 59
def prefixEnd_6905163 : Nat := 4983230072969 + 3 ^ 40 * 6905163 * 2
def baseEnd_6905163 : Nat := 3545667616642272251706239

theorem tailTrace_6905163 : CollatzResearch.WordTrace tailWord_6905163 prefixEnd_6905163 3545667616642272251706239 := by
  unfold tailWord_6905163
  simp only [CollatzResearch.WordTrace]
  refine ⟨251851985082781233796008143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167901323388520822530672095 251851985082781233796008143)
  ·
    refine ⟨377777977624171850694012215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251851985082781233796008143 377777977624171850694012215)
    ·
      refine ⟨566666966436257776041018323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377777977624171850694012215 566666966436257776041018323)
      ·
        refine ⟨850000449654386664061527485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566666966436257776041018323 850000449654386664061527485)
        ·
          refine ⟨318750168620394999023072807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 850000449654386664061527485 318750168620394999023072807)
          ·
            refine ⟨478125252930592498534609211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318750168620394999023072807 478125252930592498534609211)
            ·
              refine ⟨717187879395888747801913817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478125252930592498534609211 717187879395888747801913817)
              ·
                refine ⟨537890909546916560851435363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717187879395888747801913817 537890909546916560851435363)
                ·
                  refine ⟨806836364320374841277153045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537890909546916560851435363 806836364320374841277153045)
                  ·
                    refine ⟨37820454577517570684866549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 806836364320374841277153045 37820454577517570684866549)
                    ·
                      refine ⟨3545667616642272251706239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37820454577517570684866549 3545667616642272251706239)
                      ·
                        rfl

theorem cell23_6905163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_6905163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905163 prefixEnd_6905163 := by exact prefixLift 6905163
  have htrace : WordTrace (prefixWord ++ tailWord_6905163) baseStart_6905163 baseEnd_6905163 := by
    simpa [prefixWord, tailWord_6905163, baseEnd_6905163] using wordTrace_append hprefix tailTrace_6905163
  have hstable : (prefixWord ++ tailWord_6905163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905163).length < 2 ^ (prefixWord ++ tailWord_6905163).sum := by decide
  have hdescent : baseEnd_6905163 < baseStart_6905163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905187 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 1, 5]
def baseStart_6905187 : Nat := 118140960795 + 6905187 * 2 ^ 59
def prefixEnd_6905187 : Nat := 4983230072969 + 3 ^ 40 * 6905187 * 2
def baseEnd_6905187 : Nat := 1181893313392660052602043

theorem tailTrace_6905187 : CollatzResearch.WordTrace tailWord_6905187 prefixEnd_6905187 1181893313392660052602043 := by
  unfold tailWord_6905187
  simp only [CollatzResearch.WordTrace]
  refine ⟨251852860434694285894881815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167901906956462857263254543 251852860434694285894881815)
  ·
    refine ⟨377779290652041428842322723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251852860434694285894881815 377779290652041428842322723)
    ·
      refine ⟨566668935978062143263484085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377779290652041428842322723 566668935978062143263484085)
      ·
        refine ⟨53125212747943325930951633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 566668935978062143263484085 53125212747943325930951633)
        ·
          refine ⟨39843909560957494448213725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53125212747943325930951633 39843909560957494448213725)
          ·
            refine ⟨14941466085359060418080147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39843909560957494448213725 14941466085359060418080147)
            ·
              refine ⟨22412199128038590627120221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14941466085359060418080147 22412199128038590627120221)
              ·
                refine ⟨8404574673014471485170083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22412199128038590627120221 8404574673014471485170083)
                ·
                  refine ⟨12606862009521707227755125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404574673014471485170083 12606862009521707227755125)
                  ·
                    refine ⟨1181893313392660052602043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12606862009521707227755125 1181893313392660052602043)
                    ·
                      rfl

theorem cell23_6905187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 5].length) (baseStart_6905187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905187 prefixEnd_6905187 := by exact prefixLift 6905187
  have htrace : WordTrace (prefixWord ++ tailWord_6905187) baseStart_6905187 baseEnd_6905187 := by
    simpa [prefixWord, tailWord_6905187, baseEnd_6905187] using wordTrace_append hprefix tailTrace_6905187
  have hstable : (prefixWord ++ tailWord_6905187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905187).length < 2 ^ (prefixWord ++ tailWord_6905187).sum := by decide
  have hdescent : baseEnd_6905187 < baseStart_6905187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905210 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_6905210 : Nat := 118140960795 + 6905210 * 2 ^ 59
def prefixEnd_6905210 : Nat := 4983230072969 + 3 ^ 40 * 6905210 * 2
def baseEnd_6905210 : Nat := 3545691750233033567818523

theorem tailTrace_6905210 : CollatzResearch.WordTrace tailWord_6905210 prefixEnd_6905210 3545691750233033567818523 := by
  unfold tailWord_6905210
  simp only [CollatzResearch.WordTrace]
  refine ⟨62963424828402740205742271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167902466209073973881979389 62963424828402740205742271)
  ·
    refine ⟨94445137242604110308613407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62963424828402740205742271 94445137242604110308613407)
    ·
      refine ⟨141667705863906165462920111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94445137242604110308613407 141667705863906165462920111)
      ·
        refine ⟨212501558795859248194380167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141667705863906165462920111 212501558795859248194380167)
        ·
          refine ⟨318752338193788872291570251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212501558795859248194380167 318752338193788872291570251)
          ·
            refine ⟨478128507290683308437355377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318752338193788872291570251 478128507290683308437355377)
            ·
              refine ⟨358596380468012481328016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478128507290683308437355377 358596380468012481328016533)
              ·
                refine ⟨16809205334438085062250775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358596380468012481328016533 16809205334438085062250775)
                ·
                  refine ⟨25213808001657127593376163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16809205334438085062250775 25213808001657127593376163)
                  ·
                    refine ⟨37820712002485691390064245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25213808001657127593376163 37820712002485691390064245)
                    ·
                      refine ⟨3545691750233033567818523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37820712002485691390064245 3545691750233033567818523)
                      ·
                        rfl

theorem cell23_6905210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_6905210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905210 prefixEnd_6905210 := by exact prefixLift 6905210
  have htrace : WordTrace (prefixWord ++ tailWord_6905210) baseStart_6905210 baseEnd_6905210 := by
    simpa [prefixWord, tailWord_6905210, baseEnd_6905210] using wordTrace_append hprefix tailTrace_6905210
  have hstable : (prefixWord ++ tailWord_6905210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905210).length < 2 ^ (prefixWord ++ tailWord_6905210).sum := by decide
  have hdescent : baseEnd_6905210 < baseStart_6905210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905224 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6905224 : Nat := 118140960795 + 6905224 * 2 ^ 59
def prefixEnd_6905224 : Nat := 4983230072969 + 3 ^ 40 * 6905224 * 2
def baseEnd_6905224 : Nat := 3545698938962196513043459

theorem tailTrace_6905224 : CollatzResearch.WordTrace tailWord_6905224 prefixEnd_6905224 3545698938962196513043459 := by
  unfold tailWord_6905224
  simp only [CollatzResearch.WordTrace]
  refine ⟨125927104967780120606989363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167902806623706827475985817 125927104967780120606989363)
  ·
    refine ⟨188890657451670180910484045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125927104967780120606989363 188890657451670180910484045)
    ·
      refine ⟨70833996544376317841431517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188890657451670180910484045 70833996544376317841431517)
      ·
        refine ⟨26562748704141119190536819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70833996544376317841431517 26562748704141119190536819)
        ·
          refine ⟨39844123056211678785805229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26562748704141119190536819 39844123056211678785805229)
          ·
            refine ⟨14941546146079379544676961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39844123056211678785805229 14941546146079379544676961)
            ·
              refine ⟨11206159609559534658507721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14941546146079379544676961 11206159609559534658507721)
              ·
                refine ⟨8404619707169650993880791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11206159609559534658507721 8404619707169650993880791)
                ·
                  refine ⟨12606929560754476490821187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404619707169650993880791 12606929560754476490821187)
                  ·
                    refine ⟨18910394341131714736231781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12606929560754476490821187 18910394341131714736231781)
                    ·
                      refine ⟨3545698938962196513043459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18910394341131714736231781 3545698938962196513043459)
                      ·
                        rfl

theorem cell23_6905224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6905224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905224 prefixEnd_6905224 := by exact prefixLift 6905224
  have htrace : WordTrace (prefixWord ++ tailWord_6905224) baseStart_6905224 baseEnd_6905224 := by
    simpa [prefixWord, tailWord_6905224, baseEnd_6905224] using wordTrace_append hprefix tailTrace_6905224
  have hstable : (prefixWord ++ tailWord_6905224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905224).length < 2 ^ (prefixWord ++ tailWord_6905224).sum := by decide
  have hdescent : baseEnd_6905224 < baseStart_6905224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905354 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 5]
def baseStart_6905354 : Nat := 118140960795 + 6905354 * 2 ^ 59
def prefixEnd_6905354 : Nat := 4983230072969 + 3 ^ 40 * 6905354 * 2
def baseEnd_6905354 : Nat := 393973965716364556046429

theorem tailTrace_6905354 : CollatzResearch.WordTrace tailWord_6905354 prefixEnd_6905354 393973965716364556046429 := by
  unfold tailWord_6905354
  simp only [CollatzResearch.WordTrace]
  refine ⟨62964737856272318354052779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167905967616726182277474077 62964737856272318354052779)
  ·
    refine ⟨94447106784408477531079169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62964737856272318354052779 94447106784408477531079169)
    ·
      refine ⟨70835330088306358148309377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94447106784408477531079169 70835330088306358148309377)
      ·
        refine ⟨53126497566229768611232033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70835330088306358148309377 53126497566229768611232033)
        ·
          refine ⟨39844873174672326458424025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53126497566229768611232033 39844873174672326458424025)
          ·
            refine ⟨29883654881004244843818019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39844873174672326458424025 29883654881004244843818019)
            ·
              refine ⟨44825482321506367265727029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29883654881004244843818019 44825482321506367265727029)
              ·
                refine ⟨4202388967641221931161909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44825482321506367265727029 4202388967641221931161909)
                ·
                  refine ⟨393973965716364556046429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202388967641221931161909 393973965716364556046429)
                  ·
                    rfl

theorem cell23_6905354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_6905354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905354 prefixEnd_6905354 := by exact prefixLift 6905354
  have htrace : WordTrace (prefixWord ++ tailWord_6905354) baseStart_6905354 baseEnd_6905354 := by
    simpa [prefixWord, tailWord_6905354, baseEnd_6905354] using wordTrace_append hprefix tailTrace_6905354
  have hstable : (prefixWord ++ tailWord_6905354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905354).length < 2 ^ (prefixWord ++ tailWord_6905354).sum := by decide
  have hdescent : baseEnd_6905354 < baseStart_6905354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905424 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_6905424 : Nat := 118140960795 + 6905424 * 2 ^ 59
def prefixEnd_6905424 : Nat := 4983230072969 + 3 ^ 40 * 6905424 * 2
def baseEnd_6905424 : Nat := 3545801635093095730542539

theorem tailTrace_6905424 : CollatzResearch.WordTrace tailWord_6905424 prefixEnd_6905424 3545801635093095730542539 := by
  unfold tailWord_6905424
  simp only [CollatzResearch.WordTrace]
  refine ⟨125930752267417837685629663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167907669689890450247506217 125930752267417837685629663)
  ·
    refine ⟨188896128401126756528444495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125930752267417837685629663 188896128401126756528444495)
    ·
      refine ⟨283344192601690134792666743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188896128401126756528444495 283344192601690134792666743)
      ·
        refine ⟨425016288902535202189000115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283344192601690134792666743 425016288902535202189000115)
        ·
          refine ⟨637524433353802803283500173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425016288902535202189000115 637524433353802803283500173)
          ·
            refine ⟨239071662507676051231312565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 637524433353802803283500173 239071662507676051231312565)
            ·
              refine ⟨22412968360094629802935553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239071662507676051231312565 22412968360094629802935553)
              ·
                refine ⟨16809726270070972352201665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22412968360094629802935553 16809726270070972352201665)
                ·
                  refine ⟨12607294702553229264151249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16809726270070972352201665 12607294702553229264151249)
                  ·
                    refine ⟨9455471026914921948113437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12607294702553229264151249 9455471026914921948113437)
                    ·
                      refine ⟨3545801635093095730542539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9455471026914921948113437 3545801635093095730542539)
                      ·
                        rfl

theorem cell23_6905424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_6905424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905424 prefixEnd_6905424 := by exact prefixLift 6905424
  have htrace : WordTrace (prefixWord ++ tailWord_6905424) baseStart_6905424 baseEnd_6905424 := by
    simpa [prefixWord, tailWord_6905424, baseEnd_6905424] using wordTrace_append hprefix tailTrace_6905424
  have hstable : (prefixWord ++ tailWord_6905424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905424).length < 2 ^ (prefixWord ++ tailWord_6905424).sum := by decide
  have hdescent : baseEnd_6905424 < baseStart_6905424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905431 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 3, 4]
def baseStart_6905431 : Nat := 118140960795 + 6905431 * 2 ^ 59
def prefixEnd_6905431 : Nat := 4983230072969 + 3 ^ 40 * 6905431 * 2
def baseEnd_6905431 : Nat := 1181935076485892401051669

theorem tailTrace_6905431 : CollatzResearch.WordTrace tailWord_6905431 prefixEnd_6905431 1181935076485892401051669 := by
  unfold tailWord_6905431
  simp only [CollatzResearch.WordTrace]
  refine ⟨251861759845810315566764147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167907839897206877044509431 251861759845810315566764147)
  ·
    refine ⟨377792639768715473350146221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251861759845810315566764147 377792639768715473350146221)
    ·
      refine ⟨141672239913268302506304833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377792639768715473350146221 141672239913268302506304833)
      ·
        refine ⟨106254179934951226879728625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141672239913268302506304833 106254179934951226879728625)
        ·
          refine ⟨79690634951213420159796469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106254179934951226879728625 79690634951213420159796469)
          ·
            refine ⟨7470997026676258139980919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79690634951213420159796469 7470997026676258139980919)
            ·
              refine ⟨11206495540014387209971379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470997026676258139980919 11206495540014387209971379)
              ·
                refine ⟨16809743310021580814957069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206495540014387209971379 16809743310021580814957069)
                ·
                  refine ⟨6303653741258092805608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16809743310021580814957069 6303653741258092805608901)
                  ·
                    refine ⟨1181935076485892401051669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303653741258092805608901 1181935076485892401051669)
                    ·
                      rfl

theorem cell23_6905431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_6905431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905431 prefixEnd_6905431 := by exact prefixLift 6905431
  have htrace : WordTrace (prefixWord ++ tailWord_6905431) baseStart_6905431 baseEnd_6905431 := by
    simpa [prefixWord, tailWord_6905431, baseEnd_6905431] using wordTrace_append hprefix tailTrace_6905431
  have hstable : (prefixWord ++ tailWord_6905431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905431).length < 2 ^ (prefixWord ++ tailWord_6905431).sum := by decide
  have hdescent : baseEnd_6905431 < baseStart_6905431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905444 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 6]
def baseStart_6905444 : Nat := 118140960795 + 6905444 * 2 ^ 59
def prefixEnd_6905444 : Nat := 4983230072969 + 3 ^ 40 * 6905444 * 2
def baseEnd_6905444 : Nat := 393979100522909516921383

theorem tailTrace_6905444 : CollatzResearch.WordTrace tailWord_6905444 prefixEnd_6905444 393979100522909516921383 := by
  unfold tailWord_6905444
  simp only [CollatzResearch.WordTrace]
  refine ⟨125931116997381609393493693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167908155996508812524658257 125931116997381609393493693)
  ·
    refine ⟨47224168874018103522560135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125931116997381609393493693 47224168874018103522560135)
    ·
      refine ⟨70836253311027155283840203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47224168874018103522560135 70836253311027155283840203)
      ·
        refine ⟨106254379966540732925760305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70836253311027155283840203 106254379966540732925760305)
        ·
          refine ⟨79690784974905549694320229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106254379966540732925760305 79690784974905549694320229)
          ·
            refine ⟨14942022182794790567685043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79690784974905549694320229 14942022182794790567685043)
            ·
              refine ⟨22413033274192185851527565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942022182794790567685043 22413033274192185851527565)
              ·
                refine ⟨8404887477822069694322837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22413033274192185851527565 8404887477822069694322837)
                ·
                  refine ⟨393979100522909516921383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8404887477822069694322837 393979100522909516921383)
                  ·
                    rfl

theorem cell23_6905444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_6905444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905444 prefixEnd_6905444 := by exact prefixLift 6905444
  have htrace : WordTrace (prefixWord ++ tailWord_6905444) baseStart_6905444 baseEnd_6905444 := by
    simpa [prefixWord, tailWord_6905444, baseEnd_6905444] using wordTrace_append hprefix tailTrace_6905444
  have hstable : (prefixWord ++ tailWord_6905444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905444).length < 2 ^ (prefixWord ++ tailWord_6905444).sum := by decide
  have hdescent : baseEnd_6905444 < baseStart_6905444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905447 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6905447 : Nat := 118140960795 + 6905447 * 2 ^ 59
def prefixEnd_6905447 : Nat := 4983230072969 + 3 ^ 40 * 6905447 * 2
def baseEnd_6905447 : Nat := 3545813445148149140554933

theorem tailTrace_6905447 : CollatzResearch.WordTrace tailWord_6905447 prefixEnd_6905447 3545813445148149140554933 := by
  unfold tailWord_6905447
  simp only [CollatzResearch.WordTrace]
  refine ⟨251862343413752350299346595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167908228942501566866231063 251862343413752350299346595)
  ·
    refine ⟨377793515120628525449019893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251862343413752350299346595 377793515120628525449019893)
    ·
      refine ⟨35418142042558924260845615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 377793515120628525449019893 35418142042558924260845615)
      ·
        refine ⟨53127213063838386391268423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35418142042558924260845615 53127213063838386391268423)
        ·
          refine ⟨79690819595757579586902635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53127213063838386391268423 79690819595757579586902635)
          ·
            refine ⟨119536229393636369380353953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79690819595757579586902635 119536229393636369380353953)
            ·
              refine ⟨89652172045227277035265465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119536229393636369380353953 89652172045227277035265465)
              ·
                refine ⟨67239129033920457776449099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89652172045227277035265465 67239129033920457776449099)
                ·
                  refine ⟨100858693550880686664673649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67239129033920457776449099 100858693550880686664673649)
                  ·
                    refine ⟨75644020163160514998505237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100858693550880686664673649 75644020163160514998505237)
                    ·
                      refine ⟨3545813445148149140554933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75644020163160514998505237 3545813445148149140554933)
                      ·
                        rfl

theorem cell23_6905447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6905447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905447 prefixEnd_6905447 := by exact prefixLift 6905447
  have htrace : WordTrace (prefixWord ++ tailWord_6905447) baseStart_6905447 baseEnd_6905447 := by
    simpa [prefixWord, tailWord_6905447, baseEnd_6905447] using wordTrace_append hprefix tailTrace_6905447
  have hstable : (prefixWord ++ tailWord_6905447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905447).length < 2 ^ (prefixWord ++ tailWord_6905447).sum := by decide
  have hdescent : baseEnd_6905447 < baseStart_6905447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905481 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 2, 3, 2]
def baseStart_6905481 : Nat := 118140960795 + 6905481 * 2 ^ 59
def prefixEnd_6905481 : Nat := 4983230072969 + 3 ^ 40 * 6905481 * 2
def baseEnd_6905481 : Nat := 3545830903490402007529777

theorem tailTrace_6905481 : CollatzResearch.WordTrace tailWord_6905481 prefixEnd_6905481 3545830903490402007529777 := by
  unfold tailWord_6905481
  simp only [CollatzResearch.WordTrace]
  refine ⟨251863583495629174106084297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167909055663752782737389531 251863583495629174106084297)
  ·
    refine ⟨188897687621721880579563223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251863583495629174106084297 188897687621721880579563223)
    ·
      refine ⟨283346531432582820869344835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188897687621721880579563223 283346531432582820869344835)
      ·
        refine ⟨425019797148874231304017253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283346531432582820869344835 425019797148874231304017253)
        ·
          refine ⟨79691211965413918369503235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425019797148874231304017253 79691211965413918369503235)
          ·
            refine ⟨119536817948120877554254853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79691211965413918369503235 119536817948120877554254853)
            ·
              refine ⟨22413153365272664541422785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119536817948120877554254853 22413153365272664541422785)
              ·
                refine ⟨16809865023954498406067089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22413153365272664541422785 16809865023954498406067089)
                ·
                  refine ⟨12607398767965873804550317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16809865023954498406067089 12607398767965873804550317)
                  ·
                    refine ⟨4727774537987202676706369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12607398767965873804550317 4727774537987202676706369)
                    ·
                      refine ⟨3545830903490402007529777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727774537987202676706369 3545830903490402007529777)
                      ·
                        rfl

theorem cell23_6905481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3, 2].length) (baseStart_6905481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905481 prefixEnd_6905481 := by exact prefixLift 6905481
  have htrace : WordTrace (prefixWord ++ tailWord_6905481) baseStart_6905481 baseEnd_6905481 := by
    simpa [prefixWord, tailWord_6905481, baseEnd_6905481] using wordTrace_append hprefix tailTrace_6905481
  have hstable : (prefixWord ++ tailWord_6905481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905481).length < 2 ^ (prefixWord ++ tailWord_6905481).sum := by decide
  have hdescent : baseEnd_6905481 < baseStart_6905481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905504 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_6905504 : Nat := 118140960795 + 6905504 * 2 ^ 59
def prefixEnd_6905504 : Nat := 4983230072969 + 3 ^ 40 * 6905504 * 2
def baseEnd_6905504 : Nat := 1181947571181818472514057

theorem tailTrace_6905504 : CollatzResearch.WordTrace tailWord_6905504 prefixEnd_6905504 1181947571181818472514057 := by
  unfold tailWord_6905504
  simp only [CollatzResearch.WordTrace]
  refine ⟨125932211187272924517085783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167909614916363899356114377 125932211187272924517085783)
  ·
    refine ⟨188898316780909386775628675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125932211187272924517085783 188898316780909386775628675)
    ·
      refine ⟨283347475171364080163443013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188898316780909386775628675 283347475171364080163443013)
      ·
        refine ⟨53127651594630765030645565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 283347475171364080163443013 53127651594630765030645565)
        ·
          refine ⟨19922869347986536886492087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53127651594630765030645565 19922869347986536886492087)
          ·
            refine ⟨29884304021979805329738131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19922869347986536886492087 29884304021979805329738131)
            ·
              refine ⟨44826456032969707994607197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29884304021979805329738131 44826456032969707994607197)
              ·
                refine ⟨16809921012363640497977699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44826456032969707994607197 16809921012363640497977699)
                ·
                  refine ⟨25214881518545460746966549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16809921012363640497977699 25214881518545460746966549)
                  ·
                    refine ⟨1181947571181818472514057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25214881518545460746966549 1181947571181818472514057)
                    ·
                      rfl

theorem cell23_6905504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_6905504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905504 prefixEnd_6905504 := by exact prefixLift 6905504
  have htrace : WordTrace (prefixWord ++ tailWord_6905504) baseStart_6905504 baseEnd_6905504 := by
    simpa [prefixWord, tailWord_6905504, baseEnd_6905504] using wordTrace_append hprefix tailTrace_6905504
  have hstable : (prefixWord ++ tailWord_6905504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905504).length < 2 ^ (prefixWord ++ tailWord_6905504).sum := by decide
  have hdescent : baseEnd_6905504 < baseStart_6905504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905525 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_6905525 : Nat := 118140960795 + 6905525 * 2 ^ 59
def prefixEnd_6905525 : Nat := 4983230072969 + 3 ^ 40 * 6905525 * 2
def baseEnd_6905525 : Nat := 1181951165546399945126525

theorem tailTrace_6905525 : CollatzResearch.WordTrace tailWord_6905525 prefixEnd_6905525 1181951165546399945126525 := by
  unfold tailWord_6905525
  simp only [CollatzResearch.WordTrace]
  refine ⟨251865188307469769620686029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167910125538313179747124019 251865188307469769620686029)
  ·
    refine ⟨94449445615301163607757261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251865188307469769620686029 94449445615301163607757261)
    ·
      refine ⟨35418542105737936352908973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94449445615301163607757261 35418542105737936352908973)
      ·
        refine ⟨13281953289651726132340865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35418542105737936352908973 13281953289651726132340865)
        ·
          refine ⟨9961464967238794599255649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281953289651726132340865 9961464967238794599255649)
          ·
            refine ⟨7471098725429095949441737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9961464967238794599255649 7471098725429095949441737)
            ·
              refine ⟨5603324044071821962081303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471098725429095949441737 5603324044071821962081303)
              ·
                refine ⟨8404986066107732943121955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603324044071821962081303 8404986066107732943121955)
                ·
                  refine ⟨12607479099161599414682933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404986066107732943121955 12607479099161599414682933)
                  ·
                    refine ⟨1181951165546399945126525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12607479099161599414682933 1181951165546399945126525)
                    ·
                      rfl

theorem cell23_6905525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_6905525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905525 prefixEnd_6905525 := by exact prefixLift 6905525
  have htrace : WordTrace (prefixWord ++ tailWord_6905525) baseStart_6905525 baseEnd_6905525 := by
    simpa [prefixWord, tailWord_6905525, baseEnd_6905525] using wordTrace_append hprefix tailTrace_6905525
  have hstable : (prefixWord ++ tailWord_6905525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905525).length < 2 ^ (prefixWord ++ tailWord_6905525).sum := by decide
  have hdescent : baseEnd_6905525 < baseStart_6905525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905534 : List Nat := [4, 2, 1, 1, 2, 3, 10]
def baseStart_6905534 : Nat := 118140960795 + 6905534 * 2 ^ 59
def prefixEnd_6905534 : Nat := 4983230072969 + 3 ^ 40 * 6905534 * 2
def baseEnd_6905534 : Nat := 43776026147717164199593

theorem tailTrace_6905534 : CollatzResearch.WordTrace tailWord_6905534 prefixEnd_6905534 43776026147717164199593 := by
  unfold tailWord_6905534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483189570554645519720457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167910344376291442771842437 31483189570554645519720457)
  ·
    refine ⟨23612392177915984139790343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31483189570554645519720457 23612392177915984139790343)
    ·
      refine ⟨35418588266873976209685515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23612392177915984139790343 35418588266873976209685515)
      ·
        refine ⟨53127882400310964314528273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35418588266873976209685515 53127882400310964314528273)
        ·
          refine ⟨39845911800233223235896205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53127882400310964314528273 39845911800233223235896205)
          ·
            refine ⟨14942216925087458713461077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39845911800233223235896205 14942216925087458713461077)
            ·
              refine ⟨43776026147717164199593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14942216925087458713461077 43776026147717164199593)
              ·
                rfl

theorem cell23_6905534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 10].length) (baseStart_6905534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905534 prefixEnd_6905534 := by exact prefixLift 6905534
  have htrace : WordTrace (prefixWord ++ tailWord_6905534) baseStart_6905534 baseEnd_6905534 := by
    simpa [prefixWord, tailWord_6905534, baseEnd_6905534] using wordTrace_append hprefix tailTrace_6905534
  have hstable : (prefixWord ++ tailWord_6905534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905534).length < 2 ^ (prefixWord ++ tailWord_6905534).sum := by decide
  have hdescent : baseEnd_6905534 < baseStart_6905534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905547 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 9]
def baseStart_6905547 : Nat := 118140960795 + 6905547 * 2 ^ 59
def prefixEnd_6905547 : Nat := 4983230072969 + 3 ^ 40 * 6905547 * 2
def baseEnd_6905547 : Nat := 1181954931071199583101491

theorem tailTrace_6905547 : CollatzResearch.WordTrace tailWord_6905547 prefixEnd_6905547 1181954931071199583101491 := by
  unfold tailWord_6905547
  simp only [CollatzResearch.WordTrace]
  refine ⟨251865990713390067377986895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167910660475593378251991263 251865990713390067377986895)
  ·
    refine ⟨377798986070085101066980343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251865990713390067377986895 377798986070085101066980343)
    ·
      refine ⟨566698479105127651600470515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377798986070085101066980343 566698479105127651600470515)
      ·
        refine ⟨850047718657691477400705773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566698479105127651600470515 850047718657691477400705773)
        ·
          refine ⟨318767894496634304025264665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 850047718657691477400705773 318767894496634304025264665)
          ·
            refine ⟨239075920872475728018948499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318767894496634304025264665 239075920872475728018948499)
            ·
              refine ⟨358613881308713592028422749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239075920872475728018948499 358613881308713592028422749)
              ·
                refine ⟨134480205490767597010658531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358613881308713592028422749 134480205490767597010658531)
                ·
                  refine ⟨201720308236151395515987797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134480205490767597010658531 201720308236151395515987797)
                  ·
                    refine ⟨1181954931071199583101491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 201720308236151395515987797 1181954931071199583101491)
                    ·
                      rfl

theorem cell23_6905547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_6905547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905547 prefixEnd_6905547 := by exact prefixLift 6905547
  have htrace : WordTrace (prefixWord ++ tailWord_6905547) baseStart_6905547 baseEnd_6905547 := by
    simpa [prefixWord, tailWord_6905547, baseEnd_6905547] using wordTrace_append hprefix tailTrace_6905547
  have hstable : (prefixWord ++ tailWord_6905547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905547).length < 2 ^ (prefixWord ++ tailWord_6905547).sum := by decide
  have hdescent : baseEnd_6905547 < baseStart_6905547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905561 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_6905561 : Nat := 118140960795 + 6905561 * 2 ^ 59
def prefixEnd_6905561 : Nat := 4983230072969 + 3 ^ 40 * 6905561 * 2
def baseEnd_6905561 : Nat := 3545871981942761694529409

theorem tailTrace_6905561 : CollatzResearch.WordTrace tailWord_6905561 prefixEnd_6905561 3545871981942761694529409 := by
  unfold tailWord_6905561
  simp only [CollatzResearch.WordTrace]
  refine ⟨251866501335339347768996537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167911000890226231845997691 251866501335339347768996537)
  ·
    refine ⟨188899876001504510826747403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251866501335339347768996537 188899876001504510826747403)
    ·
      refine ⟨283349814002256766240121105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188899876001504510826747403 283349814002256766240121105)
      ·
        refine ⟨212512360501692574680090829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283349814002256766240121105 212512360501692574680090829)
        ·
          refine ⟨79692135188134715505034061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212512360501692574680090829 79692135188134715505034061)
          ·
            refine ⟨29884550695550518314387773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79692135188134715505034061 29884550695550518314387773)
            ·
              refine ⟨11206706510831444367895415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29884550695550518314387773 11206706510831444367895415)
              ·
                refine ⟨16810059766247166551843123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206706510831444367895415 16810059766247166551843123)
                ·
                  refine ⟨25215089649370749827764685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16810059766247166551843123 25215089649370749827764685)
                  ·
                    refine ⟨9455658618514031185411757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25215089649370749827764685 9455658618514031185411757)
                    ·
                      refine ⟨3545871981942761694529409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9455658618514031185411757 3545871981942761694529409)
                      ·
                        rfl

theorem cell23_6905561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_6905561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905561 prefixEnd_6905561 := by exact prefixLift 6905561
  have htrace : WordTrace (prefixWord ++ tailWord_6905561) baseStart_6905561 baseEnd_6905561 := by
    simpa [prefixWord, tailWord_6905561, baseEnd_6905561] using wordTrace_append hprefix tailTrace_6905561
  have hstable : (prefixWord ++ tailWord_6905561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905561).length < 2 ^ (prefixWord ++ tailWord_6905561).sum := by decide
  have hdescent : baseEnd_6905561 < baseStart_6905561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905606 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6905606 : Nat := 118140960795 + 6905606 * 2 ^ 59
def prefixEnd_6905606 : Nat := 4983230072969 + 3 ^ 40 * 6905606 * 2
def baseEnd_6905606 : Nat := 1181965029524071339488901

theorem tailTrace_6905606 : CollatzResearch.WordTrace tailWord_6905606 prefixEnd_6905606 1181965029524071339488901 := by
  unfold tailWord_6905606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870879456880510014199521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167912095080117546969589781 7870879456880510014199521)
  ·
    refine ⟨5903159592660382510649641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7870879456880510014199521 5903159592660382510649641)
    ·
      refine ⟨4427369694495286882987231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5903159592660382510649641 4427369694495286882987231)
      ·
        refine ⟨6641054541742930324480847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427369694495286882987231 6641054541742930324480847)
        ·
          refine ⟨9961581812614395486721271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641054541742930324480847 9961581812614395486721271)
          ·
            refine ⟨14942372718921593230081907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961581812614395486721271 14942372718921593230081907)
            ·
              refine ⟨22413559078382389845122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942372718921593230081907 22413559078382389845122861)
              ·
                refine ⟨8405084654393396191921073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22413559078382389845122861 8405084654393396191921073)
                ·
                  refine ⟨6303813490795047143940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405084654393396191921073 6303813490795047143940805)
                  ·
                    refine ⟨1181965029524071339488901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303813490795047143940805 1181965029524071339488901)
                    ·
                      rfl

theorem cell23_6905606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6905606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905606 prefixEnd_6905606 := by exact prefixLift 6905606
  have htrace : WordTrace (prefixWord ++ tailWord_6905606) baseStart_6905606 baseEnd_6905606 := by
    simpa [prefixWord, tailWord_6905606, baseEnd_6905606] using wordTrace_append hprefix tailTrace_6905606
  have hstable : (prefixWord ++ tailWord_6905606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905606).length < 2 ^ (prefixWord ++ tailWord_6905606).sum := by decide
  have hdescent : baseEnd_6905606 < baseStart_6905606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905624 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 7]
def baseStart_6905624 : Nat := 118140960795 + 6905624 * 2 ^ 59
def prefixEnd_6905624 : Nat := 4983230072969 + 3 ^ 40 * 6905624 * 2
def baseEnd_6905624 : Nat := 393989370135999438671291

theorem tailTrace_6905624 : CollatzResearch.WordTrace tailWord_6905624 prefixEnd_6905624 393989370135999438671291 := by
  unfold tailWord_6905624
  simp only [CollatzResearch.WordTrace]
  refine ⟨125934399567055554764269963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167912532756074073019026617 125934399567055554764269963)
  ·
    refine ⟨188901599350583332146404945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125934399567055554764269963 188901599350583332146404945)
    ·
      refine ⟨141676199512937499109803709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188901599350583332146404945 141676199512937499109803709)
      ·
        refine ⟨53128574817351562166176391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141676199512937499109803709 53128574817351562166176391)
        ·
          refine ⟨79692862226027343249264587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53128574817351562166176391 79692862226027343249264587)
          ·
            refine ⟨119539293339041014873896881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79692862226027343249264587 119539293339041014873896881)
            ·
              refine ⟨89654470004280761155422661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119539293339041014873896881 89654470004280761155422661)
              ·
                refine ⟨16810213125802642716641749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89654470004280761155422661 16810213125802642716641749)
                ·
                  refine ⟨393989370135999438671291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16810213125802642716641749 393989370135999438671291)
                  ·
                    rfl

theorem cell23_6905624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_6905624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905624 prefixEnd_6905624 := by exact prefixLift 6905624
  have htrace : WordTrace (prefixWord ++ tailWord_6905624) baseStart_6905624 baseEnd_6905624 := by
    simpa [prefixWord, tailWord_6905624, baseEnd_6905624] using wordTrace_append hprefix tailTrace_6905624
  have hstable : (prefixWord ++ tailWord_6905624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905624).length < 2 ^ (prefixWord ++ tailWord_6905624).sum := by decide
  have hdescent : baseEnd_6905624 < baseStart_6905624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905652 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_6905652 : Nat := 118140960795 + 6905652 * 2 ^ 59
def prefixEnd_6905652 : Nat := 4983230072969 + 3 ^ 40 * 6905652 * 2
def baseEnd_6905652 : Nat := 3545918708682320838491491

theorem tailTrace_6905652 : CollatzResearch.WordTrace tailWord_6905652 prefixEnd_6905652 3545918708682320838491491 := by
  unfold tailWord_6905652
  simp only [CollatzResearch.WordTrace]
  refine ⟨125934910189004835155279605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167913213585339780207039473 125934910189004835155279605)
  ·
    refine ⟨11806397830219203295807463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125934910189004835155279605 11806397830219203295807463)
    ·
      refine ⟨17709596745328804943711195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11806397830219203295807463 17709596745328804943711195)
      ·
        refine ⟨26564395117993207415566793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17709596745328804943711195 26564395117993207415566793)
        ·
          refine ⟨19923296338494905561675095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26564395117993207415566793 19923296338494905561675095)
          ·
            refine ⟨29884944507742358342512643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19923296338494905561675095 29884944507742358342512643)
            ·
              refine ⟨44827416761613537513768965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29884944507742358342512643 44827416761613537513768965)
              ·
                refine ⟨8405140642802538283831681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44827416761613537513768965 8405140642802538283831681)
                ·
                  refine ⟨6303855482101903712873761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405140642802538283831681 6303855482101903712873761)
                  ·
                    refine ⟨4727891611576427784655321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303855482101903712873761 4727891611576427784655321)
                    ·
                      refine ⟨3545918708682320838491491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727891611576427784655321 3545918708682320838491491)
                      ·
                        rfl

theorem cell23_6905652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_6905652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905652 prefixEnd_6905652 := by exact prefixLift 6905652
  have htrace : WordTrace (prefixWord ++ tailWord_6905652) baseStart_6905652 baseEnd_6905652 := by
    simpa [prefixWord, tailWord_6905652, baseEnd_6905652] using wordTrace_append hprefix tailTrace_6905652
  have hstable : (prefixWord ++ tailWord_6905652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905652).length < 2 ^ (prefixWord ++ tailWord_6905652).sum := by decide
  have hdescent : baseEnd_6905652 < baseStart_6905652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905658 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 5]
def baseStart_6905658 : Nat := 118140960795 + 6905658 * 2 ^ 59
def prefixEnd_6905658 : Nat := 4983230072969 + 3 ^ 40 * 6905658 * 2
def baseEnd_6905658 : Nat := 393991309951805312779607

theorem tailTrace_6905658 : CollatzResearch.WordTrace tailWord_6905658 prefixEnd_6905658 393991309951805312779607 := by
  unfold tailWord_6905658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62967509803996983333819407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167913359477325288890185085 62967509803996983333819407)
  ·
    refine ⟨94451264705995475000729111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62967509803996983333819407 94451264705995475000729111)
    ·
      refine ⟨141676897058993212501093667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94451264705995475000729111 141676897058993212501093667)
      ·
        refine ⟨212515345588489818751640501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141676897058993212501093667 212515345588489818751640501)
        ·
          refine ⟨19923313648920920507966297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212515345588489818751640501 19923313648920920507966297)
          ·
            refine ⟨14942485236690690380974723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19923313648920920507966297 14942485236690690380974723)
            ·
              refine ⟨22413727855036035571462085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942485236690690380974723 22413727855036035571462085)
              ·
                refine ⟨4202573972819256669649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22413727855036035571462085 4202573972819256669649141)
                ·
                  refine ⟨393991309951805312779607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202573972819256669649141 393991309951805312779607)
                  ·
                    rfl

theorem cell23_6905658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_6905658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905658 prefixEnd_6905658 := by exact prefixLift 6905658
  have htrace : WordTrace (prefixWord ++ tailWord_6905658) baseStart_6905658 baseEnd_6905658 := by
    simpa [prefixWord, tailWord_6905658, baseEnd_6905658] using wordTrace_append hprefix tailTrace_6905658
  have hstable : (prefixWord ++ tailWord_6905658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905658).length < 2 ^ (prefixWord ++ tailWord_6905658).sum := by decide
  have hdescent : baseEnd_6905658 < baseStart_6905658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905701 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_6905701 : Nat := 118140960795 + 6905701 * 2 ^ 59
def prefixEnd_6905701 : Nat := 4983230072969 + 3 ^ 40 * 6905701 * 2
def baseEnd_6905701 : Nat := 1181981289744797048926255

theorem tailTrace_6905701 : CollatzResearch.WordTrace tailWord_6905701 prefixEnd_6905701 1181981289744797048926255 := by
  unfold tailWord_6905701
  simp only [CollatzResearch.WordTrace]
  refine ⟨251871607554832151679092957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167914405036554767786061971 251871607554832151679092957)
  ·
    refine ⟨94451852833062056879659859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251871607554832151679092957 94451852833062056879659859)
    ·
      refine ⟨141677779249593085319489789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94451852833062056879659859 141677779249593085319489789)
      ·
        refine ⟨53129167218597406994808671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141677779249593085319489789 53129167218597406994808671)
        ·
          refine ⟨79693750827896110492213007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53129167218597406994808671 79693750827896110492213007)
          ·
            refine ⟨119540626241844165738319511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79693750827896110492213007 119540626241844165738319511)
            ·
              refine ⟨179310939362766248607479267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119540626241844165738319511 179310939362766248607479267)
              ·
                refine ⟨268966409044149372911218901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179310939362766248607479267 268966409044149372911218901)
                ·
                  refine ⟨6303900211972250927606693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268966409044149372911218901 6303900211972250927606693)
                  ·
                    refine ⟨1181981289744797048926255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303900211972250927606693 1181981289744797048926255)
                    ·
                      rfl

theorem cell23_6905701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_6905701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905701 prefixEnd_6905701 := by exact prefixLift 6905701
  have htrace : WordTrace (prefixWord ++ tailWord_6905701) baseStart_6905701 baseEnd_6905701 := by
    simpa [prefixWord, tailWord_6905701, baseEnd_6905701] using wordTrace_append hprefix tailTrace_6905701
  have hstable : (prefixWord ++ tailWord_6905701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905701).length < 2 ^ (prefixWord ++ tailWord_6905701).sum := by decide
  have hdescent : baseEnd_6905701 < baseStart_6905701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905708 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_6905708 : Nat := 118140960795 + 6905708 * 2 ^ 59
def prefixEnd_6905708 : Nat := 4983230072969 + 3 ^ 40 * 6905708 * 2
def baseEnd_6905708 : Nat := 3545947463598972619391233

theorem tailTrace_6905708 : CollatzResearch.WordTrace tailWord_6905708 prefixEnd_6905708 3545947463598972619391233 := by
  unfold tailWord_6905708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125935931432903395937298889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167914575243871194583065185 125935931432903395937298889)
  ·
    refine ⟨94451948574677546952974167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125935931432903395937298889 94451948574677546952974167)
    ·
      refine ⟨141677922862016320429461251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94451948574677546952974167 141677922862016320429461251)
      ·
        refine ⟨212516884293024480644191877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141677922862016320429461251 212516884293024480644191877)
        ·
          refine ⟨39846915804942090120785977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212516884293024480644191877 39846915804942090120785977)
          ·
            refine ⟨29885186853706567590589483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39846915804942090120785977 29885186853706567590589483)
            ·
              refine ⟨44827780280559851385884225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29885186853706567590589483 44827780280559851385884225)
              ·
                refine ⟨33620835210419888539413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44827780280559851385884225 33620835210419888539413169)
                ·
                  refine ⟨25215626407814916404559877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33620835210419888539413169 25215626407814916404559877)
                  ·
                    refine ⟨4727929951465296825854977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25215626407814916404559877 4727929951465296825854977)
                    ·
                      refine ⟨3545947463598972619391233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4727929951465296825854977 3545947463598972619391233)
                      ·
                        rfl

theorem cell23_6905708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_6905708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905708 prefixEnd_6905708 := by exact prefixLift 6905708
  have htrace : WordTrace (prefixWord ++ tailWord_6905708) baseStart_6905708 baseEnd_6905708 := by
    simpa [prefixWord, tailWord_6905708, baseEnd_6905708] using wordTrace_append hprefix tailTrace_6905708
  have hstable : (prefixWord ++ tailWord_6905708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905708).length < 2 ^ (prefixWord ++ tailWord_6905708).sum := by decide
  have hdescent : baseEnd_6905708 < baseStart_6905708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905791 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 6]
def baseStart_6905791 : Nat := 118140960795 + 6905791 * 2 ^ 59
def prefixEnd_6905791 : Nat := 4983230072969 + 3 ^ 40 * 6905791 * 2
def baseEnd_6905791 : Nat := 1181996694164431931551117

theorem tailTrace_6905791 : CollatzResearch.WordTrace tailWord_6905791 prefixEnd_6905791 1181996694164431931551117 := by
  unfold tailWord_6905791
  simp only [CollatzResearch.WordTrace]
  refine ⟨251874890124506097049869227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167916593416337398033246151 251874890124506097049869227)
  ·
    refine ⟨377812335186759145574803841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251874890124506097049869227 377812335186759145574803841)
    ·
      refine ⟨283359251390069359181102881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377812335186759145574803841 283359251390069359181102881)
      ·
        refine ⟨212519438542552019385827161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283359251390069359181102881 212519438542552019385827161)
        ·
          refine ⟨159389578906914014539370371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212519438542552019385827161 159389578906914014539370371)
          ·
            refine ⟨239084368360371021809055557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159389578906914014539370371 239084368360371021809055557)
            ·
              refine ⟨44828319067569566589197917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239084368360371021809055557 44828319067569566589197917)
              ·
                refine ⟨16810619650338587470949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44828319067569566589197917 16810619650338587470949219)
                ·
                  refine ⟨25215929475507881206423829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16810619650338587470949219 25215929475507881206423829)
                  ·
                    refine ⟨1181996694164431931551117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25215929475507881206423829 1181996694164431931551117)
                    ·
                      rfl

theorem cell23_6905791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_6905791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905791 prefixEnd_6905791 := by exact prefixLift 6905791
  have htrace : WordTrace (prefixWord ++ tailWord_6905791) baseStart_6905791 baseEnd_6905791 := by
    simpa [prefixWord, tailWord_6905791, baseEnd_6905791] using wordTrace_append hprefix tailTrace_6905791
  have hstable : (prefixWord ++ tailWord_6905791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905791).length < 2 ^ (prefixWord ++ tailWord_6905791).sum := by decide
  have hdescent : baseEnd_6905791 < baseStart_6905791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905801 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_6905801 : Nat := 118140960795 + 6905801 * 2 ^ 59
def prefixEnd_6905801 : Nat := 4983230072969 + 3 ^ 40 * 6905801 * 2
def baseEnd_6905801 : Nat := 3545995217299840755528305

theorem tailTrace_6905801 : CollatzResearch.WordTrace tailWord_6905801 prefixEnd_6905801 3545995217299840755528305 := by
  unfold tailWord_6905801
  simp only [CollatzResearch.WordTrace]
  refine ⟨251875254854469868757733257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167916836569646579171822171 251875254854469868757733257)
  ·
    refine ⟨188906441140852401568299943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251875254854469868757733257 188906441140852401568299943)
    ·
      refine ⟨283359661711278602352449915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188906441140852401568299943 283359661711278602352449915)
      ·
        refine ⟨425039492566917903528674873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283359661711278602352449915 425039492566917903528674873)
        ·
          refine ⟨318779619425188427646506155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425039492566917903528674873 318779619425188427646506155)
          ·
            refine ⟨478169429137782641469759233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318779619425188427646506155 478169429137782641469759233)
            ·
              refine ⟨358627071853336981102319425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478169429137782641469759233 358627071853336981102319425)
              ·
                refine ⟨268970303890002735826739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358627071853336981102319425 268970303890002735826739569)
                ·
                  refine ⟨201727727917502051870054677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268970303890002735826739569 201727727917502051870054677)
                  ·
                    refine ⟨9455987246132908681408813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 201727727917502051870054677 9455987246132908681408813)
                    ·
                      refine ⟨3545995217299840755528305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9455987246132908681408813 3545995217299840755528305)
                      ·
                        rfl

theorem cell23_6905801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_6905801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905801 prefixEnd_6905801 := by exact prefixLift 6905801
  have htrace : WordTrace (prefixWord ++ tailWord_6905801) baseStart_6905801 baseEnd_6905801 := by
    simpa [prefixWord, tailWord_6905801, baseEnd_6905801] using wordTrace_append hprefix tailTrace_6905801
  have hstable : (prefixWord ++ tailWord_6905801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905801).length < 2 ^ (prefixWord ++ tailWord_6905801).sum := by decide
  have hdescent : baseEnd_6905801 < baseStart_6905801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905815 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 1, 1, 4]
def baseStart_6905815 : Nat := 118140960795 + 6905815 * 2 ^ 59
def prefixEnd_6905815 : Nat := 4983230072969 + 3 ^ 40 * 6905815 * 2
def baseEnd_6905815 : Nat := 3546002406029003700753241

theorem tailTrace_6905815 : CollatzResearch.WordTrace tailWord_6905815 prefixEnd_6905815 3546002406029003700753241 := by
  unfold tailWord_6905815
  simp only [CollatzResearch.WordTrace]
  refine ⟨251875765476419149148742899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167917176984279432765828599 251875765476419149148742899)
  ·
    refine ⟨377813648214628723723114349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251875765476419149148742899 377813648214628723723114349)
    ·
      refine ⟨141680118080485771396167881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377813648214628723723114349 141680118080485771396167881)
      ·
        refine ⟨106260088560364328547125911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141680118080485771396167881 106260088560364328547125911)
        ·
          refine ⟨159390132840546492820688867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106260088560364328547125911 159390132840546492820688867)
          ·
            refine ⟨239085199260819739231033301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159390132840546492820688867 239085199260819739231033301)
            ·
              refine ⟨5603559357675462638227343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 239085199260819739231033301 5603559357675462638227343)
              ·
                refine ⟨8405339036513193957341015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603559357675462638227343 8405339036513193957341015)
                ·
                  refine ⟨12608008554769790936011523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8405339036513193957341015 12608008554769790936011523)
                  ·
                    refine ⟨18912012832154686404017285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12608008554769790936011523 18912012832154686404017285)
                    ·
                      refine ⟨3546002406029003700753241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18912012832154686404017285 3546002406029003700753241)
                      ·
                        rfl

theorem cell23_6905815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_6905815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905815 prefixEnd_6905815 := by exact prefixLift 6905815
  have htrace : WordTrace (prefixWord ++ tailWord_6905815) baseStart_6905815 baseEnd_6905815 := by
    simpa [prefixWord, tailWord_6905815, baseEnd_6905815] using wordTrace_append hprefix tailTrace_6905815
  have hstable : (prefixWord ++ tailWord_6905815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905815).length < 2 ^ (prefixWord ++ tailWord_6905815).sum := by decide
  have hdescent : baseEnd_6905815 < baseStart_6905815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905820 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6905820 : Nat := 118140960795 + 6905820 * 2 ^ 59
def prefixEnd_6905820 : Nat := 4983230072969 + 3 ^ 40 * 6905820 * 2
def baseEnd_6905820 : Nat := 1182001657810758727063573

theorem tailTrace_6905820 : CollatzResearch.WordTrace tailWord_6905820 prefixEnd_6905820 1182001657810758727063573 := by
  unfold tailWord_6905820
  simp only [CollatzResearch.WordTrace]
  refine ⟨125937973920700517501337457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167917298560934023335116609 125937973920700517501337457)
  ·
    refine ⟨94453480440525388126003093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125937973920700517501337457 94453480440525388126003093)
    ·
      refine ⟨4427506895649627568406395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94453480440525388126003093 4427506895649627568406395)
      ·
        refine ⟨6641260343474441352609593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427506895649627568406395 6641260343474441352609593)
        ·
          refine ⟨4980945257605831014457195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6641260343474441352609593 4980945257605831014457195)
          ·
            refine ⟨7471417886408746521685793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980945257605831014457195 7471417886408746521685793)
            ·
              refine ⟨5603563414806559891264345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471417886408746521685793 5603563414806559891264345)
              ·
                refine ⟨4202672561104919918448259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603563414806559891264345 4202672561104919918448259)
                ·
                  refine ⟨6304008841657379877672389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202672561104919918448259 6304008841657379877672389)
                  ·
                    refine ⟨1182001657810758727063573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304008841657379877672389 1182001657810758727063573)
                    ·
                      rfl

theorem cell23_6905820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6905820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905820 prefixEnd_6905820 := by exact prefixLift 6905820
  have htrace : WordTrace (prefixWord ++ tailWord_6905820) baseStart_6905820 baseEnd_6905820 := by
    simpa [prefixWord, tailWord_6905820, baseEnd_6905820] using wordTrace_append hprefix tailTrace_6905820
  have hstable : (prefixWord ++ tailWord_6905820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905820).length < 2 ^ (prefixWord ++ tailWord_6905820).sum := by decide
  have hdescent : baseEnd_6905820 < baseStart_6905820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905821 : List Nat := [1, 4, 3, 1, 14]
def baseStart_6905821 : Nat := 118140960795 + 6905821 * 2 ^ 59
def prefixEnd_6905821 : Nat := 4983230072969 + 3 ^ 40 * 6905821 * 2
def baseEnd_6905821 : Nat := 4864205057493732067597

theorem tailTrace_6905821 : CollatzResearch.WordTrace tailWord_6905821 prefixEnd_6905821 4864205057493732067597 := by
  unfold tailWord_6905821
  simp only [CollatzResearch.WordTrace]
  refine ⟨251875984314397412173461317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167917322876264941448974211 251875984314397412173461317)
  ·
    refine ⟨47226747058949514782523997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251875984314397412173461317 47226747058949514782523997)
    ·
      refine ⟨17710030147106068043446499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47226747058949514782523997 17710030147106068043446499)
      ·
        refine ⟨26565045220659102065169749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17710030147106068043446499 26565045220659102065169749)
        ·
          refine ⟨4864205057493732067597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26565045220659102065169749 4864205057493732067597)
          ·
            rfl

theorem cell23_6905821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 14].length) (baseStart_6905821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905821 prefixEnd_6905821 := by exact prefixLift 6905821
  have htrace : WordTrace (prefixWord ++ tailWord_6905821) baseStart_6905821 baseEnd_6905821 := by
    simpa [prefixWord, tailWord_6905821, baseEnd_6905821] using wordTrace_append hprefix tailTrace_6905821
  have hstable : (prefixWord ++ tailWord_6905821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905821).length < 2 ^ (prefixWord ++ tailWord_6905821).sum := by decide
  have hdescent : baseEnd_6905821 < baseStart_6905821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905826 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6905826 : Nat := 118140960795 + 6905826 * 2 ^ 59
def prefixEnd_6905826 : Nat := 4983230072969 + 3 ^ 40 * 6905826 * 2
def baseEnd_6905826 : Nat := 3546008054316203157715691

theorem tailTrace_6905826 : CollatzResearch.WordTrace tailWord_6905826 prefixEnd_6905826 3546008054316203157715691 := by
  unfold tailWord_6905826
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969041669844824506848333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167917444452919532018262221 62969041669844824506848333)
  ·
    refine ⟨23613390626191809190068125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62969041669844824506848333 23613390626191809190068125)
    ·
      refine ⟨8855021484821928446275547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23613390626191809190068125 8855021484821928446275547)
      ·
        refine ⟨13282532227232892669413321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855021484821928446275547 13282532227232892669413321)
        ·
          refine ⟨9961899170424669502059991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13282532227232892669413321 9961899170424669502059991)
          ·
            refine ⟨14942848755637004253089987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961899170424669502059991 14942848755637004253089987)
            ·
              refine ⟨22414273133455506379634981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942848755637004253089987 22414273133455506379634981)
              ·
                refine ⟨4202676212522907446181559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22414273133455506379634981 4202676212522907446181559)
                ·
                  refine ⟨6304014318784361169272339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202676212522907446181559 6304014318784361169272339)
                  ·
                    refine ⟨9456021478176541753908509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6304014318784361169272339 9456021478176541753908509)
                    ·
                      refine ⟨3546008054316203157715691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456021478176541753908509 3546008054316203157715691)
                      ·
                        rfl

theorem cell23_6905826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6905826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905826 prefixEnd_6905826 := by exact prefixLift 6905826
  have htrace : WordTrace (prefixWord ++ tailWord_6905826) baseStart_6905826 baseEnd_6905826 := by
    simpa [prefixWord, tailWord_6905826, baseEnd_6905826] using wordTrace_append hprefix tailTrace_6905826
  have hstable : (prefixWord ++ tailWord_6905826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905826).length < 2 ^ (prefixWord ++ tailWord_6905826).sum := by decide
  have hdescent : baseEnd_6905826 < baseStart_6905826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905838 : List Nat := [4, 1, 2, 1, 3, 1, 3, 8]
def baseStart_6905838 : Nat := 118140960795 + 6905838 * 2 ^ 59
def prefixEnd_6905838 : Nat := 4983230072969 + 3 ^ 40 * 6905838 * 2
def baseEnd_6905838 : Nat := 131333859854965078176505

theorem tailTrace_6905838 : CollatzResearch.WordTrace tailWord_6905838 prefixEnd_6905838 131333859854965078176505 := by
  unfold tailWord_6905838
  simp only [CollatzResearch.WordTrace]
  refine ⟨31484575544416978009603771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167917736236890549384553445 31484575544416978009603771)
  ·
    refine ⟨47226863316625467014405657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31484575544416978009603771 47226863316625467014405657)
    ·
      refine ⟨35420147487469100260804243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47226863316625467014405657 35420147487469100260804243)
      ·
        refine ⟨53130221231203650391206365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35420147487469100260804243 53130221231203650391206365)
        ·
          refine ⟨19923832961701368896702387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53130221231203650391206365 19923832961701368896702387)
          ·
            refine ⟨29885749442552053345053581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19923832961701368896702387 29885749442552053345053581)
            ·
              refine ⟨11207156040957020004395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29885749442552053345053581 11207156040957020004395093)
              ·
                refine ⟨131333859854965078176505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11207156040957020004395093 131333859854965078176505)
                ·
                  rfl

theorem cell23_6905838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_6905838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905838 prefixEnd_6905838 := by exact prefixLift 6905838
  have htrace : WordTrace (prefixWord ++ tailWord_6905838) baseStart_6905838 baseEnd_6905838 := by
    simpa [prefixWord, tailWord_6905838, baseEnd_6905838] using wordTrace_append hprefix tailTrace_6905838
  have hstable : (prefixWord ++ tailWord_6905838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905838).length < 2 ^ (prefixWord ++ tailWord_6905838).sum := by decide
  have hdescent : baseEnd_6905838 < baseStart_6905838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905848 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_6905848 : Nat := 118140960795 + 6905848 * 2 ^ 59
def prefixEnd_6905848 : Nat := 4983230072969 + 3 ^ 40 * 6905848 * 2
def baseEnd_6905848 : Nat := 3546019350890602071640589

theorem tailTrace_6905848 : CollatzResearch.WordTrace tailWord_6905848 prefixEnd_6905848 3546019350890602071640589 := by
  unfold tailWord_6905848
  simp only [CollatzResearch.WordTrace]
  refine ⟨125938484542649797892347099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167917979390199730523129465 125938484542649797892347099)
  ·
    refine ⟨188907726813974696838520649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125938484542649797892347099 188907726813974696838520649)
    ·
      refine ⟨141680795110481022628890487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188907726813974696838520649 141680795110481022628890487)
      ·
        refine ⟨212521192665721533943335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141680795110481022628890487 212521192665721533943335731)
        ·
          refine ⟨318781788998582300915003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212521192665721533943335731 318781788998582300915003597)
          ·
            refine ⟨119543170874468362843126349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318781788998582300915003597 119543170874468362843126349)
            ·
              refine ⟨44828689077925636066172381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119543170874468362843126349 44828689077925636066172381)
              ·
                refine ⟨16810758404222113524814643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44828689077925636066172381 16810758404222113524814643)
                ·
                  refine ⟨25216137606333170287221965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16810758404222113524814643 25216137606333170287221965)
                  ·
                    refine ⟨9456051602374938857708237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25216137606333170287221965 9456051602374938857708237)
                    ·
                      refine ⟨3546019350890602071640589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456051602374938857708237 3546019350890602071640589)
                      ·
                        rfl

theorem cell23_6905848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_6905848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905848 prefixEnd_6905848 := by exact prefixLift 6905848
  have htrace : WordTrace (prefixWord ++ tailWord_6905848) baseStart_6905848 baseEnd_6905848 := by
    simpa [prefixWord, tailWord_6905848, baseEnd_6905848] using wordTrace_append hprefix tailTrace_6905848
  have hstable : (prefixWord ++ tailWord_6905848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905848).length < 2 ^ (prefixWord ++ tailWord_6905848).sum := by decide
  have hdescent : baseEnd_6905848 < baseStart_6905848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905866 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_6905866 : Nat := 118140960795 + 6905866 * 2 ^ 59
def prefixEnd_6905866 : Nat := 4983230072969 + 3 ^ 40 * 6905866 * 2
def baseEnd_6905866 : Nat := 3546028593542383001215507

theorem tailTrace_6905866 : CollatzResearch.WordTrace tailWord_6905866 prefixEnd_6905866 3546028593542383001215507 := by
  unfold tailWord_6905866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969406399808596214712363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167918417066156256572566301 62969406399808596214712363)
  ·
    refine ⟨94454109599712894322068545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62969406399808596214712363 94454109599712894322068545)
    ·
      refine ⟨70840582199784670741551409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94454109599712894322068545 70840582199784670741551409)
      ·
        refine ⟨53130436649838503056163557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70840582199784670741551409 53130436649838503056163557)
        ·
          refine ⟨9961956871844719323030667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53130436649838503056163557 9961956871844719323030667)
          ·
            refine ⟨14942935307767078984546001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961956871844719323030667 14942935307767078984546001)
            ·
              refine ⟨11207201480825309238409501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14942935307767078984546001 11207201480825309238409501)
              ·
                refine ⟨4202700555309490964403563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11207201480825309238409501 4202700555309490964403563)
                ·
                  refine ⟨6304050832964236446605345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202700555309490964403563 6304050832964236446605345)
                  ·
                    refine ⟨4728038124723177334954009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304050832964236446605345 4728038124723177334954009)
                    ·
                      refine ⟨3546028593542383001215507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728038124723177334954009 3546028593542383001215507)
                      ·
                        rfl

theorem cell23_6905866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_6905866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905866 prefixEnd_6905866 := by exact prefixLift 6905866
  have htrace : WordTrace (prefixWord ++ tailWord_6905866) baseStart_6905866 baseEnd_6905866 := by
    simpa [prefixWord, tailWord_6905866, baseEnd_6905866] using wordTrace_append hprefix tailTrace_6905866
  have hstable : (prefixWord ++ tailWord_6905866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905866).length < 2 ^ (prefixWord ++ tailWord_6905866).sum := by decide
  have hdescent : baseEnd_6905866 < baseStart_6905866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905876 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_6905876 : Nat := 118140960795 + 6905876 * 2 ^ 59
def prefixEnd_6905876 : Nat := 4983230072969 + 3 ^ 40 * 6905876 * 2
def baseEnd_6905876 : Nat := 1182011242782975987363487

theorem tailTrace_6905876 : CollatzResearch.WordTrace tailWord_6905876 prefixEnd_6905876 1182011242782975987363487 := by
  unfold tailWord_6905876
  simp only [CollatzResearch.WordTrace]
  refine ⟨125938995164599078283356741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167918660219465437711142321 125938995164599078283356741)
  ·
    refine ⟨23613561593362327178129389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125938995164599078283356741 23613561593362327178129389)
    ·
      refine ⟨8855085597510872691798521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23613561593362327178129389 8855085597510872691798521)
      ·
        refine ⟨6641314198133154518848891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8855085597510872691798521 6641314198133154518848891)
        ·
          refine ⟨9961971297199731778273337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641314198133154518848891 9961971297199731778273337)
          ·
            refine ⟨7471478472899798833705003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9961971297199731778273337 7471478472899798833705003)
            ·
              refine ⟨11207217709349698250557505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471478472899798833705003 11207217709349698250557505)
              ·
                refine ⟨8405413282012273687918129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207217709349698250557505 8405413282012273687918129)
                ·
                  refine ⟨6304059961509205265938597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405413282012273687918129 6304059961509205265938597)
                  ·
                    refine ⟨1182011242782975987363487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304059961509205265938597 1182011242782975987363487)
                    ·
                      rfl

theorem cell23_6905876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_6905876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905876 prefixEnd_6905876 := by exact prefixLift 6905876
  have htrace : WordTrace (prefixWord ++ tailWord_6905876) baseStart_6905876 baseEnd_6905876 := by
    simpa [prefixWord, tailWord_6905876, baseEnd_6905876] using wordTrace_append hprefix tailTrace_6905876
  have hstable : (prefixWord ++ tailWord_6905876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905876).length < 2 ^ (prefixWord ++ tailWord_6905876).sum := by decide
  have hdescent : baseEnd_6905876 < baseStart_6905876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905882 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_6905882 : Nat := 118140960795 + 6905882 * 2 ^ 59
def prefixEnd_6905882 : Nat := 4983230072969 + 3 ^ 40 * 6905882 * 2
def baseEnd_6905882 : Nat := 3546036809232854938615433

theorem tailTrace_6905882 : CollatzResearch.WordTrace tailWord_6905882 prefixEnd_6905882 3546036809232854938615433 := by
  unfold tailWord_6905882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62969552291794104897857975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167918806111450946394287933 62969552291794104897857975)
  ·
    refine ⟨94454328437691157346786963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62969552291794104897857975 94454328437691157346786963)
    ·
      refine ⟨141681492656536736020180445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94454328437691157346786963 141681492656536736020180445)
      ·
        refine ⟨53130559746201276007567667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141681492656536736020180445 53130559746201276007567667)
        ·
          refine ⟨79695839619301914011351501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53130559746201276007567667 79695839619301914011351501)
          ·
            refine ⟨29885939857238217754256813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79695839619301914011351501 29885939857238217754256813)
            ·
              refine ⟨11207227446464331657846305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29885939857238217754256813 11207227446464331657846305)
              ·
                refine ⟨8405420584848248743384729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207227446464331657846305 8405420584848248743384729)
                ·
                  refine ⟨6304065438636186557538547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405420584848248743384729 6304065438636186557538547)
                  ·
                    refine ⟨9456098157954279836307821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6304065438636186557538547 9456098157954279836307821)
                    ·
                      refine ⟨3546036809232854938615433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456098157954279836307821 3546036809232854938615433)
                      ·
                        rfl

theorem cell23_6905882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_6905882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905882 prefixEnd_6905882 := by exact prefixLift 6905882
  have htrace : WordTrace (prefixWord ++ tailWord_6905882) baseStart_6905882 baseEnd_6905882 := by
    simpa [prefixWord, tailWord_6905882, baseEnd_6905882] using wordTrace_append hprefix tailTrace_6905882
  have hstable : (prefixWord ++ tailWord_6905882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905882).length < 2 ^ (prefixWord ++ tailWord_6905882).sum := by decide
  have hdescent : baseEnd_6905882 < baseStart_6905882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905950 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6905950 : Nat := 118140960795 + 6905950 * 2 ^ 59
def prefixEnd_6905950 : Nat := 4983230072969 + 3 ^ 40 * 6905950 * 2
def baseEnd_6905950 : Nat := 3546071725917360672565121

theorem tailTrace_6905950 : CollatzResearch.WordTrace tailWord_6905950 prefixEnd_6905950 3546071725917360672565121 := by
  unfold tailWord_6905950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31485086166366258400613413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167920459553953378136604869 31485086166366258400613413)
  ·
    refine ⟨5903453656193673450115015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31485086166366258400613413 5903453656193673450115015)
    ·
      refine ⟨8855180484290510175172523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903453656193673450115015 8855180484290510175172523)
      ·
        refine ⟨13282770726435765262758785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855180484290510175172523 13282770726435765262758785)
        ·
          refine ⟨9962078044826823947069089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13282770726435765262758785 9962078044826823947069089)
          ·
            refine ⟨7471558533620117960301817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962078044826823947069089 7471558533620117960301817)
            ·
              refine ⟨5603668900215088470226363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471558533620117960301817 5603668900215088470226363)
              ·
                refine ⟨8405503350322632705339545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603668900215088470226363 8405503350322632705339545)
                ·
                  refine ⟨6304127512741974529004659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405503350322632705339545 6304127512741974529004659)
                  ·
                    refine ⟨9456191269112961793506989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6304127512741974529004659 9456191269112961793506989)
                    ·
                      refine ⟨3546071725917360672565121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456191269112961793506989 3546071725917360672565121)
                      ·
                        rfl

theorem cell23_6905950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6905950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905950 prefixEnd_6905950 := by exact prefixLift 6905950
  have htrace : WordTrace (prefixWord ++ tailWord_6905950) baseStart_6905950 baseEnd_6905950 := by
    simpa [prefixWord, tailWord_6905950, baseEnd_6905950] using wordTrace_append hprefix tailTrace_6905950
  have hstable : (prefixWord ++ tailWord_6905950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905950).length < 2 ^ (prefixWord ++ tailWord_6905950).sum := by decide
  have hdescent : baseEnd_6905950 < baseStart_6905950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6905975 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 2, 5]
def baseStart_6905975 : Nat := 118140960795 + 6905975 * 2 ^ 59
def prefixEnd_6905975 : Nat := 4983230072969 + 3 ^ 40 * 6905975 * 2
def baseEnd_6905975 : Nat := 1182028187644574358250835

theorem tailTrace_6905975 : CollatzResearch.WordTrace tailWord_6905975 prefixEnd_6905975 1182028187644574358250835 := by
  unfold tailWord_6905975
  simp only [CollatzResearch.WordTrace]
  refine ⟨251881601155839496474567379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167921067437226330983044919 251881601155839496474567379)
  ·
    refine ⟨377822401733759244711851069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251881601155839496474567379 377822401733759244711851069)
    ·
      refine ⟨141683400650159716766944151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377822401733759244711851069 141683400650159716766944151)
      ·
        refine ⟨212525100975239575150416227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141683400650159716766944151 212525100975239575150416227)
        ·
          refine ⟨318787651462859362725624341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212525100975239575150416227 318787651462859362725624341)
          ·
            refine ⟨14943171162321532627763641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318787651462859362725624341 14943171162321532627763641)
            ·
              refine ⟨11207378371741149470822731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14943171162321532627763641 11207378371741149470822731)
              ·
                refine ⟨16811067557611724206234097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207378371741149470822731 16811067557611724206234097)
                ·
                  refine ⟨12608300668208793154675573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16811067557611724206234097 12608300668208793154675573)
                  ·
                    refine ⟨1182028187644574358250835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12608300668208793154675573 1182028187644574358250835)
                    ·
                      rfl

theorem cell23_6905975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_6905975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6905975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6905975 prefixEnd_6905975 := by exact prefixLift 6905975
  have htrace : WordTrace (prefixWord ++ tailWord_6905975) baseStart_6905975 baseEnd_6905975 := by
    simpa [prefixWord, tailWord_6905975, baseEnd_6905975] using wordTrace_append hprefix tailTrace_6905975
  have hstable : (prefixWord ++ tailWord_6905975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6905975).length < 2 ^ (prefixWord ++ tailWord_6905975).sum := by decide
  have hdescent : baseEnd_6905975 < baseStart_6905975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6905975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906005 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_6906005 : Nat := 118140960795 + 6906005 * 2 ^ 59
def prefixEnd_6906005 : Nat := 4983230072969 + 3 ^ 40 * 6906005 * 2
def baseEnd_6906005 : Nat := 1182033322451119319125789

theorem tailTrace_6906005 : CollatzResearch.WordTrace tailWord_6906005 prefixEnd_6906005 1182033322451119319125789 := by
  unfold tailWord_6906005
  simp only [CollatzResearch.WordTrace]
  refine ⟨251882695345730811598159469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167921796897153874398772979 251882695345730811598159469)
  ·
    refine ⟨94456010754649054349309801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251882695345730811598159469 94456010754649054349309801)
    ·
      refine ⟨70842008065986790761982351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94456010754649054349309801 70842008065986790761982351)
      ·
        refine ⟨106263012098980186142973527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70842008065986790761982351 106263012098980186142973527)
        ·
          refine ⟨159394518148470279214460291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106263012098980186142973527 159394518148470279214460291)
          ·
            refine ⟨239091777222705418821690437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159394518148470279214460291 239091777222705418821690437)
            ·
              refine ⟨44829708229257266029066957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239091777222705418821690437 44829708229257266029066957)
              ·
                refine ⟨16811140585971474760900109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44829708229257266029066957 16811140585971474760900109)
                ·
                  refine ⟨6304177719739303035337541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16811140585971474760900109 6304177719739303035337541)
                  ·
                    refine ⟨1182033322451119319125789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304177719739303035337541 1182033322451119319125789)
                    ·
                      rfl

theorem cell23_6906005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_6906005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906005 prefixEnd_6906005 := by exact prefixLift 6906005
  have htrace : WordTrace (prefixWord ++ tailWord_6906005) baseStart_6906005 baseEnd_6906005 := by
    simpa [prefixWord, tailWord_6906005, baseEnd_6906005] using wordTrace_append hprefix tailTrace_6906005
  have hstable : (prefixWord ++ tailWord_6906005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906005).length < 2 ^ (prefixWord ++ tailWord_6906005).sum := by decide
  have hdescent : baseEnd_6906005 < baseStart_6906005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906012 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6906012 : Nat := 118140960795 + 6906012 * 2 ^ 59
def prefixEnd_6906012 : Nat := 4983230072969 + 3 ^ 40 * 6906012 * 2
def baseEnd_6906012 : Nat := 3546103561717939429989835

theorem tailTrace_6906012 : CollatzResearch.WordTrace tailWord_6906012 prefixEnd_6906012 3546103561717939429989835 := by
  unfold tailWord_6906012
  simp only [CollatzResearch.WordTrace]
  refine ⟨125941475328352725896832145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167921967104470301195776193 125941475328352725896832145)
  ·
    refine ⟨94456106496264544422624109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125941475328352725896832145 94456106496264544422624109)
    ·
      refine ⟨35421039936099204158484041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94456106496264544422624109 35421039936099204158484041)
      ·
        refine ⟨26565779952074403118863031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35421039936099204158484041 26565779952074403118863031)
        ·
          refine ⟨39848669928111604678294547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26565779952074403118863031 39848669928111604678294547)
          ·
            refine ⟨59773004892167407017441821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39848669928111604678294547 59773004892167407017441821)
            ·
              refine ⟨22414876834562777631540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59773004892167407017441821 22414876834562777631540683)
              ·
                refine ⟨33622315251844166447311025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22414876834562777631540683 33622315251844166447311025)
                ·
                  refine ⟨25216736438883124835483269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33622315251844166447311025 25216736438883124835483269)
                  ·
                    refine ⟨4728138082290585906653113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25216736438883124835483269 4728138082290585906653113)
                    ·
                      refine ⟨3546103561717939429989835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728138082290585906653113 3546103561717939429989835)
                      ·
                        rfl

theorem cell23_6906012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6906012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906012 prefixEnd_6906012 := by exact prefixLift 6906012
  have htrace : WordTrace (prefixWord ++ tailWord_6906012) baseStart_6906012 baseEnd_6906012 := by
    simpa [prefixWord, tailWord_6906012, baseEnd_6906012] using wordTrace_append hprefix tailTrace_6906012
  have hstable : (prefixWord ++ tailWord_6906012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906012).length < 2 ^ (prefixWord ++ tailWord_6906012).sum := by decide
  have hdescent : baseEnd_6906012 < baseStart_6906012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906026 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6906026 : Nat := 118140960795 + 6906026 * 2 ^ 59
def prefixEnd_6906026 : Nat := 4983230072969 + 3 ^ 40 * 6906026 * 2
def baseEnd_6906026 : Nat := 1182036916815700791738257

theorem tailTrace_6906026 : CollatzResearch.WordTrace tailWord_6906026 prefixEnd_6906026 1182036916815700791738257 := by
  unfold tailWord_6906026
  simp only [CollatzResearch.WordTrace]
  refine ⟨62970865319663683046168483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167922307519103154789782621 62970865319663683046168483)
  ·
    refine ⟨94456297979495524569252725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62970865319663683046168483 94456297979495524569252725)
    ·
      refine ⟨8855277935577705428367443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94456297979495524569252725 8855277935577705428367443)
      ·
        refine ⟨13282916903366558142551165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855277935577705428367443 13282916903366558142551165)
        ·
          refine ⟨4981093838762459303456687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13282916903366558142551165 4981093838762459303456687)
          ·
            refine ⟨7471640758143688955185031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981093838762459303456687 7471640758143688955185031)
            ·
              refine ⟨11207461137215533432777547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471640758143688955185031 11207461137215533432777547)
              ·
                refine ⟨16811191705823300149166321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207461137215533432777547 16811191705823300149166321)
                ·
                  refine ⟨12608393779367475111874741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16811191705823300149166321 12608393779367475111874741)
                  ·
                    refine ⟨1182036916815700791738257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12608393779367475111874741 1182036916815700791738257)
                    ·
                      rfl

theorem cell23_6906026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6906026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906026 prefixEnd_6906026 := by exact prefixLift 6906026
  have htrace : WordTrace (prefixWord ++ tailWord_6906026) baseStart_6906026 baseEnd_6906026 := by
    simpa [prefixWord, tailWord_6906026, baseEnd_6906026] using wordTrace_append hprefix tailTrace_6906026
  have hstable : (prefixWord ++ tailWord_6906026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906026).length < 2 ^ (prefixWord ++ tailWord_6906026).sum := by decide
  have hdescent : baseEnd_6906026 < baseStart_6906026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906029 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_6906029 : Nat := 118140960795 + 6906029 * 2 ^ 59
def prefixEnd_6906029 : Nat := 4983230072969 + 3 ^ 40 * 6906029 * 2
def baseEnd_6906029 : Nat := 3546112290889065863477257

theorem tailTrace_6906029 : CollatzResearch.WordTrace tailWord_6906029 prefixEnd_6906029 3546112290889065863477257 := by
  unfold tailWord_6906029
  simp only [CollatzResearch.WordTrace]
  refine ⟨251883570697643863697033141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167922380465095909131355427 251883570697643863697033141)
  ·
    refine ⟨23614084752904112221596857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 251883570697643863697033141 23614084752904112221596857)
    ·
      refine ⟨17710563564678084166197643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23614084752904112221596857 17710563564678084166197643)
      ·
        refine ⟨26565845347017126249296465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17710563564678084166197643 26565845347017126249296465)
        ·
          refine ⟨19924384010262844686972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26565845347017126249296465 19924384010262844686972349)
          ·
            refine ⟨7471644003848566757614631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19924384010262844686972349 7471644003848566757614631)
            ·
              refine ⟨11207466005772850136421947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471644003848566757614631 11207466005772850136421947)
              ·
                refine ⟨16811199008659275204632921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207466005772850136421947 16811199008659275204632921)
                ·
                  refine ⟨12608399256494456403474691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16811199008659275204632921 12608399256494456403474691)
                  ·
                    refine ⟨18912598884741684605212037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12608399256494456403474691 18912598884741684605212037)
                    ·
                      refine ⟨3546112290889065863477257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18912598884741684605212037 3546112290889065863477257)
                      ·
                        rfl

theorem cell23_6906029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_6906029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906029 prefixEnd_6906029 := by exact prefixLift 6906029
  have htrace : WordTrace (prefixWord ++ tailWord_6906029) baseStart_6906029 baseEnd_6906029 := by
    simpa [prefixWord, tailWord_6906029, baseEnd_6906029] using wordTrace_append hprefix tailTrace_6906029
  have hstable : (prefixWord ++ tailWord_6906029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906029).length < 2 ^ (prefixWord ++ tailWord_6906029).sum := by decide
  have hdescent : baseEnd_6906029 < baseStart_6906029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906039 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 1, 4]
def baseStart_6906039 : Nat := 118140960795 + 6906039 * 2 ^ 59
def prefixEnd_6906039 : Nat := 4983230072969 + 3 ^ 40 * 6906039 * 2
def baseEnd_6906039 : Nat := 1182039141898536941450737

theorem tailTrace_6906039 : CollatzResearch.WordTrace tailWord_6906039 prefixEnd_6906039 1182039141898536941450737 := by
  unfold tailWord_6906039
  simp only [CollatzResearch.WordTrace]
  refine ⟨251883935427607635404897171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167922623618405090269931447 251883935427607635404897171)
  ·
    refine ⟨377825903141411453107345757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251883935427607635404897171 377825903141411453107345757)
    ·
      refine ⟨141684713678029294915254659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377825903141411453107345757 141684713678029294915254659)
      ·
        refine ⟨212527070517043942372881989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141684713678029294915254659 212527070517043942372881989)
        ·
          refine ⟨39848825721945739194915373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212527070517043942372881989 39848825721945739194915373)
          ·
            refine ⟨14943309645729652198093265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39848825721945739194915373 14943309645729652198093265)
            ·
              refine ⟨11207482234297239148569949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14943309645729652198093265 11207482234297239148569949)
              ·
                refine ⟨4202805837861464680713731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11207482234297239148569949 4202805837861464680713731)
                ·
                  refine ⟨6304208756792197021070597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202805837861464680713731 6304208756792197021070597)
                  ·
                    refine ⟨1182039141898536941450737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304208756792197021070597 1182039141898536941450737)
                    ·
                      rfl

theorem cell23_6906039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_6906039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906039 prefixEnd_6906039 := by exact prefixLift 6906039
  have htrace : WordTrace (prefixWord ++ tailWord_6906039) baseStart_6906039 baseEnd_6906039 := by
    simpa [prefixWord, tailWord_6906039, baseEnd_6906039] using wordTrace_append hprefix tailTrace_6906039
  have hstable : (prefixWord ++ tailWord_6906039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906039).length < 2 ^ (prefixWord ++ tailWord_6906039).sum := by decide
  have hdescent : baseEnd_6906039 < baseStart_6906039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906052 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 6]
def baseStart_6906052 : Nat := 118140960795 + 6906052 * 2 ^ 59
def prefixEnd_6906052 : Nat := 4983230072969 + 3 ^ 40 * 6906052 * 2
def baseEnd_6906052 : Nat := 394013788993791030387739

theorem tailTrace_6906052 : CollatzResearch.WordTrace tailWord_6906052 prefixEnd_6906052 394013788993791030387739 := by
  unfold tailWord_6906052
  simp only [CollatzResearch.WordTrace]
  refine ⟨125942204788280269312560205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167922939717707025750080273 125942204788280269312560205)
  ·
    refine ⟨47228326795605100992210077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125942204788280269312560205 47228326795605100992210077)
    ·
      refine ⟨17710622548351912872078779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47228326795605100992210077 17710622548351912872078779)
      ·
        refine ⟨26565933822527869308118169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17710622548351912872078779 26565933822527869308118169)
        ·
          refine ⟨19924450366895901981088627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26565933822527869308118169 19924450366895901981088627)
          ·
            refine ⟨29886675550343852971632941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19924450366895901981088627 29886675550343852971632941)
            ·
              refine ⟨11207503331378944864362353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29886675550343852971632941 11207503331378944864362353)
              ·
                refine ⟨8405627498534208648271765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11207503331378944864362353 8405627498534208648271765)
                ·
                  refine ⟨394013788993791030387739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8405627498534208648271765 394013788993791030387739)
                  ·
                    rfl

theorem cell23_6906052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_6906052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906052 prefixEnd_6906052 := by exact prefixLift 6906052
  have htrace : WordTrace (prefixWord ++ tailWord_6906052) baseStart_6906052 baseEnd_6906052 := by
    simpa [prefixWord, tailWord_6906052, baseEnd_6906052] using wordTrace_append hprefix tailTrace_6906052
  have hstable : (prefixWord ++ tailWord_6906052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906052).length < 2 ^ (prefixWord ++ tailWord_6906052).sum := by decide
  have hdescent : baseEnd_6906052 < baseStart_6906052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906069 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 6]
def baseStart_6906069 : Nat := 118140960795 + 6906069 * 2 ^ 59
def prefixEnd_6906069 : Nat := 4983230072969 + 3 ^ 40 * 6906069 * 2
def baseEnd_6906069 : Nat := 394014758901693967441897

theorem tailTrace_6906069 : CollatzResearch.WordTrace tailWord_6906069 prefixEnd_6906069 394014758901693967441897 := by
  unfold tailWord_6906069
  simp only [CollatzResearch.WordTrace]
  refine ⟨251885029617498950528489261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167923353078332633685659507 251885029617498950528489261)
  ·
    refine ⟨94456886106562106448183473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251885029617498950528489261 94456886106562106448183473)
    ·
      refine ⟨70842664579921579836137605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94456886106562106448183473 70842664579921579836137605)
      ·
        refine ⟨13282999608735296219275801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70842664579921579836137605 13282999608735296219275801)
        ·
          refine ⟨9962249706551472164456851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13282999608735296219275801 9962249706551472164456851)
          ·
            refine ⟨14943374559827208246685277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962249706551472164456851 14943374559827208246685277)
            ·
              refine ⟨5603765459935203092506979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14943374559827208246685277 5603765459935203092506979)
              ·
                refine ⟨8405648189902804638760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603765459935203092506979 8405648189902804638760469)
                ·
                  refine ⟨394014758901693967441897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8405648189902804638760469 394014758901693967441897)
                  ·
                    rfl

theorem cell23_6906069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_6906069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906069 prefixEnd_6906069 := by exact prefixLift 6906069
  have htrace : WordTrace (prefixWord ++ tailWord_6906069) baseStart_6906069 baseEnd_6906069 := by
    simpa [prefixWord, tailWord_6906069, baseEnd_6906069] using wordTrace_append hprefix tailTrace_6906069
  have hstable : (prefixWord ++ tailWord_6906069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906069).length < 2 ^ (prefixWord ++ tailWord_6906069).sum := by decide
  have hdescent : baseEnd_6906069 < baseStart_6906069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906072 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_6906072 : Nat := 118140960795 + 6906072 * 2 ^ 59
def prefixEnd_6906072 : Nat := 4983230072969 + 3 ^ 40 * 6906072 * 2
def baseEnd_6906072 : Nat := 3546134370557209195239559

theorem tailTrace_6906072 : CollatzResearch.WordTrace tailWord_6906072 prefixEnd_6906072 3546134370557209195239559 := by
  unfold tailWord_6906072
  simp only [CollatzResearch.WordTrace]
  refine ⟨125942569518244041020424235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167923426024325388027232313 125942569518244041020424235)
  ·
    refine ⟨188913854277366061530636353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125942569518244041020424235 188913854277366061530636353)
    ·
      refine ⟨141685390708024546147977265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188913854277366061530636353 141685390708024546147977265)
      ·
        refine ⟨106264043031018409610982949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141685390708024546147977265 106264043031018409610982949)
        ·
          refine ⟨19924508068315951802059303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106264043031018409610982949 19924508068315951802059303)
          ·
            refine ⟨29886762102473927703088955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19924508068315951802059303 29886762102473927703088955)
            ·
              refine ⟨44830143153710891554633433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29886762102473927703088955 44830143153710891554633433)
              ·
                refine ⟨33622607365283168665975075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44830143153710891554633433 33622607365283168665975075)
                ·
                  refine ⟨50433911047924752998962613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33622607365283168665975075 50433911047924752998962613)
                  ·
                    refine ⟨4728179160742945593652745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50433911047924752998962613 4728179160742945593652745)
                    ·
                      refine ⟨3546134370557209195239559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728179160742945593652745 3546134370557209195239559)
                      ·
                        rfl

theorem cell23_6906072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_6906072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906072 prefixEnd_6906072 := by exact prefixLift 6906072
  have htrace : WordTrace (prefixWord ++ tailWord_6906072) baseStart_6906072 baseEnd_6906072 := by
    simpa [prefixWord, tailWord_6906072, baseEnd_6906072] using wordTrace_append hprefix tailTrace_6906072
  have hstable : (prefixWord ++ tailWord_6906072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906072).length < 2 ^ (prefixWord ++ tailWord_6906072).sum := by decide
  have hdescent : baseEnd_6906072 < baseStart_6906072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906129 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_6906129 : Nat := 118140960795 + 6906129 * 2 ^ 59
def prefixEnd_6906129 : Nat := 4983230072969 + 3 ^ 40 * 6906129 * 2
def baseEnd_6906129 : Nat := 1182054546318171824075599

theorem tailTrace_6906129 : CollatzResearch.WordTrace tailWord_6906129 prefixEnd_6906129 1182054546318171824075599 := by
  unfold tailWord_6906129
  simp only [CollatzResearch.WordTrace]
  refine ⟨251887217997281580775673441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167924811998187720517115627 251887217997281580775673441)
  ·
    refine ⟨188915413497961185581755081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251887217997281580775673441 188915413497961185581755081)
    ·
      refine ⟨141686560123470889186316311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188915413497961185581755081 141686560123470889186316311)
      ·
        refine ⟨212529840185206333779474467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141686560123470889186316311 212529840185206333779474467)
        ·
          refine ⟨318794760277809500669211701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212529840185206333779474467 318794760277809500669211701)
          ·
            refine ⟨29887008776044640687738597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318794760277809500669211701 29887008776044640687738597)
            ·
              refine ⟨5603814145508370128950987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29887008776044640687738597 5603814145508370128950987)
              ·
                refine ⟨8405721218262555193426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603814145508370128950987 8405721218262555193426481)
                ·
                  refine ⟨6304290913696916395069861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8405721218262555193426481 6304290913696916395069861)
                  ·
                    refine ⟨1182054546318171824075599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6304290913696916395069861 1182054546318171824075599)
                    ·
                      rfl

theorem cell23_6906129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_6906129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906129 prefixEnd_6906129 := by exact prefixLift 6906129
  have htrace : WordTrace (prefixWord ++ tailWord_6906129) baseStart_6906129 baseEnd_6906129 := by
    simpa [prefixWord, tailWord_6906129, baseEnd_6906129] using wordTrace_append hprefix tailTrace_6906129
  have hstable : (prefixWord ++ tailWord_6906129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906129).length < 2 ^ (prefixWord ++ tailWord_6906129).sum := by decide
  have hdescent : baseEnd_6906129 < baseStart_6906129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906170 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_6906170 : Nat := 118140960795 + 6906170 * 2 ^ 59
def prefixEnd_6906170 : Nat := 4983230072969 + 3 ^ 40 * 6906170 * 2
def baseEnd_6906170 : Nat := 3546184691661349811814109

theorem tailTrace_6906170 : CollatzResearch.WordTrace tailWord_6906170 prefixEnd_6906170 3546184691661349811814109 := by
  unfold tailWord_6906170
  simp only [CollatzResearch.WordTrace]
  refine ⟨62972178347533261194478991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167925808926755363185277309 62972178347533261194478991)
  ·
    refine ⟨94458267521299891791718487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62972178347533261194478991 94458267521299891791718487)
    ·
      refine ⟨141687401281949837687577731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94458267521299891791718487 141687401281949837687577731)
      ·
        refine ⟨212531101922924756531366597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141687401281949837687577731 212531101922924756531366597)
        ·
          refine ⟨39849581610548391849631237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212531101922924756531366597 39849581610548391849631237)
          ·
            refine ⟨7471796551977823471805857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39849581610548391849631237 7471796551977823471805857)
            ·
              refine ⟨5603847413983367603854393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471796551977823471805857 5603847413983367603854393)
              ·
                refine ⟨4202885560487525702890795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603847413983367603854393 4202885560487525702890795)
                ·
                  refine ⟨6304328340731288554336193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202885560487525702890795 6304328340731288554336193)
                  ·
                    refine ⟨4728246255548466415752145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304328340731288554336193 4728246255548466415752145)
                    ·
                      refine ⟨3546184691661349811814109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728246255548466415752145 3546184691661349811814109)
                      ·
                        rfl

theorem cell23_6906170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_6906170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906170 prefixEnd_6906170 := by exact prefixLift 6906170
  have htrace : WordTrace (prefixWord ++ tailWord_6906170) baseStart_6906170 baseEnd_6906170 := by
    simpa [prefixWord, tailWord_6906170, baseEnd_6906170] using wordTrace_append hprefix tailTrace_6906170
  have hstable : (prefixWord ++ tailWord_6906170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906170).length < 2 ^ (prefixWord ++ tailWord_6906170).sum := by decide
  have hdescent : baseEnd_6906170 < baseStart_6906170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906175 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_6906175 : Nat := 118140960795 + 6906175 * 2 ^ 59
def prefixEnd_6906175 : Nat := 4983230072969 + 3 ^ 40 * 6906175 * 2
def baseEnd_6906175 : Nat := 3546187259064622292251585

theorem tailTrace_6906175 : CollatzResearch.WordTrace tailWord_6906175 prefixEnd_6906175 3546187259064622292251585 := by
  unfold tailWord_6906175
  simp only [CollatzResearch.WordTrace]
  refine ⟨251888895755114930631847979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167925930503409953754565319 251888895755114930631847979)
  ·
    refine ⟨377833343632672395947771969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251888895755114930631847979 377833343632672395947771969)
    ·
      refine ⟨283375007724504296960828977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377833343632672395947771969 283375007724504296960828977)
      ·
        refine ⟨212531255793378222720621733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283375007724504296960828977 212531255793378222720621733)
        ·
          refine ⟨39849610461258416760116575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212531255793378222720621733 39849610461258416760116575)
          ·
            refine ⟨59774415691887625140174863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39849610461258416760116575 59774415691887625140174863)
            ·
              refine ⟨89661623537831437710262295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59774415691887625140174863 89661623537831437710262295)
              ·
                refine ⟨134492435306747156565393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89661623537831437710262295 134492435306747156565393443)
                ·
                  refine ⟨201738652960120734848090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134492435306747156565393443 201738652960120734848090165)
                  ·
                    refine ⟨18912998715011318892008453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201738652960120734848090165 18912998715011318892008453)
                    ·
                      refine ⟨3546187259064622292251585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18912998715011318892008453 3546187259064622292251585)
                      ·
                        rfl

theorem cell23_6906175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_6906175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906175 prefixEnd_6906175 := by exact prefixLift 6906175
  have htrace : WordTrace (prefixWord ++ tailWord_6906175) baseStart_6906175 baseEnd_6906175 := by
    simpa [prefixWord, tailWord_6906175, baseEnd_6906175] using wordTrace_append hprefix tailTrace_6906175
  have hstable : (prefixWord ++ tailWord_6906175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906175).length < 2 ^ (prefixWord ++ tailWord_6906175).sum := by decide
  have hdescent : baseEnd_6906175 < baseStart_6906175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906195 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_6906195 : Nat := 118140960795 + 6906195 * 2 ^ 59
def prefixEnd_6906195 : Nat := 4983230072969 + 3 ^ 40 * 6906195 * 2
def baseEnd_6906195 : Nat := 3546197528677712214001493

theorem tailTrace_6906195 : CollatzResearch.WordTrace tailWord_6906195 prefixEnd_6906195 3546197528677712214001493 := by
  unfold tailWord_6906195
  simp only [CollatzResearch.WordTrace]
  refine ⟨251889625215042474047576039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167926416810028316031717359 251889625215042474047576039)
  ·
    refine ⟨377834437822563711071364059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251889625215042474047576039 377834437822563711071364059)
    ·
      refine ⟨566751656733845566607046089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377834437822563711071364059 566751656733845566607046089)
      ·
        refine ⟨425063742550384174955284567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566751656733845566607046089 425063742550384174955284567)
        ·
          refine ⟨637595613825576262432926851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425063742550384174955284567 637595613825576262432926851)
          ·
            refine ⟨956393420738364393649390277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637595613825576262432926851 956393420738364393649390277)
            ·
              refine ⟨179323766388443323809260677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 956393420738364393649390277 179323766388443323809260677)
              ·
                refine ⟨33623206197833123214236377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179323766388443323809260677 33623206197833123214236377)
                ·
                  refine ⟨25217404648374842410677283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33623206197833123214236377 25217404648374842410677283)
                  ·
                    refine ⟨37826106972562263616015925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25217404648374842410677283 37826106972562263616015925)
                    ·
                      refine ⟨3546197528677712214001493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37826106972562263616015925 3546197528677712214001493)
                      ·
                        rfl

theorem cell23_6906195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_6906195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906195 prefixEnd_6906195 := by exact prefixLift 6906195
  have htrace : WordTrace (prefixWord ++ tailWord_6906195) baseStart_6906195 baseEnd_6906195 := by
    simpa [prefixWord, tailWord_6906195, baseEnd_6906195] using wordTrace_append hprefix tailTrace_6906195
  have hstable : (prefixWord ++ tailWord_6906195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906195).length < 2 ^ (prefixWord ++ tailWord_6906195).sum := by decide
  have hdescent : baseEnd_6906195 < baseStart_6906195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906213 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_6906213 : Nat := 118140960795 + 6906213 * 2 ^ 59
def prefixEnd_6906213 : Nat := 4983230072969 + 3 ^ 40 * 6906213 * 2
def baseEnd_6906213 : Nat := 3546206771329493143576411

theorem tailTrace_6906213 : CollatzResearch.WordTrace tailWord_6906213 prefixEnd_6906213 3546206771329493143576411 := by
  unfold tailWord_6906213
  simp only [CollatzResearch.WordTrace]
  refine ⟨251890281728977263121731293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167926854485984842081154195 251890281728977263121731293)
  ·
    refine ⟨94458855648366473670649235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251890281728977263121731293 94458855648366473670649235)
    ·
      refine ⟨141688283472549710505973853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94458855648366473670649235 141688283472549710505973853)
      ·
        refine ⟨53133106302206141439740195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141688283472549710505973853 53133106302206141439740195)
        ·
          refine ⟨79699659453309212159610293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53133106302206141439740195 79699659453309212159610293)
          ·
            refine ⟨7471843073747738639963465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79699659453309212159610293 7471843073747738639963465)
            ·
              refine ⟨5603882305310803979972599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7471843073747738639963465 5603882305310803979972599)
              ·
                refine ⟨8405823457966205969958899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603882305310803979972599 8405823457966205969958899)
                ·
                  refine ⟨12608735186949308954938349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8405823457966205969958899 12608735186949308954938349)
                  ·
                    refine ⟨4728275695105990858101881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12608735186949308954938349 4728275695105990858101881)
                    ·
                      refine ⟨3546206771329493143576411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728275695105990858101881 3546206771329493143576411)
                      ·
                        rfl

theorem cell23_6906213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_6906213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906213 prefixEnd_6906213 := by exact prefixLift 6906213
  have htrace : WordTrace (prefixWord ++ tailWord_6906213) baseStart_6906213 baseEnd_6906213 := by
    simpa [prefixWord, tailWord_6906213, baseEnd_6906213] using wordTrace_append hprefix tailTrace_6906213
  have hstable : (prefixWord ++ tailWord_6906213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906213).length < 2 ^ (prefixWord ++ tailWord_6906213).sum := by decide
  have hdescent : baseEnd_6906213 < baseStart_6906213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906226 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_6906226 : Nat := 118140960795 + 6906226 * 2 ^ 59
def prefixEnd_6906226 : Nat := 4983230072969 + 3 ^ 40 * 6906226 * 2
def baseEnd_6906226 : Nat := 3546213446578001592713851

theorem tailTrace_6906226 : CollatzResearch.WordTrace tailWord_6906226 prefixEnd_6906226 3546213446578001592713851 := by
  unfold tailWord_6906226
  simp only [CollatzResearch.WordTrace]
  refine ⟨62972688969482541585488633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167927170585286777561303021 62972688969482541585488633)
  ·
    refine ⟨47229516727111906189116475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62972688969482541585488633 47229516727111906189116475)
    ·
      refine ⟨70844275090667859283674713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47229516727111906189116475 70844275090667859283674713)
      ·
        refine ⟨53133206318000894462756035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70844275090667859283674713 53133206318000894462756035)
        ·
          refine ⟨79699809477001341694134053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53133206318000894462756035 79699809477001341694134053)
          ·
            refine ⟨14943714276937751567650135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79699809477001341694134053 14943714276937751567650135)
            ·
              refine ⟨22415571415406627351475203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14943714276937751567650135 22415571415406627351475203)
              ·
                refine ⟨33623357123109941027212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22415571415406627351475203 33623357123109941027212805)
                ·
                  refine ⟨6304379460583113942602401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33623357123109941027212805 6304379460583113942602401)
                  ·
                    refine ⟨4728284595437335456951801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304379460583113942602401 4728284595437335456951801)
                    ·
                      refine ⟨3546213446578001592713851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728284595437335456951801 3546213446578001592713851)
                      ·
                        rfl

theorem cell23_6906226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_6906226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906226 prefixEnd_6906226 := by exact prefixLift 6906226
  have htrace : WordTrace (prefixWord ++ tailWord_6906226) baseStart_6906226 baseEnd_6906226 := by
    simpa [prefixWord, tailWord_6906226, baseEnd_6906226] using wordTrace_append hprefix tailTrace_6906226
  have hstable : (prefixWord ++ tailWord_6906226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906226).length < 2 ^ (prefixWord ++ tailWord_6906226).sum := by decide
  have hdescent : baseEnd_6906226 < baseStart_6906226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906243 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 4, 2]
def baseStart_6906243 : Nat := 118140960795 + 6906243 * 2 ^ 59
def prefixEnd_6906243 : Nat := 4983230072969 + 3 ^ 40 * 6906243 * 2
def baseEnd_6906243 : Nat := 3546222175749128026201273

theorem tailTrace_6906243 : CollatzResearch.WordTrace tailWord_6906243 prefixEnd_6906243 3546222175749128026201273 := by
  unfold tailWord_6906243
  simp only [CollatzResearch.WordTrace]
  refine ⟨251891375918868578245323383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167927583945912385496882255 251891375918868578245323383)
  ·
    refine ⟨377837063878302867367985075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251891375918868578245323383 377837063878302867367985075)
    ·
      refine ⟨566755595817454301051977613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377837063878302867367985075 566755595817454301051977613)
      ·
        refine ⟨212533348431545362894491605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566755595817454301051977613 212533348431545362894491605)
        ·
          refine ⟨4981250353864344442839647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212533348431545362894491605 4981250353864344442839647)
          ·
            refine ⟨7471875530796516664259471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981250353864344442839647 7471875530796516664259471)
            ·
              refine ⟨11207813296194774996389207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471875530796516664259471 11207813296194774996389207)
              ·
                refine ⟨16811719944292162494583811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207813296194774996389207 16811719944292162494583811)
                ·
                  refine ⟨25217579916438243741875717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16811719944292162494583811 25217579916438243741875717)
                  ·
                    refine ⟨4728296234332170701601697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25217579916438243741875717 4728296234332170701601697)
                    ·
                      refine ⟨3546222175749128026201273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728296234332170701601697 3546222175749128026201273)
                      ·
                        rfl

theorem cell23_6906243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_6906243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906243 prefixEnd_6906243 := by exact prefixLift 6906243
  have htrace : WordTrace (prefixWord ++ tailWord_6906243) baseStart_6906243 baseEnd_6906243 := by
    simpa [prefixWord, tailWord_6906243, baseEnd_6906243] using wordTrace_append hprefix tailTrace_6906243
  have hstable : (prefixWord ++ tailWord_6906243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906243).length < 2 ^ (prefixWord ++ tailWord_6906243).sum := by decide
  have hdescent : baseEnd_6906243 < baseStart_6906243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906266 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 5]
def baseStart_6906266 : Nat := 118140960795 + 6906266 * 2 ^ 59
def prefixEnd_6906266 : Nat := 4983230072969 + 3 ^ 40 * 6906266 * 2
def baseEnd_6906266 : Nat := 394025998422686826245963

theorem tailTrace_6906266 : CollatzResearch.WordTrace tailWord_6906266 prefixEnd_6906266 394025998422686826245963 := by
  unfold tailWord_6906266
  simp only [CollatzResearch.WordTrace]
  refine ⟨62973053699446313293352663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167928143198523502115607101 62973053699446313293352663)
  ·
    refine ⟨94459580549169469940028995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62973053699446313293352663 94459580549169469940028995)
    ·
      refine ⟨141689370823754204910043493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94459580549169469940028995 141689370823754204910043493)
      ·
        refine ⟨26566757029453913420633155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141689370823754204910043493 26566757029453913420633155)
        ·
          refine ⟨39850135544180870130949733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26566757029453913420633155 39850135544180870130949733)
          ·
            refine ⟨7471900414533913149553075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39850135544180870130949733 7471900414533913149553075)
            ·
              refine ⟨11207850621800869724329613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471900414533913149553075 11207850621800869724329613)
              ·
                refine ⟨4202943983175326146623605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11207850621800869724329613 4202943983175326146623605)
                ·
                  refine ⟨394025998422686826245963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4202943983175326146623605 394025998422686826245963)
                  ·
                    rfl

theorem cell23_6906266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_6906266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906266 prefixEnd_6906266 := by exact prefixLift 6906266
  have htrace : WordTrace (prefixWord ++ tailWord_6906266) baseStart_6906266 baseEnd_6906266 := by
    simpa [prefixWord, tailWord_6906266, baseEnd_6906266] using wordTrace_append hprefix tailTrace_6906266
  have hstable : (prefixWord ++ tailWord_6906266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906266).length < 2 ^ (prefixWord ++ tailWord_6906266).sum := by decide
  have hdescent : baseEnd_6906266 < baseStart_6906266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906279 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6906279 : Nat := 118140960795 + 6906279 * 2 ^ 59
def prefixEnd_6906279 : Nat := 4983230072969 + 3 ^ 40 * 6906279 * 2
def baseEnd_6906279 : Nat := 1182080220350896628450369

theorem tailTrace_6906279 : CollatzResearch.WordTrace tailWord_6906279 prefixEnd_6906279 1182080220350896628450369 := by
  unfold tailWord_6906279
  simp only [CollatzResearch.WordTrace]
  refine ⟨251892688946738156393633891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167928459297825437595755927 251892688946738156393633891)
  ·
    refine ⟨377839033420107234590450837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251892688946738156393633891 377839033420107234590450837)
    ·
      refine ⟨17711204691567526621427383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 377839033420107234590450837 17711204691567526621427383)
      ·
        refine ⟨26566807037351289932141075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711204691567526621427383 26566807037351289932141075)
        ·
          refine ⟨39850210556026934898211613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26566807037351289932141075 39850210556026934898211613)
          ·
            refine ⟨14943828958510100586829355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39850210556026934898211613 14943828958510100586829355)
            ·
              refine ⟨22415743437765150880244033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14943828958510100586829355 22415743437765150880244033)
              ·
                refine ⟨16811807578323863160183025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22415743437765150880244033 16811807578323863160183025)
                ·
                  refine ⟨12608855683742897370137269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16811807578323863160183025 12608855683742897370137269)
                  ·
                    refine ⟨1182080220350896628450369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12608855683742897370137269 1182080220350896628450369)
                    ·
                      rfl

theorem cell23_6906279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6906279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906279 prefixEnd_6906279 := by exact prefixLift 6906279
  have htrace : WordTrace (prefixWord ++ tailWord_6906279) baseStart_6906279 baseEnd_6906279 := by
    simpa [prefixWord, tailWord_6906279, baseEnd_6906279] using wordTrace_append hprefix tailTrace_6906279
  have hstable : (prefixWord ++ tailWord_6906279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906279).length < 2 ^ (prefixWord ++ tailWord_6906279).sum := by decide
  have hdescent : baseEnd_6906279 < baseStart_6906279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906316 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_6906316 : Nat := 118140960795 + 6906316 * 2 ^ 59
def prefixEnd_6906316 : Nat := 4983230072969 + 3 ^ 40 * 6906316 * 2
def baseEnd_6906316 : Nat := 3546259659836906240588437

theorem tailTrace_6906316 : CollatzResearch.WordTrace tailWord_6906316 prefixEnd_6906316 3546259659836906240588437 := by
  unfold tailWord_6906316
  simp only [CollatzResearch.WordTrace]
  refine ⟨125947019223802055856365401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167929358965069407808487201 125947019223802055856365401)
  ·
    refine ⟨94460264417851541892274051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125947019223802055856365401 94460264417851541892274051)
    ·
      refine ⟨141690396626777312838411077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94460264417851541892274051 141690396626777312838411077)
      ·
        refine ⟨26566949367520746157202077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141690396626777312838411077 26566949367520746157202077)
        ·
          refine ⟨9962606012820279808950779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26566949367520746157202077 9962606012820279808950779)
          ·
            refine ⟨14943909019230419713426169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962606012820279808950779 14943909019230419713426169)
            ·
              refine ⟨11207931764422814785069627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14943909019230419713426169 11207931764422814785069627)
              ·
                refine ⟨16811897646634222177604441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207931764422814785069627 16811897646634222177604441)
                ·
                  refine ⟨12608923234975666633203331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16811897646634222177604441 12608923234975666633203331)
                  ·
                    refine ⟨18913384852463499949804997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12608923234975666633203331 18913384852463499949804997)
                    ·
                      refine ⟨3546259659836906240588437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18913384852463499949804997 3546259659836906240588437)
                      ·
                        rfl

theorem cell23_6906316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_6906316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906316 prefixEnd_6906316 := by exact prefixLift 6906316
  have htrace : WordTrace (prefixWord ++ tailWord_6906316) baseStart_6906316 baseEnd_6906316 := by
    simpa [prefixWord, tailWord_6906316, baseEnd_6906316] using wordTrace_append hprefix tailTrace_6906316
  have hstable : (prefixWord ++ tailWord_6906316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906316).length < 2 ^ (prefixWord ++ tailWord_6906316).sum := by decide
  have hdescent : baseEnd_6906316 < baseStart_6906316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906352 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_6906352 : Nat := 118140960795 + 6906352 * 2 ^ 59
def prefixEnd_6906352 : Nat := 4983230072969 + 3 ^ 40 * 6906352 * 2
def baseEnd_6906352 : Nat := 1182092715046822699912757

theorem tailTrace_6906352 : CollatzResearch.WordTrace tailWord_6906352 prefixEnd_6906352 1182092715046822699912757 := by
  unfold tailWord_6906352
  simp only [CollatzResearch.WordTrace]
  refine ⟨125947675737736844930520655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167930234316982459907360873 125947675737736844930520655)
  ·
    refine ⟨188921513606605267395780983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125947675737736844930520655 188921513606605267395780983)
    ·
      refine ⟨283382270409907901093671475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188921513606605267395780983 283382270409907901093671475)
      ·
        refine ⟨425073405614861851640507213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283382270409907901093671475 425073405614861851640507213)
        ·
          refine ⟨159402527105573194365190205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425073405614861851640507213 159402527105573194365190205)
          ·
            refine ⟨59775947664589947886946327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159402527105573194365190205 59775947664589947886946327)
            ·
              refine ⟨89663921496884921830419491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59775947664589947886946327 89663921496884921830419491)
              ·
                refine ⟨134495882245327382745629237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89663921496884921830419491 134495882245327382745629237)
                ·
                  refine ⟨12608988960499442132402741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134495882245327382745629237 12608988960499442132402741)
                  ·
                    refine ⟨1182092715046822699912757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12608988960499442132402741 1182092715046822699912757)
                    ·
                      rfl

theorem cell23_6906352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_6906352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906352 prefixEnd_6906352 := by exact prefixLift 6906352
  have htrace : WordTrace (prefixWord ++ tailWord_6906352) baseStart_6906352 baseEnd_6906352 := by
    simpa [prefixWord, tailWord_6906352, baseEnd_6906352] using wordTrace_append hprefix tailTrace_6906352
  have hstable : (prefixWord ++ tailWord_6906352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906352).length < 2 ^ (prefixWord ++ tailWord_6906352).sum := by decide
  have hdescent : baseEnd_6906352 < baseStart_6906352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906369 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_6906369 : Nat := 118140960795 + 6906369 * 2 ^ 59
def prefixEnd_6906369 : Nat := 4983230072969 + 3 ^ 40 * 6906369 * 2
def baseEnd_6906369 : Nat := 1182095624770531511075231

theorem tailTrace_6906369 : CollatzResearch.WordTrace tailWord_6906369 prefixEnd_6906369 1182095624770531511075231 := by
  unfold tailWord_6906369
  simp only [CollatzResearch.WordTrace]
  refine ⟨251895971516412101764410161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167930647677608067842940107 251895971516412101764410161)
  ·
    refine ⟨188921978637309076323307621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251895971516412101764410161 188921978637309076323307621)
    ·
      refine ⟨35422870994495451810620179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188921978637309076323307621 35422870994495451810620179)
      ·
        refine ⟨53134306491743177715930269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35422870994495451810620179 53134306491743177715930269)
        ·
          refine ⟨19925364934403691643473851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53134306491743177715930269 19925364934403691643473851)
          ·
            refine ⟨29888047401605537465210777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19925364934403691643473851 29888047401605537465210777)
            ·
              refine ⟨22416035551204153098908083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29888047401605537465210777 22416035551204153098908083)
              ·
                refine ⟨33624053326806229648362125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22416035551204153098908083 33624053326806229648362125)
                ·
                  refine ⟨12609019997552336118135797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33624053326806229648362125 12609019997552336118135797)
                  ·
                    refine ⟨1182095624770531511075231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12609019997552336118135797 1182095624770531511075231)
                    ·
                      rfl

theorem cell23_6906369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_6906369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906369 prefixEnd_6906369 := by exact prefixLift 6906369
  have htrace : WordTrace (prefixWord ++ tailWord_6906369) baseStart_6906369 baseEnd_6906369 := by
    simpa [prefixWord, tailWord_6906369, baseEnd_6906369] using wordTrace_append hprefix tailTrace_6906369
  have hstable : (prefixWord ++ tailWord_6906369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906369).length < 2 ^ (prefixWord ++ tailWord_6906369).sum := by decide
  have hdescent : baseEnd_6906369 < baseStart_6906369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906370 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_6906370 : Nat := 118140960795 + 6906370 * 2 ^ 59
def prefixEnd_6906370 : Nat := 4983230072969 + 3 ^ 40 * 6906370 * 2
def baseEnd_6906370 : Nat := 3546287387792249029313189

theorem tailTrace_6906370 : CollatzResearch.WordTrace tailWord_6906370 prefixEnd_6906370 3546287387792249029313189 := by
  unfold tailWord_6906370
  simp only [CollatzResearch.WordTrace]
  refine ⟨62974001997352119733799141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167930671992938985956797709 62974001997352119733799141)
  ·
    refine ⟨11807625374503522450087339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62974001997352119733799141 11807625374503522450087339)
    ·
      refine ⟨17711438061755283675131009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807625374503522450087339 17711438061755283675131009)
      ·
        refine ⟨13283578546316462756348257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17711438061755283675131009 13283578546316462756348257)
        ·
          refine ⟨9962683909737347067261193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13283578546316462756348257 9962683909737347067261193)
          ·
            refine ⟨7472012932303010300445895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962683909737347067261193 7472012932303010300445895)
            ·
              refine ⟨11208019398454515450668843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472012932303010300445895 11208019398454515450668843)
              ·
                refine ⟨16812029097681773176003265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208019398454515450668843 16812029097681773176003265)
                ·
                  refine ⟨12609021823261329882002449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16812029097681773176003265 12609021823261329882002449)
                  ·
                    refine ⟨9456766367445997411501837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12609021823261329882002449 9456766367445997411501837)
                    ·
                      refine ⟨3546287387792249029313189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456766367445997411501837 3546287387792249029313189)
                      ·
                        rfl

theorem cell23_6906370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_6906370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906370 prefixEnd_6906370 := by exact prefixLift 6906370
  have htrace : WordTrace (prefixWord ++ tailWord_6906370) baseStart_6906370 baseEnd_6906370 := by
    simpa [prefixWord, tailWord_6906370, baseEnd_6906370] using wordTrace_append hprefix tailTrace_6906370
  have hstable : (prefixWord ++ tailWord_6906370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906370).length < 2 ^ (prefixWord ++ tailWord_6906370).sum := by decide
  have hdescent : baseEnd_6906370 < baseStart_6906370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906420 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6906420 : Nat := 118140960795 + 6906420 * 2 ^ 59
def prefixEnd_6906420 : Nat := 4983230072969 + 3 ^ 40 * 6906420 * 2
def baseEnd_6906420 : Nat := 1182104353941657944562653

theorem tailTrace_6906420 : CollatzResearch.WordTrace tailWord_6906420 prefixEnd_6906420 1182104353941657944562653 := by
  unfold tailWord_6906420
  simp only [CollatzResearch.WordTrace]
  refine ⟨125948915819613668737258357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167931887759484891649677809 125948915819613668737258357)
  ·
    refine ⟨11807710858088781444117971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125948915819613668737258357 11807710858088781444117971)
    ·
      refine ⟨17711566287133172166176957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807710858088781444117971 17711566287133172166176957)
      ·
        refine ⟨6641837357674939562316359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17711566287133172166176957 6641837357674939562316359)
        ·
          refine ⟨9962756036512409343474539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641837357674939562316359 9962756036512409343474539)
          ·
            refine ⟨14944134054768614015211809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962756036512409343474539 14944134054768614015211809)
            ·
              refine ⟨11208100541076460511408857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14944134054768614015211809 11208100541076460511408857)
              ·
                refine ⟨8406075405807345383556643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11208100541076460511408857 8406075405807345383556643)
                ·
                  refine ⟨12609113108711018075334965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406075405807345383556643 12609113108711018075334965)
                  ·
                    refine ⟨1182104353941657944562653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12609113108711018075334965 1182104353941657944562653)
                    ·
                      rfl

theorem cell23_6906420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6906420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906420 prefixEnd_6906420 := by exact prefixLift 6906420
  have htrace : WordTrace (prefixWord ++ tailWord_6906420) baseStart_6906420 baseEnd_6906420 := by
    simpa [prefixWord, tailWord_6906420, baseEnd_6906420] using wordTrace_append hprefix tailTrace_6906420
  have hstable : (prefixWord ++ tailWord_6906420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906420).length < 2 ^ (prefixWord ++ tailWord_6906420).sum := by decide
  have hdescent : baseEnd_6906420 < baseStart_6906420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906426 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_6906426 : Nat := 118140960795 + 6906426 * 2 ^ 59
def prefixEnd_6906426 : Nat := 4983230072969 + 3 ^ 40 * 6906426 * 2
def baseEnd_6906426 : Nat := 3546316142708900810212931

theorem tailTrace_6906426 : CollatzResearch.WordTrace tailWord_6906426 prefixEnd_6906426 3546316142708900810212931 := by
  unfold tailWord_6906426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62974512619301400124808783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167932033651470400332823421 62974512619301400124808783)
  ·
    refine ⟨94461768928952100187213175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62974512619301400124808783 94461768928952100187213175)
    ·
      refine ⟨141692653393428150280819763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94461768928952100187213175 141692653393428150280819763)
      ·
        refine ⟨212538980090142225421229645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141692653393428150280819763 212538980090142225421229645)
        ·
          refine ⟨79702117533803334532961117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212538980090142225421229645 79702117533803334532961117)
          ·
            refine ⟨29888294075176250449860419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79702117533803334532961117 29888294075176250449860419)
            ·
              refine ⟨44832441112764375674790629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29888294075176250449860419 44832441112764375674790629)
              ·
                refine ⟨8406082708643320439023243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44832441112764375674790629 8406082708643320439023243)
                ·
                  refine ⟨12609124062964980658534865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406082708643320439023243 12609124062964980658534865)
                  ·
                    refine ⟨9456843047223735493901149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12609124062964980658534865 9456843047223735493901149)
                    ·
                      refine ⟨3546316142708900810212931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456843047223735493901149 3546316142708900810212931)
                      ·
                        rfl

theorem cell23_6906426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_6906426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906426 prefixEnd_6906426 := by exact prefixLift 6906426
  have htrace : WordTrace (prefixWord ++ tailWord_6906426) baseStart_6906426 baseEnd_6906426 := by
    simpa [prefixWord, tailWord_6906426, baseEnd_6906426] using wordTrace_append hprefix tailTrace_6906426
  have hstable : (prefixWord ++ tailWord_6906426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906426).length < 2 ^ (prefixWord ++ tailWord_6906426).sum := by decide
  have hdescent : baseEnd_6906426 < baseStart_6906426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906429 : List Nat := [1, 4, 1, 3, 2, 2, 1, 9]
def baseStart_6906429 : Nat := 118140960795 + 6906429 * 2 ^ 59
def prefixEnd_6906429 : Nat := 4983230072969 + 3 ^ 40 * 6906429 * 2
def baseEnd_6906429 : Nat := 131345099375957936980571

theorem tailTrace_6906429 : CollatzResearch.WordTrace tailWord_6906429 prefixEnd_6906429 131345099375957936980571 := by
  unfold tailWord_6906429
  simp only [CollatzResearch.WordTrace]
  refine ⟨251898159896194732011594341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167932106597463154674396227 251898159896194732011594341)
  ·
    refine ⟨47230904980536512252173939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251898159896194732011594341 47230904980536512252173939)
    ·
      refine ⟨70846357470804768378260909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47230904980536512252173939 70846357470804768378260909)
      ·
        refine ⟨26567384051551788141847841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70846357470804768378260909 26567384051551788141847841)
        ·
          refine ⟨19925538038663841106385881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26567384051551788141847841 19925538038663841106385881)
          ·
            refine ⟨14944153528997880829789411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19925538038663841106385881 14944153528997880829789411)
            ·
              refine ⟨22416230293496821244684117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14944153528997880829789411 22416230293496821244684117)
              ·
                refine ⟨131345099375957936980571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22416230293496821244684117 131345099375957936980571)
                ·
                  rfl

theorem cell23_6906429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 9].length) (baseStart_6906429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906429 prefixEnd_6906429 := by exact prefixLift 6906429
  have htrace : WordTrace (prefixWord ++ tailWord_6906429) baseStart_6906429 baseEnd_6906429 := by
    simpa [prefixWord, tailWord_6906429, baseEnd_6906429] using wordTrace_append hprefix tailTrace_6906429
  have hstable : (prefixWord ++ tailWord_6906429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906429).length < 2 ^ (prefixWord ++ tailWord_6906429).sum := by decide
  have hdescent : baseEnd_6906429 < baseStart_6906429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906456 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_6906456 : Nat := 118140960795 + 6906456 * 2 ^ 59
def prefixEnd_6906456 : Nat := 4983230072969 + 3 ^ 40 * 6906456 * 2
def baseEnd_6906456 : Nat := 3546331547128535692837793

theorem tailTrace_6906456 : CollatzResearch.WordTrace tailWord_6906456 prefixEnd_6906456 3546331547128535692837793 := by
  unfold tailWord_6906456
  simp only [CollatzResearch.WordTrace]
  refine ⟨125949572333548457811413611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167932763111397943748551481 125949572333548457811413611)
  ·
    refine ⟨188924358500322686717120417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125949572333548457811413611 188924358500322686717120417)
    ·
      refine ⟨141693268875242015037840313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188924358500322686717120417 141693268875242015037840313)
      ·
        refine ⟨106269951656431511278380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141693268875242015037840313 106269951656431511278380235)
        ·
          refine ⟨159404927484647266917570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106269951656431511278380235 159404927484647266917570353)
          ·
            refine ⟨119553695613485450188177765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159404927484647266917570353 119553695613485450188177765)
            ·
              refine ⟨22416317927528521910283331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119553695613485450188177765 22416317927528521910283331)
              ·
                refine ⟨33624476891292782865424997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22416317927528521910283331 33624476891292782865424997)
                ·
                  refine ⟨6304589417117396787267187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33624476891292782865424997 6304589417117396787267187)
                  ·
                    refine ⟨9456884125676095180900781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6304589417117396787267187 9456884125676095180900781)
                    ·
                      refine ⟨3546331547128535692837793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9456884125676095180900781 3546331547128535692837793)
                      ·
                        rfl

theorem cell23_6906456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_6906456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906456 prefixEnd_6906456 := by exact prefixLift 6906456
  have htrace : WordTrace (prefixWord ++ tailWord_6906456) baseStart_6906456 baseEnd_6906456 := by
    simpa [prefixWord, tailWord_6906456, baseEnd_6906456] using wordTrace_append hprefix tailTrace_6906456
  have hstable : (prefixWord ++ tailWord_6906456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906456).length < 2 ^ (prefixWord ++ tailWord_6906456).sum := by decide
  have hdescent : baseEnd_6906456 < baseStart_6906456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906496 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2]
def baseStart_6906496 : Nat := 118140960795 + 6906496 * 2 ^ 59
def prefixEnd_6906496 : Nat := 4983230072969 + 3 ^ 40 * 6906496 * 2
def baseEnd_6906496 : Nat := 3546352086354715536337609

theorem tailTrace_6906496 : CollatzResearch.WordTrace tailWord_6906496 prefixEnd_6906496 3546352086354715536337609 := by
  unfold tailWord_6906496
  simp only [CollatzResearch.WordTrace]
  refine ⟨125950301793476001227141671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167933735724634668302855561 125950301793476001227141671)
  ·
    refine ⟨188925452690214001840712507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125950301793476001227141671 188925452690214001840712507)
    ·
      refine ⟨283388179035321002761068761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188925452690214001840712507 283388179035321002761068761)
      ·
        refine ⟨212541134276490752070801571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283388179035321002761068761 212541134276490752070801571)
        ·
          refine ⟨318811701414736128106202357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212541134276490752070801571 318811701414736128106202357)
          ·
            refine ⟨29888597007631512009956471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318811701414736128106202357 29888597007631512009956471)
            ·
              refine ⟨44832895511447268014934707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29888597007631512009956471 44832895511447268014934707)
              ·
                refine ⟨67249343267170902022402061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44832895511447268014934707 67249343267170902022402061)
                ·
                  refine ⟨25218503725189088258400773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67249343267170902022402061 25218503725189088258400773)
                  ·
                    refine ⟨4728469448472954048450145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25218503725189088258400773 4728469448472954048450145)
                    ·
                      refine ⟨3546352086354715536337609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728469448472954048450145 3546352086354715536337609)
                      ·
                        rfl

theorem cell23_6906496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_6906496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906496 prefixEnd_6906496 := by exact prefixLift 6906496
  have htrace : WordTrace (prefixWord ++ tailWord_6906496) baseStart_6906496 baseEnd_6906496 := by
    simpa [prefixWord, tailWord_6906496, baseEnd_6906496] using wordTrace_append hprefix tailTrace_6906496
  have hstable : (prefixWord ++ tailWord_6906496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906496).length < 2 ^ (prefixWord ++ tailWord_6906496).sum := by decide
  have hdescent : baseEnd_6906496 < baseStart_6906496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906499 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_6906499 : Nat := 118140960795 + 6906499 * 2 ^ 59
def prefixEnd_6906499 : Nat := 4983230072969 + 3 ^ 40 * 6906499 * 2
def baseEnd_6906499 : Nat := 3546353626796679024600095

theorem tailTrace_6906499 : CollatzResearch.WordTrace tailWord_6906499 prefixEnd_6906499 3546353626796679024600095 := by
  unfold tailWord_6906499
  simp only [CollatzResearch.WordTrace]
  refine ⟨251900713005941133966642551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167933808670627422644428367 251900713005941133966642551)
  ·
    refine ⟨377851069508911700949963827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251900713005941133966642551 377851069508911700949963827)
    ·
      refine ⟨566776604263367551424945741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377851069508911700949963827 566776604263367551424945741)
      ·
        refine ⟨212541226598762831784354653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566776604263367551424945741 212541226598762831784354653)
        ·
          refine ⟨79702959974536061919132995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212541226598762831784354653 79702959974536061919132995)
          ·
            refine ⟨119554439961804092878699493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79702959974536061919132995 119554439961804092878699493)
            ·
              refine ⟨22416457492838267414756155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119554439961804092878699493 22416457492838267414756155)
              ·
                refine ⟨33624686239257401122134233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22416457492838267414756155 33624686239257401122134233)
                ·
                  refine ⟨25218514679443050841600675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33624686239257401122134233 25218514679443050841600675)
                  ·
                    refine ⟨37827772019164576262401013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25218514679443050841600675 37827772019164576262401013)
                    ·
                      refine ⟨3546353626796679024600095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37827772019164576262401013 3546353626796679024600095)
                      ·
                        rfl

theorem cell23_6906499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_6906499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906499 prefixEnd_6906499 := by exact prefixLift 6906499
  have htrace : WordTrace (prefixWord ++ tailWord_6906499) baseStart_6906499 baseEnd_6906499 := by
    simpa [prefixWord, tailWord_6906499, baseEnd_6906499] using wordTrace_append hprefix tailTrace_6906499
  have hstable : (prefixWord ++ tailWord_6906499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906499).length < 2 ^ (prefixWord ++ tailWord_6906499).sum := by decide
  have hdescent : baseEnd_6906499 < baseStart_6906499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906519 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 7]
def baseStart_6906519 : Nat := 118140960795 + 6906519 * 2 ^ 59
def prefixEnd_6906519 : Nat := 4983230072969 + 3 ^ 40 * 6906519 * 2
def baseEnd_6906519 : Nat := 394040432934418771816667

theorem tailTrace_6906519 : CollatzResearch.WordTrace tailWord_6906519 prefixEnd_6906519 394040432934418771816667 := by
  unfold tailWord_6906519
  simp only [CollatzResearch.WordTrace]
  refine ⟨251901442465868677382370611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167934294977245784921580407 251901442465868677382370611)
  ·
    refine ⟨377852163698803016073555917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251901442465868677382370611 377852163698803016073555917)
    ·
      refine ⟨141694561387051131027583469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377852163698803016073555917 141694561387051131027583469)
      ·
        refine ⟨53135460520144174135343801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141694561387051131027583469 53135460520144174135343801)
        ·
          refine ⟨39851595390108130601507851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53135460520144174135343801 39851595390108130601507851)
          ·
            refine ⟨59777393085162195902261777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39851595390108130601507851 59777393085162195902261777)
            ·
              refine ⟨44833044813871646926696333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59777393085162195902261777 44833044813871646926696333)
              ·
                refine ⟨16812391805201867597511125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44833044813871646926696333 16812391805201867597511125)
                ·
                  refine ⟨394040432934418771816667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16812391805201867597511125 394040432934418771816667)
                  ·
                    rfl

theorem cell23_6906519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 7].length) (baseStart_6906519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906519 prefixEnd_6906519 := by exact prefixLift 6906519
  have htrace : WordTrace (prefixWord ++ tailWord_6906519) baseStart_6906519 baseEnd_6906519 := by
    simpa [prefixWord, tailWord_6906519, baseEnd_6906519] using wordTrace_append hprefix tailTrace_6906519
  have hstable : (prefixWord ++ tailWord_6906519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906519).length < 2 ^ (prefixWord ++ tailWord_6906519).sum := by decide
  have hdescent : baseEnd_6906519 < baseStart_6906519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906609 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 10]
def baseStart_6906609 : Nat := 118140960795 + 6906609 * 2 ^ 59
def prefixEnd_6906609 : Nat := 4983230072969 + 3 ^ 40 * 6906609 * 2
def baseEnd_6906609 : Nat := 394045567740963732691621

theorem tailTrace_6906609 : CollatzResearch.WordTrace tailWord_6906609 prefixEnd_6906609 394045567740963732691621 := by
  unfold tailWord_6906609
  simp only [CollatzResearch.WordTrace]
  refine ⟨251904725035542622753146881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167936483357028415168764587 251904725035542622753146881)
  ·
    refine ⟨188928543776656967064860161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251904725035542622753146881 188928543776656967064860161)
    ·
      refine ⟨141696407832492725298645121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188928543776656967064860161 141696407832492725298645121)
      ·
        refine ⟨106272305874369543973983841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141696407832492725298645121 106272305874369543973983841)
        ·
          refine ⟨79704229405777157980487881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106272305874369543973983841 79704229405777157980487881)
          ·
            refine ⟨59778172054332868485365911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79704229405777157980487881 59778172054332868485365911)
            ·
              refine ⟨89667258081499302728048867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59778172054332868485365911 89667258081499302728048867)
              ·
                refine ⟨134500887122248954092073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89667258081499302728048867 134500887122248954092073301)
                ·
                  refine ⟨394045567740963732691621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134500887122248954092073301 394045567740963732691621)
                  ·
                    rfl

theorem cell23_6906609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_6906609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906609 prefixEnd_6906609 := by exact prefixLift 6906609
  have htrace : WordTrace (prefixWord ++ tailWord_6906609) baseStart_6906609 baseEnd_6906609 := by
    simpa [prefixWord, tailWord_6906609, baseEnd_6906609] using wordTrace_append hprefix tailTrace_6906609
  have hstable : (prefixWord ++ tailWord_6906609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906609).length < 2 ^ (prefixWord ++ tailWord_6906609).sum := by decide
  have hdescent : baseEnd_6906609 < baseStart_6906609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_6906629 : Nat := 118140960795 + 6906629 * 2 ^ 59
def prefixEnd_6906629 : Nat := 4983230072969 + 3 ^ 40 * 6906629 * 2
def baseEnd_6906629 : Nat := 3546420379281763515974497

theorem tailTrace_6906629 : CollatzResearch.WordTrace tailWord_6906629 prefixEnd_6906629 3546420379281763515974497 := by
  unfold tailWord_6906629
  simp only [CollatzResearch.WordTrace]
  refine ⟨251905454495470166168874941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167936969663646777445916627 251905454495470166168874941)
  ·
    refine ⟨94464545435801312313328103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251905454495470166168874941 94464545435801312313328103)
    ·
      refine ⟨141696818153701968469992155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94464545435801312313328103 141696818153701968469992155)
      ·
        refine ⟨212545227230552952704988233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141696818153701968469992155 212545227230552952704988233)
        ·
          refine ⟨159408920422914714528741175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212545227230552952704988233 159408920422914714528741175)
          ·
            refine ⟨239113380634372071793111763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159408920422914714528741175 239113380634372071793111763)
            ·
              refine ⟨358670070951558107689667645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239113380634372071793111763 358670070951558107689667645)
              ·
                refine ⟨134501276606834290383625367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358670070951558107689667645 134501276606834290383625367)
                ·
                  refine ⟨201751914910251435575438051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134501276606834290383625367 201751914910251435575438051)
                  ·
                    refine ⟨302627872365377153363157077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 201751914910251435575438051 302627872365377153363157077)
                    ·
                      refine ⟨3546420379281763515974497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 302627872365377153363157077 3546420379281763515974497)
                      ·
                        rfl

theorem cell23_6906629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_6906629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906629 prefixEnd_6906629 := by exact prefixLift 6906629
  have htrace : WordTrace (prefixWord ++ tailWord_6906629) baseStart_6906629 baseEnd_6906629 := by
    simpa [prefixWord, tailWord_6906629, baseEnd_6906629] using wordTrace_append hprefix tailTrace_6906629
  have hstable : (prefixWord ++ tailWord_6906629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906629).length < 2 ^ (prefixWord ++ tailWord_6906629).sum := by decide
  have hdescent : baseEnd_6906629 < baseStart_6906629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906649 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6906649 : Nat := 118140960795 + 6906649 * 2 ^ 59
def prefixEnd_6906649 : Nat := 4983230072969 + 3 ^ 40 * 6906649 * 2
def baseEnd_6906649 : Nat := 3546430648894853437724405

theorem tailTrace_6906649 : CollatzResearch.WordTrace tailWord_6906649 prefixEnd_6906649 3546430648894853437724405 := by
  unfold tailWord_6906649
  simp only [CollatzResearch.WordTrace]
  refine ⟨251906183955397709584603001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167937455970265139723068667 251906183955397709584603001)
  ·
    refine ⟨188929637966548282188452251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251906183955397709584603001 188929637966548282188452251)
    ·
      refine ⟨283394456949822423282678377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188929637966548282188452251 283394456949822423282678377)
      ·
        refine ⟨212545842712366817462008783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283394456949822423282678377 212545842712366817462008783)
        ·
          refine ⟨318818764068550226193013175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212545842712366817462008783 318818764068550226193013175)
          ·
            refine ⟨478228146102825339289519763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318818764068550226193013175 478228146102825339289519763)
            ·
              refine ⟨717342219154238008934279645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478228146102825339289519763 717342219154238008934279645)
              ·
                refine ⟨269003332182839253350354867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717342219154238008934279645 269003332182839253350354867)
                ·
                  refine ⟨403504998274258880025532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269003332182839253350354867 403504998274258880025532301)
                  ·
                    refine ⟨151314374352847080009574613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403504998274258880025532301 151314374352847080009574613)
                    ·
                      refine ⟨3546430648894853437724405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151314374352847080009574613 3546430648894853437724405)
                      ·
                        rfl

theorem cell23_6906649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6906649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906649 prefixEnd_6906649 := by exact prefixLift 6906649
  have htrace : WordTrace (prefixWord ++ tailWord_6906649) baseStart_6906649 baseEnd_6906649 := by
    simpa [prefixWord, tailWord_6906649, baseEnd_6906649] using wordTrace_append hprefix tailTrace_6906649
  have hstable : (prefixWord ++ tailWord_6906649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906649).length < 2 ^ (prefixWord ++ tailWord_6906649).sum := by decide
  have hdescent : baseEnd_6906649 < baseStart_6906649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906687 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 1, 1, 3]
def baseStart_6906687 : Nat := 118140960795 + 6906687 * 2 ^ 59
def prefixEnd_6906687 : Nat := 4983230072969 + 3 ^ 40 * 6906687 * 2
def baseEnd_6906687 : Nat := 3546450161159724289049231

theorem tailTrace_6906687 : CollatzResearch.WordTrace tailWord_6906687 prefixEnd_6906687 3546450161159724289049231 := by
  unfold tailWord_6906687
  simp only [CollatzResearch.WordTrace]
  refine ⟨251907569929260042074486315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167938379952840028049657543 251907569929260042074486315)
  ·
    refine ⟨377861354893890063111729473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251907569929260042074486315 377861354893890063111729473)
    ·
      refine ⟨283396016170417547333797105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377861354893890063111729473 283396016170417547333797105)
      ·
        refine ⟨212547012127813160500347829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283396016170417547333797105 212547012127813160500347829)
        ·
          refine ⟨19926282386982483796907609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212547012127813160500347829 19926282386982483796907609)
          ·
            refine ⟨14944711790236862847680707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19926282386982483796907609 14944711790236862847680707)
            ·
              refine ⟨22417067685355294271521061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14944711790236862847680707 22417067685355294271521061)
              ·
                refine ⟨4203200191004117675910199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22417067685355294271521061 4203200191004117675910199)
                ·
                  refine ⟨6304800286506176513865299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203200191004117675910199 6304800286506176513865299)
                  ·
                    refine ⟨9457200429759264770797949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6304800286506176513865299 9457200429759264770797949)
                    ·
                      refine ⟨3546450161159724289049231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9457200429759264770797949 3546450161159724289049231)
                      ·
                        rfl

theorem cell23_6906687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_6906687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906687 prefixEnd_6906687 := by exact prefixLift 6906687
  have htrace : WordTrace (prefixWord ++ tailWord_6906687) baseStart_6906687 baseEnd_6906687 := by
    simpa [prefixWord, tailWord_6906687, baseEnd_6906687] using wordTrace_append hprefix tailTrace_6906687
  have hstable : (prefixWord ++ tailWord_6906687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906687).length < 2 ^ (prefixWord ++ tailWord_6906687).sum := by decide
  have hdescent : baseEnd_6906687 < baseStart_6906687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906696 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6906696 : Nat := 118140960795 + 6906696 * 2 ^ 59
def prefixEnd_6906696 : Nat := 4983230072969 + 3 ^ 40 * 6906696 * 2
def baseEnd_6906696 : Nat := 3546454782485614753836689

theorem tailTrace_6906696 : CollatzResearch.WordTrace tailWord_6906696 prefixEnd_6906696 3546454782485614753836689 := by
  unfold tailWord_6906696
  simp only [CollatzResearch.WordTrace]
  refine ⟨125953949093113718305781971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167938598790818291074375961 125953949093113718305781971)
  ·
    refine ⟨188930923639670577458672957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125953949093113718305781971 188930923639670577458672957)
    ·
      refine ⟨70849096364876466547002359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188930923639670577458672957 70849096364876466547002359)
      ·
        refine ⟨106273644547314699820503539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70849096364876466547002359 106273644547314699820503539)
        ·
          refine ⟨159410466820972049730755309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106273644547314699820503539 159410466820972049730755309)
          ·
            refine ⟨59778925057864518649033241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159410466820972049730755309 59778925057864518649033241)
            ·
              refine ⟨44834193793398388986774931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59778925057864518649033241 44834193793398388986774931)
              ·
                refine ⟨67251290690097583480162397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44834193793398388986774931 67251290690097583480162397)
                ·
                  refine ⟨25219234008786593805060899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67251290690097583480162397 25219234008786593805060899)
                  ·
                    refine ⟨37828851013179890707591349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25219234008786593805060899 37828851013179890707591349)
                    ·
                      refine ⟨3546454782485614753836689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37828851013179890707591349 3546454782485614753836689)
                      ·
                        rfl

theorem cell23_6906696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6906696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906696 prefixEnd_6906696 := by exact prefixLift 6906696
  have htrace : WordTrace (prefixWord ++ tailWord_6906696) baseStart_6906696 baseEnd_6906696 := by
    simpa [prefixWord, tailWord_6906696, baseEnd_6906696] using wordTrace_append hprefix tailTrace_6906696
  have hstable : (prefixWord ++ tailWord_6906696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906696).length < 2 ^ (prefixWord ++ tailWord_6906696).sum := by decide
  have hdescent : baseEnd_6906696 < baseStart_6906696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906713 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_6906713 : Nat := 118140960795 + 6906713 * 2 ^ 59
def prefixEnd_6906713 : Nat := 4983230072969 + 3 ^ 40 * 6906713 * 2
def baseEnd_6906713 : Nat := 3546463511656741187324111

theorem tailTrace_6906713 : CollatzResearch.WordTrace tailWord_6906713 prefixEnd_6906713 3546463511656741187324111 := by
  unfold tailWord_6906713
  simp only [CollatzResearch.WordTrace]
  refine ⟨251908518227165848514932793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167939012151443899009955195 251908518227165848514932793)
  ·
    refine ⟨188931388670374386386199595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251908518227165848514932793 188931388670374386386199595)
    ·
      refine ⟨283397083005561579579299393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188931388670374386386199595 283397083005561579579299393)
      ·
        refine ⟨212547812254171184684474545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283397083005561579579299393 212547812254171184684474545)
        ·
          refine ⟨159410859190628388513355909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212547812254171184684474545 159410859190628388513355909)
          ·
            refine ⟨29889536098242822846254233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159410859190628388513355909 29889536098242822846254233)
            ·
              refine ⟨22417152073682117134690675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29889536098242822846254233 22417152073682117134690675)
              ·
                refine ⟨33625728110523175702036013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22417152073682117134690675 33625728110523175702036013)
                ·
                  refine ⟨12609648041446190888263505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33625728110523175702036013 12609648041446190888263505)
                  ·
                    refine ⟨9457236031084643166197629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12609648041446190888263505 9457236031084643166197629)
                    ·
                      refine ⟨3546463511656741187324111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9457236031084643166197629 3546463511656741187324111)
                      ·
                        rfl

theorem cell23_6906713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_6906713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906713 prefixEnd_6906713 := by exact prefixLift 6906713
  have htrace : WordTrace (prefixWord ++ tailWord_6906713) baseStart_6906713 baseEnd_6906713 := by
    simpa [prefixWord, tailWord_6906713, baseEnd_6906713] using wordTrace_append hprefix tailTrace_6906713
  have hstable : (prefixWord ++ tailWord_6906713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906713).length < 2 ^ (prefixWord ++ tailWord_6906713).sum := by decide
  have hdescent : baseEnd_6906713 < baseStart_6906713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906723 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6906723 : Nat := 118140960795 + 6906723 * 2 ^ 59
def prefixEnd_6906723 : Nat := 4983230072969 + 3 ^ 40 * 6906723 * 2
def baseEnd_6906723 : Nat := 3546468646463286148199065

theorem tailTrace_6906723 : CollatzResearch.WordTrace tailWord_6906723 prefixEnd_6906723 3546468646463286148199065 := by
  unfold tailWord_6906723
  simp only [CollatzResearch.WordTrace]
  refine ⟨251908882957129620222796823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167939255304753080148531215 251908882957129620222796823)
  ·
    refine ⟨377863324435694430334195235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251908882957129620222796823 377863324435694430334195235)
    ·
      refine ⟨566794986653541645501292853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377863324435694430334195235 566794986653541645501292853)
      ·
        refine ⟨53137029998769529265746205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 566794986653541645501292853 53137029998769529265746205)
        ·
          refine ⟨19926386249538573474654827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53137029998769529265746205 19926386249538573474654827)
          ·
            refine ⟨29889579374307860211982241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19926386249538573474654827 29889579374307860211982241)
            ·
              refine ⟨22417184530730895158986681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29889579374307860211982241 22417184530730895158986681)
              ·
                refine ⟨16812888398048171369240011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22417184530730895158986681 16812888398048171369240011)
                ·
                  refine ⟨25219332597072257053860017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16812888398048171369240011 25219332597072257053860017)
                  ·
                    refine ⟨18914499447804192790395013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25219332597072257053860017 18914499447804192790395013)
                    ·
                      refine ⟨3546468646463286148199065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18914499447804192790395013 3546468646463286148199065)
                      ·
                        rfl

theorem cell23_6906723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6906723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906723 prefixEnd_6906723 := by exact prefixLift 6906723
  have htrace : WordTrace (prefixWord ++ tailWord_6906723) baseStart_6906723 baseEnd_6906723 := by
    simpa [prefixWord, tailWord_6906723, baseEnd_6906723] using wordTrace_append hprefix tailTrace_6906723
  have hstable : (prefixWord ++ tailWord_6906723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906723).length < 2 ^ (prefixWord ++ tailWord_6906723).sum := by decide
  have hdescent : baseEnd_6906723 < baseStart_6906723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906727 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_6906727 : Nat := 118140960795 + 6906727 * 2 ^ 59
def prefixEnd_6906727 : Nat := 4983230072969 + 3 ^ 40 * 6906727 * 2
def baseEnd_6906727 : Nat := 3546470700385904132549047

theorem tailTrace_6906727 : CollatzResearch.WordTrace tailWord_6906727 prefixEnd_6906727 3546470700385904132549047 := by
  unfold tailWord_6906727
  simp only [CollatzResearch.WordTrace]
  refine ⟨251909028849115128905942435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167939352566076752603961623 251909028849115128905942435)
  ·
    refine ⟨377863543273672693358913653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251909028849115128905942435 377863543273672693358913653)
    ·
      refine ⟨35424707181906815002398155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 377863543273672693358913653 35424707181906815002398155)
      ·
        refine ⟨53137060772860222503597233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35424707181906815002398155 53137060772860222503597233)
        ·
          refine ⟨39852795579645166877697925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53137060772860222503597233 39852795579645166877697925)
          ·
            refine ⟨7472399171183468789568361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39852795579645166877697925 7472399171183468789568361)
            ·
              refine ⟨5604299378387601592176271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472399171183468789568361 5604299378387601592176271)
              ·
                refine ⟨8406449067581402388264407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604299378387601592176271 8406449067581402388264407)
                ·
                  refine ⟨12609673601372103582396611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406449067581402388264407 12609673601372103582396611)
                  ·
                    refine ⟨18914510402058155373594917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12609673601372103582396611 18914510402058155373594917)
                    ·
                      refine ⟨3546470700385904132549047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18914510402058155373594917 3546470700385904132549047)
                      ·
                        rfl

theorem cell23_6906727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_6906727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906727 prefixEnd_6906727 := by exact prefixLift 6906727
  have htrace : WordTrace (prefixWord ++ tailWord_6906727) baseStart_6906727 baseEnd_6906727 := by
    simpa [prefixWord, tailWord_6906727, baseEnd_6906727] using wordTrace_append hprefix tailTrace_6906727
  have hstable : (prefixWord ++ tailWord_6906727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906727).length < 2 ^ (prefixWord ++ tailWord_6906727).sum := by decide
  have hdescent : baseEnd_6906727 < baseStart_6906727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906754 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6906754 : Nat := 118140960795 + 6906754 * 2 ^ 59
def prefixEnd_6906754 : Nat := 4983230072969 + 3 ^ 40 * 6906754 * 2
def baseEnd_6906754 : Nat := 1182161521454525175637141

theorem tailTrace_6906754 : CollatzResearch.WordTrace tailWord_6906754 prefixEnd_6906754 1182161521454525175637141 := by
  unfold tailWord_6906754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977503405004328129293829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167940009080011541678116877 62977503405004328129293829)
  ·
    refine ⟨11808281888438311524242593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62977503405004328129293829 11808281888438311524242593)
    ·
      refine ⟨8856211416328733643181945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11808281888438311524242593 8856211416328733643181945)
      ·
        refine ⟨6642158562246550232386459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8856211416328733643181945 6642158562246550232386459)
        ·
          refine ⟨9963237843369825348579689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642158562246550232386459 9963237843369825348579689)
          ·
            refine ⟨7472428382527369011434767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9963237843369825348579689 7472428382527369011434767)
            ·
              refine ⟨11208642573791053517152151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472428382527369011434767 11208642573791053517152151)
              ·
                refine ⟨16812963860686580275728227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208642573791053517152151 16812963860686580275728227)
                ·
                  refine ⟨25219445791029870413592341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16812963860686580275728227 25219445791029870413592341)
                  ·
                    refine ⟨1182161521454525175637141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25219445791029870413592341 1182161521454525175637141)
                    ·
                      rfl

theorem cell23_6906754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6906754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906754 prefixEnd_6906754 := by exact prefixLift 6906754
  have htrace : WordTrace (prefixWord ++ tailWord_6906754) baseStart_6906754 baseEnd_6906754 := by
    simpa [prefixWord, tailWord_6906754, baseEnd_6906754] using wordTrace_append hprefix tailTrace_6906754
  have hstable : (prefixWord ++ tailWord_6906754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906754).length < 2 ^ (prefixWord ++ tailWord_6906754).sum := by decide
  have hdescent : baseEnd_6906754 < baseStart_6906754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906760 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6906760 : Nat := 118140960795 + 6906760 * 2 ^ 59
def prefixEnd_6906760 : Nat := 4983230072969 + 3 ^ 40 * 6906760 * 2
def baseEnd_6906760 : Nat := 3546487645247502503436395

theorem tailTrace_6906760 : CollatzResearch.WordTrace tailWord_6906760 prefixEnd_6906760 3546487645247502503436395 := by
  unfold tailWord_6906760
  simp only [CollatzResearch.WordTrace]
  refine ⟨125955116228997787770946867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167940154971997050361262489 125955116228997787770946867)
  ·
    refine ⟨188932674343496681656420301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125955116228997787770946867 188932674343496681656420301)
    ·
      refine ⟨70849752878811255621157613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188932674343496681656420301 70849752878811255621157613)
      ·
        refine ⟨26568657329554220857934105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70849752878811255621157613 26568657329554220857934105)
        ·
          refine ⟨19926492997165665643450579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26568657329554220857934105 19926492997165665643450579)
          ·
            refine ⟨29889739495748498465175869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19926492997165665643450579 29889739495748498465175869)
            ·
              refine ⟨11208652310905686924440951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29889739495748498465175869 11208652310905686924440951)
              ·
                refine ⟨16812978466358530386661427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208652310905686924440951 16812978466358530386661427)
                ·
                  refine ⟨25219467699537795579992141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16812978466358530386661427 25219467699537795579992141)
                  ·
                    refine ⟨9457300387326673342497053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25219467699537795579992141 9457300387326673342497053)
                    ·
                      refine ⟨3546487645247502503436395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9457300387326673342497053 3546487645247502503436395)
                      ·
                        rfl

theorem cell23_6906760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6906760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906760 prefixEnd_6906760 := by exact prefixLift 6906760
  have htrace : WordTrace (prefixWord ++ tailWord_6906760) baseStart_6906760 baseEnd_6906760 := by
    simpa [prefixWord, tailWord_6906760, baseEnd_6906760] using wordTrace_append hprefix tailTrace_6906760
  have hstable : (prefixWord ++ tailWord_6906760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906760).length < 2 ^ (prefixWord ++ tailWord_6906760).sum := by decide
  have hdescent : baseEnd_6906760 < baseStart_6906760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906778 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6906778 : Nat := 118140960795 + 6906778 * 2 ^ 59
def prefixEnd_6906778 : Nat := 4983230072969 + 3 ^ 40 * 6906778 * 2
def baseEnd_6906778 : Nat := 3546496887899283433011313

theorem tailTrace_6906778 : CollatzResearch.WordTrace tailWord_6906778 prefixEnd_6906778 3546496887899283433011313 := by
  unfold tailWord_6906778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977722242982591154012247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167940592647953576410699325 62977722242982591154012247)
  ·
    refine ⟨94466583364473886731018371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62977722242982591154012247 94466583364473886731018371)
    ·
      refine ⟨141699875046710830096527557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94466583364473886731018371 141699875046710830096527557)
      ·
        refine ⟨26568726571258280643098917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141699875046710830096527557 26568726571258280643098917)
        ·
          refine ⟨4981636232110927620581047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26568726571258280643098917 4981636232110927620581047)
          ·
            refine ⟨7472454348166391430871571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981636232110927620581047 7472454348166391430871571)
            ·
              refine ⟨11208681522249587146307357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472454348166391430871571 11208681522249587146307357)
              ·
                refine ⟨4203255570843595179865259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11208681522249587146307357 4203255570843595179865259)
                ·
                  refine ⟨6304883356265392769797889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203255570843595179865259 6304883356265392769797889)
                  ·
                    refine ⟨4728662517199044577348417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304883356265392769797889 4728662517199044577348417)
                    ·
                      refine ⟨3546496887899283433011313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728662517199044577348417 3546496887899283433011313)
                      ·
                        rfl

theorem cell23_6906778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6906778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906778 prefixEnd_6906778 := by exact prefixLift 6906778
  have htrace : WordTrace (prefixWord ++ tailWord_6906778) baseStart_6906778 baseEnd_6906778 := by
    simpa [prefixWord, tailWord_6906778, baseEnd_6906778] using wordTrace_append hprefix tailTrace_6906778
  have hstable : (prefixWord ++ tailWord_6906778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906778).length < 2 ^ (prefixWord ++ tailWord_6906778).sum := by decide
  have hdescent : baseEnd_6906778 < baseStart_6906778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906863 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_6906863 : Nat := 118140960795 + 6906863 * 2 ^ 59
def prefixEnd_6906863 : Nat := 4983230072969 + 3 ^ 40 * 6906863 * 2
def baseEnd_6906863 : Nat := 3546540533754915600448421

theorem tailTrace_6906863 : CollatzResearch.WordTrace tailWord_6906863 prefixEnd_6906863 3546540533754915600448421 := by
  unfold tailWord_6906863
  simp only [CollatzResearch.WordTrace]
  refine ⟨251913989176622424132893243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167942659451081616088595495 251913989176622424132893243)
  ·
    refine ⟨377870983764933636199339865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251913989176622424132893243 377870983764933636199339865)
    ·
      refine ⟨283403237823700227149504899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377870983764933636199339865 283403237823700227149504899)
      ·
        refine ⟨425104856735550340724257349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283403237823700227149504899 425104856735550340724257349)
        ·
          refine ⟨79707160637915688885798253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425104856735550340724257349 79707160637915688885798253)
          ·
            refine ⟨29890185239218383332174345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79707160637915688885798253 29890185239218383332174345)
            ·
              refine ⟨22417638929413787499130759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29890185239218383332174345 22417638929413787499130759)
              ·
                refine ⟨33626458394120681248696139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22417638929413787499130759 33626458394120681248696139)
                ·
                  refine ⟨50439687591181021873044209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33626458394120681248696139 50439687591181021873044209)
                  ·
                    refine ⟨37829765693385766404783157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50439687591181021873044209 37829765693385766404783157)
                    ·
                      refine ⟨3546540533754915600448421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37829765693385766404783157 3546540533754915600448421)
                      ·
                        rfl

theorem cell23_6906863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_6906863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906863 prefixEnd_6906863 := by exact prefixLift 6906863
  have htrace : WordTrace (prefixWord ++ tailWord_6906863) baseStart_6906863 baseEnd_6906863 := by
    simpa [prefixWord, tailWord_6906863, baseEnd_6906863] using wordTrace_append hprefix tailTrace_6906863
  have hstable : (prefixWord ++ tailWord_6906863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906863).length < 2 ^ (prefixWord ++ tailWord_6906863).sum := by decide
  have hdescent : baseEnd_6906863 < baseStart_6906863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906873 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6906873 : Nat := 118140960795 + 6906873 * 2 ^ 59
def prefixEnd_6906873 : Nat := 4983230072969 + 3 ^ 40 * 6906873 * 2
def baseEnd_6906873 : Nat := 3546545668561460561323375

theorem tailTrace_6906873 : CollatzResearch.WordTrace tailWord_6906873 prefixEnd_6906873 3546545668561460561323375 := by
  unfold tailWord_6906873
  simp only [CollatzResearch.WordTrace]
  refine ⟨251914353906586195840757273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167942902604390797227171515 251914353906586195840757273)
  ·
    refine ⟨188935765429939646880567955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251914353906586195840757273 188935765429939646880567955)
    ·
      refine ⟨283403648144909470320851933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188935765429939646880567955 283403648144909470320851933)
      ·
        refine ⟨106276368054341051370319475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283403648144909470320851933 106276368054341051370319475)
        ·
          refine ⟨159414552081511577055479213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106276368054341051370319475 159414552081511577055479213)
          ·
            refine ⟨59780457030566841395804705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159414552081511577055479213 59780457030566841395804705)
            ·
              refine ⟨44835342772925131046853529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59780457030566841395804705 44835342772925131046853529)
              ·
                refine ⟨33626507079693848285140147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44835342772925131046853529 33626507079693848285140147)
                ·
                  refine ⟨50439760619540772427710221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33626507079693848285140147 50439760619540772427710221)
                  ·
                    refine ⟨18914910232327789660391333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50439760619540772427710221 18914910232327789660391333)
                    ·
                      refine ⟨3546545668561460561323375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18914910232327789660391333 3546545668561460561323375)
                      ·
                        rfl

theorem cell23_6906873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6906873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906873 prefixEnd_6906873 := by exact prefixLift 6906873
  have htrace : WordTrace (prefixWord ++ tailWord_6906873) baseStart_6906873 baseEnd_6906873 := by
    simpa [prefixWord, tailWord_6906873, baseEnd_6906873] using wordTrace_append hprefix tailTrace_6906873
  have hstable : (prefixWord ++ tailWord_6906873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906873).length < 2 ^ (prefixWord ++ tailWord_6906873).sum := by decide
  have hdescent : baseEnd_6906873 < baseStart_6906873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906890 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_6906890 : Nat := 118140960795 + 6906890 * 2 ^ 59
def prefixEnd_6906890 : Nat := 4983230072969 + 3 ^ 40 * 6906890 * 2
def baseEnd_6906890 : Nat := 3546554397732586994810797

theorem tailTrace_6906890 : CollatzResearch.WordTrace tailWord_6906890 prefixEnd_6906890 3546554397732586994810797 := by
  unfold tailWord_6906890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62978743486881151936031531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167943315965016405162750749 62978743486881151936031531)
  ·
    refine ⟨94468115230321727904047297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62978743486881151936031531 94468115230321727904047297)
    ·
      refine ⟨70851086422741295928035473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94468115230321727904047297 70851086422741295928035473)
      ·
        refine ⟨53138314817055971946026605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70851086422741295928035473 53138314817055971946026605)
        ·
          refine ⟨19926868056395989479759977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53138314817055971946026605 19926868056395989479759977)
          ·
            refine ⟨14945151042296992109819983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19926868056395989479759977 14945151042296992109819983)
            ·
              refine ⟨22417726563445488164729975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14945151042296992109819983 22417726563445488164729975)
              ·
                refine ⟨33626589845168232247094963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22417726563445488164729975 33626589845168232247094963)
                ·
                  refine ⟨50439884767752348370642445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33626589845168232247094963 50439884767752348370642445)
                  ·
                    refine ⟨18914956787907130638990917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50439884767752348370642445 18914956787907130638990917)
                    ·
                      refine ⟨3546554397732586994810797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18914956787907130638990917 3546554397732586994810797)
                      ·
                        rfl

theorem cell23_6906890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_6906890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906890 prefixEnd_6906890 := by exact prefixLift 6906890
  have htrace : WordTrace (prefixWord ++ tailWord_6906890) baseStart_6906890 baseEnd_6906890 := by
    simpa [prefixWord, tailWord_6906890, baseEnd_6906890] using wordTrace_append hprefix tailTrace_6906890
  have hstable : (prefixWord ++ tailWord_6906890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906890).length < 2 ^ (prefixWord ++ tailWord_6906890).sum := by decide
  have hdescent : baseEnd_6906890 < baseStart_6906890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906917 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_6906917 : Nat := 118140960795 + 6906917 * 2 ^ 59
def prefixEnd_6906917 : Nat := 4983230072969 + 3 ^ 40 * 6906917 * 2
def baseEnd_6906917 : Nat := 1182189420570086129724391

theorem tailTrace_6906917 : CollatzResearch.WordTrace tailWord_6906917 prefixEnd_6906917 1182189420570086129724391 := by
  unfold tailWord_6906917
  simp only [CollatzResearch.WordTrace]
  refine ⟨251915958718426791355359005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167943972478951194236906003 251915958718426791355359005)
  ·
    refine ⟨94468484519410046758259627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251915958718426791355359005 94468484519410046758259627)
    ·
      refine ⟨141702726779115070137389441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94468484519410046758259627 141702726779115070137389441)
      ·
        refine ⟨106277045084336302603042081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141702726779115070137389441 106277045084336302603042081)
        ·
          refine ⟨79707783813252226952281561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106277045084336302603042081 79707783813252226952281561)
          ·
            refine ⟨59780837859939170214211171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79707783813252226952281561 59780837859939170214211171)
            ·
              refine ⟨89671256789908755321316757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59780837859939170214211171 89671256789908755321316757)
              ·
                refine ⟨4203340162026972905686723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89671256789908755321316757 4203340162026972905686723)
                ·
                  refine ⟨6305010243040459358530085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203340162026972905686723 6305010243040459358530085)
                  ·
                    refine ⟨1182189420570086129724391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305010243040459358530085 1182189420570086129724391)
                    ·
                      rfl

theorem cell23_6906917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_6906917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906917 prefixEnd_6906917 := by exact prefixLift 6906917
  have htrace : WordTrace (prefixWord ++ tailWord_6906917) baseStart_6906917 baseEnd_6906917 := by
    simpa [prefixWord, tailWord_6906917, baseEnd_6906917] using wordTrace_append hprefix tailTrace_6906917
  have hstable : (prefixWord ++ tailWord_6906917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906917).length < 2 ^ (prefixWord ++ tailWord_6906917).sum := by decide
  have hdescent : baseEnd_6906917 < baseStart_6906917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906933 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6906933 : Nat := 118140960795 + 6906933 * 2 ^ 59
def prefixEnd_6906933 : Nat := 4983230072969 + 3 ^ 40 * 6906933 * 2
def baseEnd_6906933 : Nat := 3546576477400730326573099

theorem tailTrace_6906933 : CollatzResearch.WordTrace tailWord_6906933 prefixEnd_6906933 3546576477400730326573099 := by
  unfold tailWord_6906933
  simp only [CollatzResearch.WordTrace]
  refine ⟨251916542286368826087941453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167944361524245884058627635 251916542286368826087941453)
  ·
    refine ⟨94468703357388309782978045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251916542286368826087941453 94468703357388309782978045)
    ·
      refine ⟨35425763759020616168616767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94468703357388309782978045 35425763759020616168616767)
      ·
        refine ⟨53138645638530924252925151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35425763759020616168616767 53138645638530924252925151)
        ·
          refine ⟨79707968457796386379387727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53138645638530924252925151 79707968457796386379387727)
          ·
            refine ⟨119561952686694579569081591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79707968457796386379387727 119561952686694579569081591)
            ·
              refine ⟨179342929030041869353622387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119561952686694579569081591 179342929030041869353622387)
              ·
                refine ⟨269014393545062804030433581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179342929030041869353622387 269014393545062804030433581)
                ·
                  refine ⟨100880397579398551511412593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269014393545062804030433581 100880397579398551511412593)
                  ·
                    refine ⟨75660298184548913633559445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100880397579398551511412593 75660298184548913633559445)
                    ·
                      refine ⟨3546576477400730326573099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75660298184548913633559445 3546576477400730326573099)
                      ·
                        rfl

theorem cell23_6906933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6906933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906933 prefixEnd_6906933 := by exact prefixLift 6906933
  have htrace : WordTrace (prefixWord ++ tailWord_6906933) baseStart_6906933 baseEnd_6906933 := by
    simpa [prefixWord, tailWord_6906933, baseEnd_6906933] using wordTrace_append hprefix tailTrace_6906933
  have hstable : (prefixWord ++ tailWord_6906933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906933).length < 2 ^ (prefixWord ++ tailWord_6906933).sum := by decide
  have hdescent : baseEnd_6906933 < baseStart_6906933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6906980 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6906980 : Nat := 118140960795 + 6906980 * 2 ^ 59
def prefixEnd_6906980 : Nat := 4983230072969 + 3 ^ 40 * 6906980 * 2
def baseEnd_6906980 : Nat := 3546600610991491642685383

theorem tailTrace_6906980 : CollatzResearch.WordTrace tailWord_6906980 prefixEnd_6906980 3546600610991491642685383 := by
  unfold tailWord_6906980
  simp only [CollatzResearch.WordTrace]
  refine ⟨125959128258599276557451197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167945504344799035409934929 125959128258599276557451197)
  ·
    refine ⟨47234673096974728709044199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125959128258599276557451197 47234673096974728709044199)
    ·
      refine ⟨70852009645462093063566299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47234673096974728709044199 70852009645462093063566299)
      ·
        refine ⟨106278014468193139595349449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70852009645462093063566299 106278014468193139595349449)
        ·
          refine ⟨79708510851144854696512087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106278014468193139595349449 79708510851144854696512087)
          ·
            refine ⟨119562766276717282044768131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79708510851144854696512087 119562766276717282044768131)
            ·
              refine ⟨179344149415075923067152197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119562766276717282044768131 179344149415075923067152197)
              ·
                refine ⟨33627028015326735575091037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179344149415075923067152197 33627028015326735575091037)
                ·
                  refine ⟨12610135505747525840659139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33627028015326735575091037 12610135505747525840659139)
                  ·
                    refine ⟨18915203258621288760988709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12610135505747525840659139 18915203258621288760988709)
                    ·
                      refine ⟨3546600610991491642685383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18915203258621288760988709 3546600610991491642685383)
                      ·
                        rfl

theorem cell23_6906980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6906980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6906980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6906980 prefixEnd_6906980 := by exact prefixLift 6906980
  have htrace : WordTrace (prefixWord ++ tailWord_6906980) baseStart_6906980 baseEnd_6906980 := by
    simpa [prefixWord, tailWord_6906980, baseEnd_6906980] using wordTrace_append hprefix tailTrace_6906980
  have hstable : (prefixWord ++ tailWord_6906980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6906980).length < 2 ^ (prefixWord ++ tailWord_6906980).sum := by decide
  have hdescent : baseEnd_6906980 < baseStart_6906980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6906980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907017 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_6907017 : Nat := 118140960795 + 6907017 * 2 ^ 59
def prefixEnd_6907017 : Nat := 4983230072969 + 3 ^ 40 * 6907017 * 2
def baseEnd_6907017 : Nat := 3546619609775707997922713

theorem tailTrace_6907017 : CollatzResearch.WordTrace tailWord_6907017 prefixEnd_6907017 3546619609775707997922713 := by
  unfold tailWord_6907017
  simp only [CollatzResearch.WordTrace]
  refine ⟨251919606018064508433999305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167946404012043005622666203 251919606018064508433999305)
  ·
    refine ⟨188939704513548381325499479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251919606018064508433999305 188939704513548381325499479)
    ·
      refine ⟨283409556770322571988249219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188939704513548381325499479 283409556770322571988249219)
      ·
        refine ⟨425114335155483857982373829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283409556770322571988249219 425114335155483857982373829)
        ·
          refine ⟨79708937841653223371695093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425114335155483857982373829 79708937841653223371695093)
          ·
            refine ⟨7472712922654989691096415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79708937841653223371695093 7472712922654989691096415)
            ·
              refine ⟨11209069383982484536644623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472712922654989691096415 11209069383982484536644623)
              ·
                refine ⟨16813604075973726804966935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209069383982484536644623 16813604075973726804966935)
                ·
                  refine ⟨25220406113960590207450403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16813604075973726804966935 25220406113960590207450403)
                  ·
                    refine ⟨37830609170940885311175605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25220406113960590207450403 37830609170940885311175605)
                    ·
                      refine ⟨3546619609775707997922713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37830609170940885311175605 3546619609775707997922713)
                      ·
                        rfl

theorem cell23_6907017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_6907017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907017 prefixEnd_6907017 := by exact prefixLift 6907017
  have htrace : WordTrace (prefixWord ++ tailWord_6907017) baseStart_6907017 baseEnd_6907017 := by
    simpa [prefixWord, tailWord_6907017, baseEnd_6907017] using wordTrace_append hprefix tailTrace_6907017
  have hstable : (prefixWord ++ tailWord_6907017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907017).length < 2 ^ (prefixWord ++ tailWord_6907017).sum := by decide
  have hdescent : baseEnd_6907017 < baseStart_6907017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907023 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_6907023 : Nat := 118140960795 + 6907023 * 2 ^ 59
def prefixEnd_6907023 : Nat := 4983230072969 + 3 ^ 40 * 6907023 * 2
def baseEnd_6907023 : Nat := 3546622690659634974447685

theorem tailTrace_6907023 : CollatzResearch.WordTrace tailWord_6907023 prefixEnd_6907023 3546622690659634974447685 := by
  unfold tailWord_6907023
  simp only [CollatzResearch.WordTrace]
  refine ⟨251919824856042771458717723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167946549904028514305811815 251919824856042771458717723)
  ·
    refine ⟨377879737284064157188076585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251919824856042771458717723 377879737284064157188076585)
    ·
      refine ⟨283409802963048117891057439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377879737284064157188076585 283409802963048117891057439)
      ·
        refine ⟨425114704444572176836586159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283409802963048117891057439 425114704444572176836586159)
        ·
          refine ⟨637672056666858265254879239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425114704444572176836586159 637672056666858265254879239)
          ·
            refine ⟨956508085000287397882318859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637672056666858265254879239 956508085000287397882318859)
            ·
              refine ⟨1434762127500431096823478289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956508085000287397882318859 1434762127500431096823478289)
              ·
                refine ⟨1076071595625323322617608717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434762127500431096823478289 1076071595625323322617608717)
                ·
                  refine ⟨403526848359496245981603269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1076071595625323322617608717 403526848359496245981603269)
                  ·
                    refine ⟨75661284067405546121550613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403526848359496245981603269 75661284067405546121550613)
                    ·
                      refine ⟨3546622690659634974447685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75661284067405546121550613 3546622690659634974447685)
                      ·
                        rfl

theorem cell23_6907023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_6907023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907023 prefixEnd_6907023 := by exact prefixLift 6907023
  have htrace : WordTrace (prefixWord ++ tailWord_6907023) baseStart_6907023 baseEnd_6907023 := by
    simpa [prefixWord, tailWord_6907023, baseEnd_6907023] using wordTrace_append hprefix tailTrace_6907023
  have hstable : (prefixWord ++ tailWord_6907023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907023).length < 2 ^ (prefixWord ++ tailWord_6907023).sum := by decide
  have hdescent : baseEnd_6907023 < baseStart_6907023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907080 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_6907080 : Nat := 118140960795 + 6907080 * 2 ^ 59
def prefixEnd_6907080 : Nat := 4983230072969 + 3 ^ 40 * 6907080 * 2
def baseEnd_6907080 : Nat := 1182217319685647083811641

theorem tailTrace_6907080 : CollatzResearch.WordTrace tailWord_6907080 prefixEnd_6907080 1182217319685647083811641 := by
  unfold tailWord_6907080
  simp only [CollatzResearch.WordTrace]
  refine ⟨125960951908418135096771347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167947935877890846795695129 125960951908418135096771347)
  ·
    refine ⟨188941427862627202645157021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125960951908418135096771347 188941427862627202645157021)
    ·
      refine ⟨70853035448485200991933883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188941427862627202645157021 70853035448485200991933883)
      ·
        refine ⟨106279553172727801487900825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70853035448485200991933883 106279553172727801487900825)
        ·
          refine ⟨79709664879545851115925619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106279553172727801487900825 79709664879545851115925619)
          ·
            refine ⟨119564497319318776673888429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79709664879545851115925619 119564497319318776673888429)
            ·
              refine ⟨44836686494744541252708161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119564497319318776673888429 44836686494744541252708161)
              ·
                refine ⟨33627514871058405939531121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44836686494744541252708161 33627514871058405939531121)
                ·
                  refine ⟨25220636153293804454648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33627514871058405939531121 25220636153293804454648341)
                  ·
                    refine ⟨1182217319685647083811641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25220636153293804454648341 1182217319685647083811641)
                    ·
                      rfl

theorem cell23_6907080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_6907080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907080 prefixEnd_6907080 := by exact prefixLift 6907080
  have htrace : WordTrace (prefixWord ++ tailWord_6907080) baseStart_6907080 baseEnd_6907080 := by
    simpa [prefixWord, tailWord_6907080, baseEnd_6907080] using wordTrace_append hprefix tailTrace_6907080
  have hstable : (prefixWord ++ tailWord_6907080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907080).length < 2 ^ (prefixWord ++ tailWord_6907080).sum := by decide
  have hdescent : baseEnd_6907080 < baseStart_6907080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907104 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2]
def baseStart_6907104 : Nat := 118140960795 + 6907104 * 2 ^ 59
def prefixEnd_6907104 : Nat := 4983230072969 + 3 ^ 40 * 6907104 * 2
def baseEnd_6907104 : Nat := 3546664282592649157534813

theorem tailTrace_6907104 : CollatzResearch.WordTrace tailWord_6907104 prefixEnd_6907104 3546664282592649157534813 := by
  unfold tailWord_6907104
  simp only [CollatzResearch.WordTrace]
  refine ⟨125961389584374661146208183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167948519445832881528277577 125961389584374661146208183)
  ·
    refine ⟨188942084376561991719312275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125961389584374661146208183 188942084376561991719312275)
    ·
      refine ⟨283413126564842987578968413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188942084376561991719312275 283413126564842987578968413)
      ·
        refine ⟨106279922461816120342113155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283413126564842987578968413 106279922461816120342113155)
        ·
          refine ⟨159419883692724180513169733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106279922461816120342113155 159419883692724180513169733)
          ·
            refine ⟨29891228192385783846219325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159419883692724180513169733 29891228192385783846219325)
            ·
              refine ⟨11209210572144668942332247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29891228192385783846219325 11209210572144668942332247)
              ·
                refine ⟨16813815858217003413498371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209210572144668942332247 16813815858217003413498371)
                ·
                  refine ⟨25220723787325505120247557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16813815858217003413498371 25220723787325505120247557)
                  ·
                    refine ⟨4728885710123532210046417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25220723787325505120247557 4728885710123532210046417)
                    ·
                      refine ⟨3546664282592649157534813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728885710123532210046417 3546664282592649157534813)
                      ·
                        rfl

theorem cell23_6907104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_6907104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907104 prefixEnd_6907104 := by exact prefixLift 6907104
  have htrace : WordTrace (prefixWord ++ tailWord_6907104) baseStart_6907104 baseEnd_6907104 := by
    simpa [prefixWord, tailWord_6907104, baseEnd_6907104] using wordTrace_append hprefix tailTrace_6907104
  have hstable : (prefixWord ++ tailWord_6907104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907104).length < 2 ^ (prefixWord ++ tailWord_6907104).sum := by decide
  have hdescent : baseEnd_6907104 < baseStart_6907104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907144 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 7]
def baseStart_6907144 : Nat := 118140960795 + 6907144 * 2 ^ 59
def prefixEnd_6907144 : Nat := 4983230072969 + 3 ^ 40 * 6907144 * 2
def baseEnd_6907144 : Nat := 394076091313203222337181

theorem tailTrace_6907144 : CollatzResearch.WordTrace tailWord_6907144 prefixEnd_6907144 394076091313203222337181 := by
  unfold tailWord_6907144
  simp only [CollatzResearch.WordTrace]
  refine ⟨125962119044302204561936243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167949492059069606082581657 125962119044302204561936243)
  ·
    refine ⟨188943178566453306842904365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125962119044302204561936243 188943178566453306842904365)
    ·
      refine ⟨70853691962419990066089137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188943178566453306842904365 70853691962419990066089137)
      ·
        refine ⟨53140268971814992549566853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70853691962419990066089137 53140268971814992549566853)
        ·
          refine ⟨9963800432215311103043785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53140268971814992549566853 9963800432215311103043785)
          ·
            refine ⟨7472850324161483327282839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9963800432215311103043785 7472850324161483327282839)
            ·
              refine ⟨11209275486242224990924259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472850324161483327282839 11209275486242224990924259)
              ·
                refine ⟨16813913229363337486386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209275486242224990924259 16813913229363337486386389)
                ·
                  refine ⟨394076091313203222337181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16813913229363337486386389 394076091313203222337181)
                  ·
                    rfl

theorem cell23_6907144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_6907144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907144 prefixEnd_6907144 := by exact prefixLift 6907144
  have htrace : WordTrace (prefixWord ++ tailWord_6907144) baseStart_6907144 baseEnd_6907144 := by
    simpa [prefixWord, tailWord_6907144, baseEnd_6907144] using wordTrace_append hprefix tailTrace_6907144
  have hstable : (prefixWord ++ tailWord_6907144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907144).length < 2 ^ (prefixWord ++ tailWord_6907144).sum := by decide
  have hdescent : baseEnd_6907144 < baseStart_6907144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907194 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_6907194 : Nat := 118140960795 + 6907194 * 2 ^ 59
def prefixEnd_6907194 : Nat := 4983230072969 + 3 ^ 40 * 6907194 * 2
def baseEnd_6907194 : Nat := 3546710495851553805409399

theorem tailTrace_6907194 : CollatzResearch.WordTrace tailWord_6907194 prefixEnd_6907194 3546710495851553805409399 := by
  unfold tailWord_6907194
  simp only [CollatzResearch.WordTrace]
  refine ⟨62981515434605816915798159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167950707825615511775461757 62981515434605816915798159)
  ·
    refine ⟨94472273151908725373697239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62981515434605816915798159 94472273151908725373697239)
    ·
      refine ⟨141708409727863088060545859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94472273151908725373697239 141708409727863088060545859)
      ·
        refine ⟨212562614591794632090818789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141708409727863088060545859 212562614591794632090818789)
        ·
          refine ⟨39855490235961493517028523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212562614591794632090818789 39855490235961493517028523)
          ·
            refine ⟨59783235353942240275542785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39855490235961493517028523 59783235353942240275542785)
            ·
              refine ⟨44837426515456680206657089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59783235353942240275542785 44837426515456680206657089)
              ·
                refine ⟨33628069886592510154992817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44837426515456680206657089 33628069886592510154992817)
                ·
                  refine ⟨25221052414944382616244613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33628069886592510154992817 25221052414944382616244613)
                  ·
                    refine ⟨4728947327802071740545865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25221052414944382616244613 4728947327802071740545865)
                    ·
                      refine ⟨3546710495851553805409399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4728947327802071740545865 3546710495851553805409399)
                      ·
                        rfl

theorem cell23_6907194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_6907194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907194 prefixEnd_6907194 := by exact prefixLift 6907194
  have htrace : WordTrace (prefixWord ++ tailWord_6907194) baseStart_6907194 baseEnd_6907194 := by
    simpa [prefixWord, tailWord_6907194, baseEnd_6907194] using wordTrace_append hprefix tailTrace_6907194
  have hstable : (prefixWord ++ tailWord_6907194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907194).length < 2 ^ (prefixWord ++ tailWord_6907194).sum := by decide
  have hdescent : baseEnd_6907194 < baseStart_6907194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907217 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 6]
def baseStart_6907217 : Nat := 118140960795 + 6907217 * 2 ^ 59
def prefixEnd_6907217 : Nat := 4983230072969 + 3 ^ 40 * 6907217 * 2
def baseEnd_6907217 : Nat := 394080256211845246157977

theorem tailTrace_6907217 : CollatzResearch.WordTrace tailWord_6907217 prefixEnd_6907217 394080256211845246157977 := by
  unfold tailWord_6907217
  simp only [CollatzResearch.WordTrace]
  refine ⟨251926900617339942591279905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167951267078226628394186603 251926900617339942591279905)
  ·
    refine ⟨188945175463004956943459929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251926900617339942591279905 188945175463004956943459929)
    ·
      refine ⟨141708881597253717707594947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188945175463004956943459929 141708881597253717707594947)
      ·
        refine ⟨212563322395880576561392421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141708881597253717707594947 212563322395880576561392421)
        ·
          refine ⟨39855622949227608105261079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212563322395880576561392421 39855622949227608105261079)
          ·
            refine ⟨59783434423841412157891619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39855622949227608105261079 59783434423841412157891619)
            ·
              refine ⟨89675151635762118236837429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59783434423841412157891619 89675151635762118236837429)
              ·
                refine ⟨8407045465852698584703509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89675151635762118236837429 8407045465852698584703509)
                ·
                  refine ⟨394080256211845246157977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8407045465852698584703509 394080256211845246157977)
                  ·
                    rfl

theorem cell23_6907217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_6907217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907217 prefixEnd_6907217 := by exact prefixLift 6907217
  have htrace : WordTrace (prefixWord ++ tailWord_6907217) baseStart_6907217 baseEnd_6907217 := by
    simpa [prefixWord, tailWord_6907217, baseEnd_6907217] using wordTrace_append hprefix tailTrace_6907217
  have hstable : (prefixWord ++ tailWord_6907217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907217).length < 2 ^ (prefixWord ++ tailWord_6907217).sum := by decide
  have hdescent : baseEnd_6907217 < baseStart_6907217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907261 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_6907261 : Nat := 118140960795 + 6907261 * 2 ^ 59
def prefixEnd_6907261 : Nat := 4983230072969 + 3 ^ 40 * 6907261 * 2
def baseEnd_6907261 : Nat := 3546744899055405043271591

theorem tailTrace_6907261 : CollatzResearch.WordTrace tailWord_6907261 prefixEnd_6907261 3546744899055405043271591 := by
  unfold tailWord_6907261
  simp only [CollatzResearch.WordTrace]
  refine ⟨251928505429180538105881637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167952336952787025403921091 251928505429180538105881637)
  ·
    refine ⟨47236594767971350894852807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251928505429180538105881637 47236594767971350894852807)
    ·
      refine ⟨70854892151957026342279211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47236594767971350894852807 70854892151957026342279211)
      ·
        refine ⟨106282338227935539513418817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70854892151957026342279211 106282338227935539513418817)
        ·
          refine ⟨79711753670951654635064113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106282338227935539513418817 79711753670951654635064113)
          ·
            refine ⟨59783815253213740976298085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79711753670951654635064113 59783815253213740976298085)
            ·
              refine ⟨11209465359977576433055891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59783815253213740976298085 11209465359977576433055891)
              ·
                refine ⟨16814198039966364649583837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11209465359977576433055891 16814198039966364649583837)
                ·
                  refine ⟨6305324264987386743593939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16814198039966364649583837 6305324264987386743593939)
                  ·
                    refine ⟨9457986397481080115390909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305324264987386743593939 9457986397481080115390909)
                    ·
                      refine ⟨3546744899055405043271591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9457986397481080115390909 3546744899055405043271591)
                      ·
                        rfl

theorem cell23_6907261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_6907261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907261 prefixEnd_6907261 := by exact prefixLift 6907261
  have htrace : WordTrace (prefixWord ++ tailWord_6907261) baseStart_6907261 baseEnd_6907261 := by
    simpa [prefixWord, tailWord_6907261, baseEnd_6907261] using wordTrace_append hprefix tailTrace_6907261
  have hstable : (prefixWord ++ tailWord_6907261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907261).length < 2 ^ (prefixWord ++ tailWord_6907261).sum := by decide
  have hdescent : baseEnd_6907261 < baseStart_6907261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6907287 : Nat := 118140960795 + 6907287 * 2 ^ 59
def prefixEnd_6907287 : Nat := 4983230072969 + 3 ^ 40 * 6907287 * 2
def baseEnd_6907287 : Nat := 3546758249552421941546471

theorem tailTrace_6907287 : CollatzResearch.WordTrace tailWord_6907287 prefixEnd_6907287 3546758249552421941546471 := by
  unfold tailWord_6907287
  simp only [CollatzResearch.WordTrace]
  refine ⟨251929453727086344546328115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167952969151390896364218743 251929453727086344546328115)
  ·
    refine ⟨377894180590629516819492173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251929453727086344546328115 377894180590629516819492173)
    ·
      refine ⟨141710317721486068807309565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377894180590629516819492173 141710317721486068807309565)
      ·
        refine ⟨53141369145557275802741087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141710317721486068807309565 53141369145557275802741087)
        ·
          refine ⟨79712053718335913704111631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53141369145557275802741087 79712053718335913704111631)
          ·
            refine ⟨119568080577503870556167447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79712053718335913704111631 119568080577503870556167447)
            ·
              refine ⟨179352120866255805834251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119568080577503870556167447 179352120866255805834251171)
              ·
                refine ⟨269028181299383708751376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179352120866255805834251171 269028181299383708751376757)
                ·
                  refine ⟨25221391996817222695441571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269028181299383708751376757 25221391996817222695441571)
                  ·
                    refine ⟨37832087995225834043162357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25221391996817222695441571 37832087995225834043162357)
                    ·
                      refine ⟨3546758249552421941546471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37832087995225834043162357 3546758249552421941546471)
                      ·
                        rfl

theorem cell23_6907287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6907287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907287 prefixEnd_6907287 := by exact prefixLift 6907287
  have htrace : WordTrace (prefixWord ++ tailWord_6907287) baseStart_6907287 baseEnd_6907287 := by
    simpa [prefixWord, tailWord_6907287, baseEnd_6907287] using wordTrace_append hprefix tailTrace_6907287
  have hstable : (prefixWord ++ tailWord_6907287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907287).length < 2 ^ (prefixWord ++ tailWord_6907287).sum := by decide
  have hdescent : baseEnd_6907287 < baseStart_6907287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907295 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 1, 1, 3]
def baseStart_6907295 : Nat := 118140960795 + 6907295 * 2 ^ 59
def prefixEnd_6907295 : Nat := 4983230072969 + 3 ^ 40 * 6907295 * 2
def baseEnd_6907295 : Nat := 3546762357397657910246435

theorem tailTrace_6907295 : CollatzResearch.WordTrace tailWord_6907295 prefixEnd_6907295 3546762357397657910246435 := by
  unfold tailWord_6907295
  simp only [CollatzResearch.WordTrace]
  refine ⟨251929745511057361912619339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167953163674038241275079559 251929745511057361912619339)
  ·
    refine ⟨377894618266586042868929009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251929745511057361912619339 377894618266586042868929009)
    ·
      refine ⟨283420963699939532151696757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377894618266586042868929009 283420963699939532151696757)
      ·
        refine ⟨26570715346869331139221571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283420963699939532151696757 26570715346869331139221571)
        ·
          refine ⟨39856073020303996708832357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26570715346869331139221571 39856073020303996708832357)
          ·
            refine ⟨7473013691306999382906067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39856073020303996708832357 7473013691306999382906067)
            ·
              refine ⟨11209520536960499074359101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473013691306999382906067 11209520536960499074359101)
              ·
                refine ⟨4203570201360187152884663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11209520536960499074359101 4203570201360187152884663)
                ·
                  refine ⟨6305355302040280729326995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203570201360187152884663 6305355302040280729326995)
                  ·
                    refine ⟨9458032953060421093990493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305355302040280729326995 9458032953060421093990493)
                    ·
                      refine ⟨3546762357397657910246435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458032953060421093990493 3546762357397657910246435)
                      ·
                        rfl

theorem cell23_6907295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_6907295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907295 prefixEnd_6907295 := by exact prefixLift 6907295
  have htrace : WordTrace (prefixWord ++ tailWord_6907295) baseStart_6907295 baseEnd_6907295 := by
    simpa [prefixWord, tailWord_6907295, baseEnd_6907295] using wordTrace_append hprefix tailTrace_6907295
  have hstable : (prefixWord ++ tailWord_6907295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907295).length < 2 ^ (prefixWord ++ tailWord_6907295).sum := by decide
  have hdescent : baseEnd_6907295 < baseStart_6907295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907338 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_6907338 : Nat := 118140960795 + 6907338 * 2 ^ 59
def prefixEnd_6907338 : Nat := 4983230072969 + 3 ^ 40 * 6907338 * 2
def baseEnd_6907338 : Nat := 3546784437065801242008737

theorem tailTrace_6907338 : CollatzResearch.WordTrace tailWord_6907338 prefixEnd_6907338 3546784437065801242008737 := by
  unfold tailWord_6907338
  simp only [CollatzResearch.WordTrace]
  refine ⟨62982828462475395064108667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167954209233267720170956445 62982828462475395064108667)
  ·
    refine ⟨94474242693713092596163001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62982828462475395064108667 94474242693713092596163001)
    ·
      refine ⟨70855682020284819447122251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94474242693713092596163001 70855682020284819447122251)
      ·
        refine ⟨106283523030427229170683377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70855682020284819447122251 106283523030427229170683377)
        ·
          refine ⟨79712642272820421878012533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106283523030427229170683377 79712642272820421878012533)
          ·
            refine ⟨7473060213076914551063675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79712642272820421878012533 7473060213076914551063675)
            ·
              refine ⟨11209590319615371826595513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473060213076914551063675 11209590319615371826595513)
              ·
                refine ⟨8407192739711528869946635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209590319615371826595513 8407192739711528869946635)
                ·
                  refine ⟨12610789109567293304919953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407192739711528869946635 12610789109567293304919953)
                  ·
                    refine ⟨9458091832175469978689965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12610789109567293304919953 9458091832175469978689965)
                    ·
                      refine ⟨3546784437065801242008737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458091832175469978689965 3546784437065801242008737)
                      ·
                        rfl

theorem cell23_6907338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_6907338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907338 prefixEnd_6907338 := by exact prefixLift 6907338
  have htrace : WordTrace (prefixWord ++ tailWord_6907338) baseStart_6907338 baseEnd_6907338 := by
    simpa [prefixWord, tailWord_6907338, baseEnd_6907338] using wordTrace_append hprefix tailTrace_6907338
  have hstable : (prefixWord ++ tailWord_6907338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907338).length < 2 ^ (prefixWord ++ tailWord_6907338).sum := by decide
  have hdescent : baseEnd_6907338 < baseStart_6907338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907344 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2]
def baseStart_6907344 : Nat := 118140960795 + 6907344 * 2 ^ 59
def prefixEnd_6907344 : Nat := 4983230072969 + 3 ^ 40 * 6907344 * 2
def baseEnd_6907344 : Nat := 3546787517949728218533709

theorem tailTrace_6907344 : CollatzResearch.WordTrace tailWord_6907344 prefixEnd_6907344 3546787517949728218533709 := by
  unfold tailWord_6907344
  simp only [CollatzResearch.WordTrace]
  refine ⟨125965766343939921640576543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167954355125253228854102057 125965766343939921640576543)
  ·
    refine ⟨188948649515909882460864815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125965766343939921640576543 188948649515909882460864815)
    ·
      refine ⟨283422974273864823691297223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188948649515909882460864815 283422974273864823691297223)
      ·
        refine ⟨425134461410797235536945835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283422974273864823691297223 425134461410797235536945835)
        ·
          refine ⟨637701692116195853305418753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425134461410797235536945835 637701692116195853305418753)
          ·
            refine ⟨478276269087146889979064065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637701692116195853305418753 478276269087146889979064065)
            ·
              refine ⟨358707201815360167484298049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478276269087146889979064065 358707201815360167484298049)
              ·
                refine ⟨269030401361520125613223537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358707201815360167484298049 269030401361520125613223537)
                ·
                  refine ⟨201772801021140094209917653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269030401361520125613223537 201772801021140094209917653)
                  ·
                    refine ⟨4729050023932970958044945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201772801021140094209917653 4729050023932970958044945)
                    ·
                      refine ⟨3546787517949728218533709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729050023932970958044945 3546787517949728218533709)
                      ·
                        rfl

theorem cell23_6907344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2].length) (baseStart_6907344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907344 prefixEnd_6907344 := by exact prefixLift 6907344
  have htrace : WordTrace (prefixWord ++ tailWord_6907344) baseStart_6907344 baseEnd_6907344 := by
    simpa [prefixWord, tailWord_6907344, baseEnd_6907344] using wordTrace_append hprefix tailTrace_6907344
  have hstable : (prefixWord ++ tailWord_6907344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907344).length < 2 ^ (prefixWord ++ tailWord_6907344).sum := by decide
  have hdescent : baseEnd_6907344 < baseStart_6907344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907368 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6907368 : Nat := 118140960795 + 6907368 * 2 ^ 59
def prefixEnd_6907368 : Nat := 4983230072969 + 3 ^ 40 * 6907368 * 2
def baseEnd_6907368 : Nat := 3546799841485436124633599

theorem tailTrace_6907368 : CollatzResearch.WordTrace tailWord_6907368 prefixEnd_6907368 3546799841485436124633599 := by
  unfold tailWord_6907368
  simp only [CollatzResearch.WordTrace]
  refine ⟨125966204019896447690013379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167954938693195263586684505 125966204019896447690013379)
  ·
    refine ⟨188949306029844671535020069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125966204019896447690013379 188949306029844671535020069)
    ·
      refine ⟨35427994880595875912816263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188949306029844671535020069 35427994880595875912816263)
      ·
        refine ⟨53141992320893813869224395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35427994880595875912816263 53141992320893813869224395)
        ·
          refine ⟨79712988481340720803836593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53141992320893813869224395 79712988481340720803836593)
          ·
            refine ⟨59784741361005540602877445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79712988481340720803836593 59784741361005540602877445)
            ·
              refine ⟨11209639005188538863039521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59784741361005540602877445 11209639005188538863039521)
              ·
                refine ⟨8407229253891404147279641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209639005188538863039521 8407229253891404147279641)
                ·
                  refine ⟨6305421940418553110459731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8407229253891404147279641 6305421940418553110459731)
                  ·
                    refine ⟨9458132910627829665689597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305421940418553110459731 9458132910627829665689597)
                    ·
                      refine ⟨3546799841485436124633599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9458132910627829665689597 3546799841485436124633599)
                      ·
                        rfl

theorem cell23_6907368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6907368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907368 prefixEnd_6907368 := by exact prefixLift 6907368
  have htrace : WordTrace (prefixWord ++ tailWord_6907368) baseStart_6907368 baseEnd_6907368 := by
    simpa [prefixWord, tailWord_6907368, baseEnd_6907368] using wordTrace_append hprefix tailTrace_6907368
  have hstable : (prefixWord ++ tailWord_6907368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907368).length < 2 ^ (prefixWord ++ tailWord_6907368).sum := by decide
  have hdescent : baseEnd_6907368 < baseStart_6907368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907374 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6907374 : Nat := 118140960795 + 6907374 * 2 ^ 59
def prefixEnd_6907374 : Nat := 4983230072969 + 3 ^ 40 * 6907374 * 2
def baseEnd_6907374 : Nat := 3546802922369363101158571

theorem tailTrace_6907374 : CollatzResearch.WordTrace tailWord_6907374 prefixEnd_6907374 3546802922369363101158571 := by
  unfold tailWord_6907374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491578359721394800593147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167955084585180772269830117 31491578359721394800593147)
  ·
    refine ⟨47237367539582092200889721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31491578359721394800593147 47237367539582092200889721)
    ·
      refine ⟨35428025654686569150667291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47237367539582092200889721 35428025654686569150667291)
      ·
        refine ⟨53142038482029853726000937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35428025654686569150667291 53142038482029853726000937)
        ·
          refine ⟨39856528861522390294500703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53142038482029853726000937 39856528861522390294500703)
          ·
            refine ⟨59784793292283585441751055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39856528861522390294500703 59784793292283585441751055)
            ·
              refine ⟨89677189938425378162626583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59784793292283585441751055 89677189938425378162626583)
              ·
                refine ⟨134515784907638067243939875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89677189938425378162626583 134515784907638067243939875)
                ·
                  refine ⟨201773677361457100865909813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134515784907638067243939875 201773677361457100865909813)
                  ·
                    refine ⟨18916282252636603206179045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201773677361457100865909813 18916282252636603206179045)
                    ·
                      refine ⟨3546802922369363101158571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18916282252636603206179045 3546802922369363101158571)
                      ·
                        rfl

theorem cell23_6907374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6907374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907374 prefixEnd_6907374 := by exact prefixLift 6907374
  have htrace : WordTrace (prefixWord ++ tailWord_6907374) baseStart_6907374 baseEnd_6907374 := by
    simpa [prefixWord, tailWord_6907374, baseEnd_6907374] using wordTrace_append hprefix tailTrace_6907374
  have hstable : (prefixWord ++ tailWord_6907374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907374).length < 2 ^ (prefixWord ++ tailWord_6907374).sum := by decide
  have hdescent : baseEnd_6907374 < baseStart_6907374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907378 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6907378 : Nat := 118140960795 + 6907378 * 2 ^ 59
def prefixEnd_6907378 : Nat := 4983230072969 + 3 ^ 40 * 6907378 * 2
def baseEnd_6907378 : Nat := 3546804976291981085508553

theorem tailTrace_6907378 : CollatzResearch.WordTrace tailWord_6907378 prefixEnd_6907378 3546804976291981085508553 := by
  unfold tailWord_6907378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983193192439166771972697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167955181846504444725260525 62983193192439166771972697)
  ·
    refine ⟨47237394894329375078979523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62983193192439166771972697 47237394894329375078979523)
    ·
      refine ⟨70856092341494062618469285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47237394894329375078979523 70856092341494062618469285)
      ·
        refine ⟨13285517314030136740962991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70856092341494062618469285 13285517314030136740962991)
        ·
          refine ⟨19928275971045205111444487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13285517314030136740962991 19928275971045205111444487)
          ·
            refine ⟨29892413956567807667166731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19928275971045205111444487 29892413956567807667166731)
            ·
              refine ⟨44838620934851711500750097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29892413956567807667166731 44838620934851711500750097)
              ·
                refine ⟨33628965701138783625562573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44838620934851711500750097 33628965701138783625562573)
                ·
                  refine ⟨12610862137927043859585965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33628965701138783625562573 12610862137927043859585965)
                  ·
                    refine ⟨4729073301722641447344737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12610862137927043859585965 4729073301722641447344737)
                    ·
                      refine ⟨3546804976291981085508553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729073301722641447344737 3546804976291981085508553)
                      ·
                        rfl

theorem cell23_6907378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6907378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907378 prefixEnd_6907378 := by exact prefixLift 6907378
  have htrace : WordTrace (prefixWord ++ tailWord_6907378) baseStart_6907378 baseEnd_6907378 := by
    simpa [prefixWord, tailWord_6907378, baseEnd_6907378] using wordTrace_append hprefix tailTrace_6907378
  have hstable : (prefixWord ++ tailWord_6907378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907378).length < 2 ^ (prefixWord ++ tailWord_6907378).sum := by decide
  have hdescent : baseEnd_6907378 < baseStart_6907378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907384 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_6907384 : Nat := 118140960795 + 6907384 * 2 ^ 59
def prefixEnd_6907384 : Nat := 4983230072969 + 3 ^ 40 * 6907384 * 2
def baseEnd_6907384 : Nat := 1182269352391969354011175

theorem tailTrace_6907384 : CollatzResearch.WordTrace tailWord_6907384 prefixEnd_6907384 1182269352391969354011175 := by
  unfold tailWord_6907384
  simp only [CollatzResearch.WordTrace]
  refine ⟨125966495803867465056304603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167955327738489953408406137 125966495803867465056304603)
  ·
    refine ⟨188949743705801197584456905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125966495803867465056304603 188949743705801197584456905)
    ·
      refine ⟨141712307779350898188342679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188949743705801197584456905 141712307779350898188342679)
      ·
        refine ⟨212568461669026347282514019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141712307779350898188342679 212568461669026347282514019)
        ·
          refine ⟨318852692503539520923771029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212568461669026347282514019 318852692503539520923771029)
          ·
            refine ⟨14946219961103415043301767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 318852692503539520923771029 14946219961103415043301767)
            ·
              refine ⟨22419329941655122564952651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946219961103415043301767 22419329941655122564952651)
              ·
                refine ⟨33628994912482683847428977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22419329941655122564952651 33628994912482683847428977)
                ·
                  refine ⟨25221746184362012885571733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33628994912482683847428977 25221746184362012885571733)
                  ·
                    refine ⟨1182269352391969354011175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25221746184362012885571733 1182269352391969354011175)
                    ·
                      rfl

theorem cell23_6907384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_6907384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907384 prefixEnd_6907384 := by exact prefixLift 6907384
  have htrace : WordTrace (prefixWord ++ tailWord_6907384) baseStart_6907384 baseEnd_6907384 := by
    simpa [prefixWord, tailWord_6907384, baseEnd_6907384] using wordTrace_append hprefix tailTrace_6907384
  have hstable : (prefixWord ++ tailWord_6907384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907384).length < 2 ^ (prefixWord ++ tailWord_6907384).sum := by decide
  have hdescent : baseEnd_6907384 < baseStart_6907384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907387 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_6907387 : Nat := 118140960795 + 6907387 * 2 ^ 59
def prefixEnd_6907387 : Nat := 4983230072969 + 3 ^ 40 * 6907387 * 2
def baseEnd_6907387 : Nat := 3546809597617871550296011

theorem tailTrace_6907387 : CollatzResearch.WordTrace tailWord_6907387 prefixEnd_6907387 3546809597617871550296011 := by
  unfold tailWord_6907387
  simp only [CollatzResearch.WordTrace]
  refine ⟨251933101026724061624968415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167955400684482707749978943 251933101026724061624968415)
  ·
    refine ⟨377899651540086092437452623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251933101026724061624968415 377899651540086092437452623)
    ·
      refine ⟨566849477310129138656178935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377899651540086092437452623 566849477310129138656178935)
      ·
        refine ⟨850274215965193707984268403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566849477310129138656178935 850274215965193707984268403)
        ·
          refine ⟨1275411323947790561976402605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850274215965193707984268403 1275411323947790561976402605)
          ·
            refine ⟨478279246480421460741150977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1275411323947790561976402605 478279246480421460741150977)
            ·
              refine ⟨358709434860316095555863233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478279246480421460741150977 358709434860316095555863233)
              ·
                refine ⟨269032076145237071666897425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358709434860316095555863233 269032076145237071666897425)
                ·
                  refine ⟨201774057108927803750173069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269032076145237071666897425 201774057108927803750173069)
                  ·
                    refine ⟨75665271415847926406314901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 201774057108927803750173069 75665271415847926406314901)
                    ·
                      refine ⟨3546809597617871550296011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75665271415847926406314901 3546809597617871550296011)
                      ·
                        rfl

theorem cell23_6907387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_6907387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907387 prefixEnd_6907387 := by exact prefixLift 6907387
  have htrace : WordTrace (prefixWord ++ tailWord_6907387) baseStart_6907387 baseEnd_6907387 := by
    simpa [prefixWord, tailWord_6907387, baseEnd_6907387] using wordTrace_append hprefix tailTrace_6907387
  have hstable : (prefixWord ++ tailWord_6907387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907387).length < 2 ^ (prefixWord ++ tailWord_6907387).sum := by decide
  have hdescent : baseEnd_6907387 < baseStart_6907387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907412 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6907412 : Nat := 118140960795 + 6907412 * 2 ^ 59
def prefixEnd_6907412 : Nat := 4983230072969 + 3 ^ 40 * 6907412 * 2
def baseEnd_6907412 : Nat := 3546822434634233952483397

theorem tailTrace_6907412 : CollatzResearch.WordTrace tailWord_6907412 prefixEnd_6907412 3546822434634233952483397 := by
  unfold tailWord_6907412
  simp only [CollatzResearch.WordTrace]
  refine ⟨125967006425816745447314245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167956008567755660596418993 125967006425816745447314245)
  ·
    refine ⟨23618813704840639771371421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125967006425816745447314245 23618813704840639771371421)
    ·
      refine ⟨8857055139315239914264283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23618813704840639771371421 8857055139315239914264283)
      ·
        refine ⟨13285582708972859871396425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857055139315239914264283 13285582708972859871396425)
        ·
          refine ⟨9964187031729644903547319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13285582708972859871396425 9964187031729644903547319)
          ·
            refine ⟨14946280547594467355320979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964187031729644903547319 14946280547594467355320979)
            ·
              refine ⟨22419420821391701032981469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946280547594467355320979 22419420821391701032981469)
              ·
                refine ⟨8407282808021887887368051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22419420821391701032981469 8407282808021887887368051)
                ·
                  refine ⟨12610924212032831831052077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407282808021887887368051 12610924212032831831052077)
                  ·
                    refine ⟨4729096579512311936644529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12610924212032831831052077 4729096579512311936644529)
                    ·
                      refine ⟨3546822434634233952483397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729096579512311936644529 3546822434634233952483397)
                      ·
                        rfl

theorem cell23_6907412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6907412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907412 prefixEnd_6907412 := by exact prefixLift 6907412
  have htrace : WordTrace (prefixWord ++ tailWord_6907412) baseStart_6907412 baseEnd_6907412 := by
    simpa [prefixWord, tailWord_6907412, baseEnd_6907412] using wordTrace_append hprefix tailTrace_6907412
  have hstable : (prefixWord ++ tailWord_6907412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907412).length < 2 ^ (prefixWord ++ tailWord_6907412).sum := by decide
  have hdescent : baseEnd_6907412 < baseStart_6907412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907425 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6907425 : Nat := 118140960795 + 6907425 * 2 ^ 59
def prefixEnd_6907425 : Nat := 4983230072969 + 3 ^ 40 * 6907425 * 2
def baseEnd_6907425 : Nat := 3546829109882742401620837

theorem tailTrace_6907425 : CollatzResearch.WordTrace tailWord_6907425 prefixEnd_6907425 3546829109882742401620837 := by
  unfold tailWord_6907425
  simp only [CollatzResearch.WordTrace]
  refine ⟨251934487000586394114851729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167956324667057596076567819 251934487000586394114851729)
  ·
    refine ⟨188950865250439795586138797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251934487000586394114851729 188950865250439795586138797)
    ·
      refine ⟨70856574468914923344802049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188950865250439795586138797 70856574468914923344802049)
      ·
        refine ⟨53142430851686192508601537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70856574468914923344802049 53142430851686192508601537)
        ·
          refine ⟨39856823138764644381451153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53142430851686192508601537 39856823138764644381451153)
          ·
            refine ⟨29892617354073483286088365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39856823138764644381451153 29892617354073483286088365)
            ·
              refine ⟨11209731507777556232283137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29892617354073483286088365 11209731507777556232283137)
              ·
                refine ⟨8407298630833167174212353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209731507777556232283137 8407298630833167174212353)
                ·
                  refine ⟨6305473973124875380659265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8407298630833167174212353 6305473973124875380659265)
                  ·
                    refine ⟨4729105479843656535494449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6305473973124875380659265 4729105479843656535494449)
                    ·
                      refine ⟨3546829109882742401620837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729105479843656535494449 3546829109882742401620837)
                      ·
                        rfl

theorem cell23_6907425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6907425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907425 prefixEnd_6907425 := by exact prefixLift 6907425
  have htrace : WordTrace (prefixWord ++ tailWord_6907425) baseStart_6907425 baseEnd_6907425 := by
    simpa [prefixWord, tailWord_6907425, baseEnd_6907425] using wordTrace_append hprefix tailTrace_6907425
  have hstable : (prefixWord ++ tailWord_6907425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907425).length < 2 ^ (prefixWord ++ tailWord_6907425).sum := by decide
  have hdescent : baseEnd_6907425 < baseStart_6907425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6907481 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 4, 2]
def baseStart_6907481 : Nat := 118140960795 + 6907481 * 2 ^ 59
def prefixEnd_6907481 : Nat := 4983230072969 + 3 ^ 40 * 6907481 * 2
def baseEnd_6907481 : Nat := 3546857864799394182520579

theorem tailTrace_6907481 : CollatzResearch.WordTrace tailWord_6907481 prefixEnd_6907481 3546857864799394182520579 := by
  unfold tailWord_6907481
  simp only [CollatzResearch.WordTrace]
  refine ⟨251936529488383515678890297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167957686325589010452593531 251936529488383515678890297)
  ·
    refine ⟨188952397116287636759167723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251936529488383515678890297 188952397116287636759167723)
    ·
      refine ⟨283428595674431455138751585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188952397116287636759167723 283428595674431455138751585)
      ·
        refine ⟨212571446755823591354063689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283428595674431455138751585 212571446755823591354063689)
        ·
          refine ⟨159428585066867693515547767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212571446755823591354063689 159428585066867693515547767)
          ·
            refine ⟨239142877600301540273321651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159428585066867693515547767 239142877600301540273321651)
            ·
              refine ⟨358714316400452310409982477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239142877600301540273321651 358714316400452310409982477)
              ·
                refine ⟨134517868650169616403743429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358714316400452310409982477 134517868650169616403743429)
                ·
                  refine ⟨25222100371906803075701893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134517868650169616403743429 25222100371906803075701893)
                  ·
                    refine ⟨4729143819732525576694105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25222100371906803075701893 4729143819732525576694105)
                    ·
                      refine ⟨3546857864799394182520579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4729143819732525576694105 3546857864799394182520579)
                      ·
                        rfl

theorem cell23_6907481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_6907481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6907481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6907481 prefixEnd_6907481 := by exact prefixLift 6907481
  have htrace : WordTrace (prefixWord ++ tailWord_6907481) baseStart_6907481 baseEnd_6907481 := by
    simpa [prefixWord, tailWord_6907481, baseEnd_6907481] using wordTrace_append hprefix tailTrace_6907481
  have hstable : (prefixWord ++ tailWord_6907481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6907481).length < 2 ^ (prefixWord ++ tailWord_6907481).sum := by decide
  have hdescent : baseEnd_6907481 < baseStart_6907481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6907481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
