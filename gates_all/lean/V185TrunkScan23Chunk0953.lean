import V185TrunkScan23Chunk0952

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5641742 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_5641742 : Nat := 118140960795 + 5641742 * 2 ^ 59
def prefixEnd_5641742 : Nat := 4983230072969 + 3 ^ 40 * 5641742 * 2
def baseEnd_5641742 : Nat := 321880597184241210242123

theorem tailTrace_5641742 : CollatzResearch.WordTrace tailWord_5641742 prefixEnd_5641742 321880597184241210242123 := by
  unfold tailWord_5641742
  simp only [CollatzResearch.WordTrace]
  refine ⟨25721404440867467708492935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137180823684626494445295653 25721404440867467708492935)
  ·
    refine ⟨38582106661301201562739403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25721404440867467708492935 38582106661301201562739403)
    ·
      refine ⟨57873159991951802344109105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38582106661301201562739403 57873159991951802344109105)
      ·
        refine ⟨43404869993963851758081829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57873159991951802344109105 43404869993963851758081829)
        ·
          refine ⟨8138413123868222204640343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43404869993963851758081829 8138413123868222204640343)
          ·
            refine ⟨12207619685802333306960515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8138413123868222204640343 12207619685802333306960515)
            ·
              refine ⟨18311429528703499960440773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12207619685802333306960515 18311429528703499960440773)
              ·
                refine ⟨3433393036631906242582645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18311429528703499960440773 3433393036631906242582645)
                ·
                  refine ⟨321880597184241210242123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433393036631906242582645 321880597184241210242123)
                  ·
                    rfl

theorem cell23_5641742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_5641742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641742 prefixEnd_5641742 := by exact prefixLift 5641742
  have htrace : WordTrace (prefixWord ++ tailWord_5641742) baseStart_5641742 baseEnd_5641742 := by
    simpa [prefixWord, tailWord_5641742, baseEnd_5641742] using wordTrace_append hprefix tailTrace_5641742
  have hstable : (prefixWord ++ tailWord_5641742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641742).length < 2 ^ (prefixWord ++ tailWord_5641742).sum := by decide
  have hdescent : baseEnd_5641742 < baseStart_5641742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641802 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_5641802 : Nat := 118140960795 + 5641802 * 2 ^ 59
def prefixEnd_5641802 : Nat := 4983230072969 + 3 ^ 40 * 5641802 * 2
def baseEnd_5641802 : Nat := 965652061165813552476277

theorem tailTrace_5641802 : CollatzResearch.WordTrace tailWord_5641802 prefixEnd_5641802 965652061165813552476277 := by
  unfold tailWord_5641802
  simp only [CollatzResearch.WordTrace]
  refine ⟨51443355976680592978781915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137182282604481581276751773 51443355976680592978781915)
  ·
    refine ⟨77165033965020889468172873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51443355976680592978781915 77165033965020889468172873)
    ·
      refine ⟨57873775473765667101129655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77165033965020889468172873 57873775473765667101129655)
      ·
        refine ⟨86810663210648500651694483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57873775473765667101129655 86810663210648500651694483)
        ·
          refine ⟨130215994815972750977541725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86810663210648500651694483 130215994815972750977541725)
          ·
            refine ⟨48830998055989781616578147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130215994815972750977541725 48830998055989781616578147)
            ·
              refine ⟨73246497083984672424867221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48830998055989781616578147 73246497083984672424867221)
              ·
                refine ⟨3433429550811781519915651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73246497083984672424867221 3433429550811781519915651)
                ·
                  refine ⟨5150144326217672279873477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433429550811781519915651 5150144326217672279873477)
                  ·
                    refine ⟨965652061165813552476277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150144326217672279873477 965652061165813552476277)
                    ·
                      rfl

theorem cell23_5641802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_5641802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641802 prefixEnd_5641802 := by exact prefixLift 5641802
  have htrace : WordTrace (prefixWord ++ tailWord_5641802) baseStart_5641802 baseEnd_5641802 := by
    simpa [prefixWord, tailWord_5641802, baseEnd_5641802] using wordTrace_append hprefix tailTrace_5641802
  have hstable : (prefixWord ++ tailWord_5641802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641802).length < 2 ^ (prefixWord ++ tailWord_5641802).sum := by decide
  have hdescent : baseEnd_5641802 < baseStart_5641802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641886 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5641886 : Nat := 118140960795 + 5641886 * 2 ^ 59
def prefixEnd_5641886 : Nat := 4983230072969 + 3 ^ 40 * 5641886 * 2
def baseEnd_5641886 : Nat := 2896999315872418328778445

theorem tailTrace_5641886 : CollatzResearch.WordTrace tailWord_5641886 prefixEnd_5641886 2896999315872418328778445 := by
  unfold tailWord_5641886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25722060954802256782648189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137184325092278702840790341 25722060954802256782648189)
  ·
    refine ⟨9645772858050846293493071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25722060954802256782648189 9645772858050846293493071)
    ·
      refine ⟨14468659287076269440239607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645772858050846293493071 14468659287076269440239607)
      ·
        refine ⟨21702988930614404160359411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14468659287076269440239607 21702988930614404160359411)
        ·
          refine ⟨32554483395921606240539117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21702988930614404160359411 32554483395921606240539117)
          ·
            refine ⟨12207931273470602340202169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32554483395921606240539117 12207931273470602340202169)
            ·
              refine ⟨9155948455102951755151627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12207931273470602340202169 9155948455102951755151627)
              ·
                refine ⟨13733922682654427632727441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9155948455102951755151627 13733922682654427632727441)
                ·
                  refine ⟨10300442011990820724545581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13733922682654427632727441 10300442011990820724545581)
                  ·
                    refine ⟨3862665754496557771704593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10300442011990820724545581 3862665754496557771704593)
                    ·
                      refine ⟨2896999315872418328778445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862665754496557771704593 2896999315872418328778445)
                      ·
                        rfl

theorem cell23_5641886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5641886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641886 prefixEnd_5641886 := by exact prefixLift 5641886
  have htrace : WordTrace (prefixWord ++ tailWord_5641886) baseStart_5641886 baseEnd_5641886 := by
    simpa [prefixWord, tailWord_5641886, baseEnd_5641886] using wordTrace_append hprefix tailTrace_5641886
  have hstable : (prefixWord ++ tailWord_5641886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641886).length < 2 ^ (prefixWord ++ tailWord_5641886).sum := by decide
  have hdescent : baseEnd_5641886 < baseStart_5641886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641910 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_5641910 : Nat := 118140960795 + 5641910 * 2 ^ 59
def prefixEnd_5641910 : Nat := 4983230072969 + 3 ^ 40 * 5641910 * 2
def baseEnd_5641910 : Nat := 2897011639408126234878335

theorem tailTrace_5641910 : CollatzResearch.WordTrace tailWord_5641910 prefixEnd_5641910 2897011639408126234878335 := by
  unfold tailWord_5641910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861085186895694147503699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137184908660220737573372789 12861085186895694147503699)
  ·
    refine ⟨19291627780343541221255549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12861085186895694147503699 19291627780343541221255549)
    ·
      refine ⟨7234360417628827957970831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19291627780343541221255549 7234360417628827957970831)
      ·
        refine ⟨10851540626443241936956247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234360417628827957970831 10851540626443241936956247)
        ·
          refine ⟨16277310939664862905434371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851540626443241936956247 16277310939664862905434371)
          ·
            refine ⟨24415966409497294358151557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16277310939664862905434371 24415966409497294358151557)
            ·
              refine ⟨4577993701780742692153417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24415966409497294358151557 4577993701780742692153417)
              ·
                refine ⟨3433495276335557019115063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577993701780742692153417 3433495276335557019115063)
                ·
                  refine ⟨5150242914503335528672595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433495276335557019115063 5150242914503335528672595)
                  ·
                    refine ⟨7725364371755003293008893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150242914503335528672595 7725364371755003293008893)
                    ·
                      refine ⟨2897011639408126234878335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7725364371755003293008893 2897011639408126234878335)
                      ·
                        rfl

theorem cell23_5641910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_5641910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641910 prefixEnd_5641910 := by exact prefixLift 5641910
  have htrace : WordTrace (prefixWord ++ tailWord_5641910) baseStart_5641910 baseEnd_5641910 := by
    simpa [prefixWord, tailWord_5641910, baseEnd_5641910] using wordTrace_append hprefix tailTrace_5641910
  have hstable : (prefixWord ++ tailWord_5641910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641910).length < 2 ^ (prefixWord ++ tailWord_5641910).sum := by decide
  have hdescent : baseEnd_5641910 < baseStart_5641910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641926 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5641926 : Nat := 118140960795 + 5641926 * 2 ^ 59
def prefixEnd_5641926 : Nat := 4983230072969 + 3 ^ 40 * 5641926 * 2
def baseEnd_5641926 : Nat := 965673285032866057426087

theorem tailTrace_5641926 : CollatzResearch.WordTrace tailWord_5641926 prefixEnd_5641926 965673285032866057426087 := by
  unfold tailWord_5641926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430560829946035659145051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137185297705515427395094421 6430560829946035659145051)
  ·
    refine ⟨9645841244919053488717577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6430560829946035659145051 9645841244919053488717577)
    ·
      refine ⟨7234380933689290116538183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9645841244919053488717577 7234380933689290116538183)
      ·
        refine ⟨10851571400533935174807275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234380933689290116538183 10851571400533935174807275)
        ·
          refine ⟨16277357100800902762210913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851571400533935174807275 16277357100800902762210913)
          ·
            refine ⟨12208017825600677071658185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16277357100800902762210913 12208017825600677071658185)
            ·
              refine ⟨9156013369200507803743639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12208017825600677071658185 9156013369200507803743639)
              ·
                refine ⟨13734020053800761705615459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9156013369200507803743639 13734020053800761705615459)
                ·
                  refine ⟨20601030080701142558423189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13734020053800761705615459 20601030080701142558423189)
                  ·
                    refine ⟨965673285032866057426087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20601030080701142558423189 965673285032866057426087)
                    ·
                      rfl

theorem cell23_5641926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5641926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641926 prefixEnd_5641926 := by exact prefixLift 5641926
  have htrace : WordTrace (prefixWord ++ tailWord_5641926) baseStart_5641926 baseEnd_5641926 := by
    simpa [prefixWord, tailWord_5641926, baseEnd_5641926] using wordTrace_append hprefix tailTrace_5641926
  have hstable : (prefixWord ++ tailWord_5641926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641926).length < 2 ^ (prefixWord ++ tailWord_5641926).sum := by decide
  have hdescent : baseEnd_5641926 < baseStart_5641926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641933 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5641933 : Nat := 118140960795 + 5641933 * 2 ^ 59
def prefixEnd_5641933 : Nat := 4983230072969 + 3 ^ 40 * 5641933 * 2
def baseEnd_5641933 : Nat := 2897023449463179644890729

theorem tailTrace_5641933 : CollatzResearch.WordTrace tailWord_5641933 prefixEnd_5641933 2897023449463179644890729 := by
  unfold tailWord_5641933
  simp only [CollatzResearch.WordTrace]
  refine ⟨205778201869247781288146453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137185467912831854192097635 205778201869247781288146453)
  ·
    refine ⟨9645853212620989747881865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205778201869247781288146453 9645853212620989747881865)
    ·
      refine ⟨7234389909465742310911399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9645853212620989747881865 7234389909465742310911399)
      ·
        refine ⟨10851584864198613466367099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234389909465742310911399 10851584864198613466367099)
        ·
          refine ⟨16277377296297920199550649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851584864198613466367099 16277377296297920199550649)
          ·
            refine ⟨12208032972223440149662987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16277377296297920199550649 12208032972223440149662987)
            ·
              refine ⟨18312049458335160224494481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12208032972223440149662987 18312049458335160224494481)
              ·
                refine ⟨13734037093751370168370861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18312049458335160224494481 13734037093751370168370861)
                ·
                  refine ⟨5150263910156763813139073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13734037093751370168370861 5150263910156763813139073)
                  ·
                    refine ⟨3862697932617572859854305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150263910156763813139073 3862697932617572859854305)
                    ·
                      refine ⟨2897023449463179644890729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862697932617572859854305 2897023449463179644890729)
                      ·
                        rfl

theorem cell23_5641933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5641933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641933 prefixEnd_5641933 := by exact prefixLift 5641933
  have htrace : WordTrace (prefixWord ++ tailWord_5641933) baseStart_5641933 baseEnd_5641933 := by
    simpa [prefixWord, tailWord_5641933, baseEnd_5641933] using wordTrace_append hprefix tailTrace_5641933
  have hstable : (prefixWord ++ tailWord_5641933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641933).length < 2 ^ (prefixWord ++ tailWord_5641933).sum := by decide
  have hdescent : baseEnd_5641933 < baseStart_5641933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641953 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_5641953 : Nat := 118140960795 + 5641953 * 2 ^ 59
def prefixEnd_5641953 : Nat := 4983230072969 + 3 ^ 40 * 5641953 * 2
def baseEnd_5641953 : Nat := 2897033719076269566640637

theorem tailTrace_5641953 : CollatzResearch.WordTrace tailWord_5641953 prefixEnd_5641953 2897033719076269566640637 := by
  unfold tailWord_5641953
  simp only [CollatzResearch.WordTrace]
  refine ⟨205778931329175324703874513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137185954219450216469249675 205778931329175324703874513)
  ·
    refine ⟨154334198496881493527905885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205778931329175324703874513 154334198496881493527905885)
    ·
      refine ⟨57875324436330560072964707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154334198496881493527905885 57875324436330560072964707)
      ·
        refine ⟨86812986654495840109447061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57875324436330560072964707 86812986654495840109447061)
        ·
          refine ⟨4069358749429492505130331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86812986654495840109447061 4069358749429492505130331)
          ·
            refine ⟨6104038124144238757695497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069358749429492505130331 6104038124144238757695497)
            ·
              refine ⟨4578028593108179068271623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104038124144238757695497 4578028593108179068271623)
              ·
                refine ⟨6867042889662268602407435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578028593108179068271623 6867042889662268602407435)
                ·
                  refine ⟨10300564334493402903611153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867042889662268602407435 10300564334493402903611153)
                  ·
                    refine ⟨7725423250870052177708365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10300564334493402903611153 7725423250870052177708365)
                    ·
                      refine ⟨2897033719076269566640637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7725423250870052177708365 2897033719076269566640637)
                      ·
                        rfl

theorem cell23_5641953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_5641953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641953 prefixEnd_5641953 := by exact prefixLift 5641953
  have htrace : WordTrace (prefixWord ++ tailWord_5641953) baseStart_5641953 baseEnd_5641953 := by
    simpa [prefixWord, tailWord_5641953, baseEnd_5641953] using wordTrace_append hprefix tailTrace_5641953
  have hstable : (prefixWord ++ tailWord_5641953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641953).length < 2 ^ (prefixWord ++ tailWord_5641953).sum := by decide
  have hdescent : baseEnd_5641953 < baseStart_5641953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641975 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_5641975 : Nat := 118140960795 + 5641975 * 2 ^ 59
def prefixEnd_5641975 : Nat := 4983230072969 + 3 ^ 40 * 5641975 * 2
def baseEnd_5641975 : Nat := 2897045015650668480565535

theorem tailTrace_5641975 : CollatzResearch.WordTrace tailWord_5641975 prefixEnd_5641975 2897045015650668480565535 := by
  unfold tailWord_5641975
  simp only [CollatzResearch.WordTrace]
  refine ⟨205779733735095622461175379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137186489156730414974116919 205779733735095622461175379)
  ·
    refine ⟨308669600602643433691763069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205779733735095622461175379 308669600602643433691763069)
    ·
      refine ⟨115751100225991287634411151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308669600602643433691763069 115751100225991287634411151)
      ·
        refine ⟨173626650338986931451616727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115751100225991287634411151 173626650338986931451616727)
        ·
          refine ⟨260439975508480397177425091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173626650338986931451616727 260439975508480397177425091)
          ·
            refine ⟨390659963262720595766137637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260439975508480397177425091 390659963262720595766137637)
            ·
              refine ⟨73248743111760111706150807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 390659963262720595766137637 73248743111760111706150807)
              ·
                refine ⟨109873114667640167559226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73248743111760111706150807 109873114667640167559226211)
                ·
                  refine ⟨164809672001460251338839317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109873114667640167559226211 164809672001460251338839317)
                  ·
                    refine ⟨7725453375068449281508093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164809672001460251338839317 7725453375068449281508093)
                    ·
                      refine ⟨2897045015650668480565535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7725453375068449281508093 2897045015650668480565535)
                      ·
                        rfl

theorem cell23_5641975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_5641975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641975 prefixEnd_5641975 := by exact prefixLift 5641975
  have htrace : WordTrace (prefixWord ++ tailWord_5641975) baseStart_5641975 baseEnd_5641975 := by
    simpa [prefixWord, tailWord_5641975, baseEnd_5641975] using wordTrace_append hprefix tailTrace_5641975
  have hstable : (prefixWord ++ tailWord_5641975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641975).length < 2 ^ (prefixWord ++ tailWord_5641975).sum := by decide
  have hdescent : baseEnd_5641975 < baseStart_5641975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5641995 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 7]
def baseStart_5641995 : Nat := 118140960795 + 5641995 * 2 ^ 59
def prefixEnd_5641995 : Nat := 4983230072969 + 3 ^ 40 * 5641995 * 2
def baseEnd_5641995 : Nat := 321895031695973155812827

theorem tailTrace_5641995 : CollatzResearch.WordTrace tailWord_5641995 prefixEnd_5641995 321895031695973155812827 := by
  unfold tailWord_5641995
  simp only [CollatzResearch.WordTrace]
  refine ⟨205780463195023165876903439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137186975463348777251268959 205780463195023165876903439)
  ·
    refine ⟨308670694792534748815355159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205780463195023165876903439 308670694792534748815355159)
    ·
      refine ⟨463006042188802123223032739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308670694792534748815355159 463006042188802123223032739)
      ·
        refine ⟨694509063283203184834549109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463006042188802123223032739 694509063283203184834549109)
        ·
          refine ⟨65110224682800298578238979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 694509063283203184834549109 65110224682800298578238979)
          ·
            refine ⟨97665337024200447867358469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65110224682800298578238979 97665337024200447867358469)
            ·
              refine ⟨18312250692037583975129713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97665337024200447867358469 18312250692037583975129713)
              ·
                refine ⟨13734188019028187981347285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18312250692037583975129713 13734188019028187981347285)
                ·
                  refine ⟨321895031695973155812827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13734188019028187981347285 321895031695973155812827)
                  ·
                    rfl

theorem cell23_5641995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 7].length) (baseStart_5641995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5641995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5641995 prefixEnd_5641995 := by exact prefixLift 5641995
  have htrace : WordTrace (prefixWord ++ tailWord_5641995) baseStart_5641995 baseEnd_5641995 := by
    simpa [prefixWord, tailWord_5641995, baseEnd_5641995] using wordTrace_append hprefix tailTrace_5641995
  have hstable : (prefixWord ++ tailWord_5641995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5641995).length < 2 ^ (prefixWord ++ tailWord_5641995).sum := by decide
  have hdescent : baseEnd_5641995 < baseStart_5641995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5641995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642055 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 8]
def baseStart_5642055 : Nat := 118140960795 + 5642055 * 2 ^ 59
def prefixEnd_5642055 : Nat := 4983230072969 + 3 ^ 40 * 5642055 * 2
def baseEnd_5642055 : Nat := 965695364701009389188389

theorem tailTrace_5642055 : CollatzResearch.WordTrace tailWord_5642055 prefixEnd_5642055 965695364701009389188389 := by
  unfold tailWord_5642055
  simp only [CollatzResearch.WordTrace]
  refine ⟨205782651574805796124087619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137188434383203864082725079 205782651574805796124087619)
  ·
    refine ⟨308673977362208694186131429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205782651574805796124087619 308673977362208694186131429)
    ·
      refine ⟨57876370755414130159899643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308673977362208694186131429 57876370755414130159899643)
      ·
        refine ⟨86814556133121195239849465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57876370755414130159899643 86814556133121195239849465)
        ·
          refine ⟨65110917099840896429887099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86814556133121195239849465 65110917099840896429887099)
          ·
            refine ⟨97666375649761344644830649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65110917099840896429887099 97666375649761344644830649)
            ·
              refine ⟨73249781737321008483622987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97666375649761344644830649 73249781737321008483622987)
              ·
                refine ⟨109874672605981512725434481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73249781737321008483622987 109874672605981512725434481)
                ·
                  refine ⟨82406004454486134544075861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109874672605981512725434481 82406004454486134544075861)
                  ·
                    refine ⟨965695364701009389188389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82406004454486134544075861 965695364701009389188389)
                    ·
                      rfl

theorem cell23_5642055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_5642055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642055 prefixEnd_5642055 := by exact prefixLift 5642055
  have htrace : WordTrace (prefixWord ++ tailWord_5642055) baseStart_5642055 baseEnd_5642055 := by
    simpa [prefixWord, tailWord_5642055, baseEnd_5642055] using wordTrace_append hprefix tailTrace_5642055
  have hstable : (prefixWord ++ tailWord_5642055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642055).length < 2 ^ (prefixWord ++ tailWord_5642055).sum := by decide
  have hdescent : baseEnd_5642055 < baseStart_5642055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642113 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5642113 : Nat := 118140960795 + 5642113 * 2 ^ 59
def prefixEnd_5642113 : Nat := 4983230072969 + 3 ^ 40 * 5642113 * 2
def baseEnd_5642113 : Nat := 2897115875980988940639901

theorem tailTrace_5642113 : CollatzResearch.WordTrace tailWord_5642113 prefixEnd_5642113 2897115875980988940639901 := by
  unfold tailWord_5642113
  simp only [CollatzResearch.WordTrace]
  refine ⟨205784767008595672029698993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137189844672397114686465995 205784767008595672029698993)
  ·
    refine ⟨154338575256446754022274245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205784767008595672029698993 154338575256446754022274245)
    ·
      refine ⟨28938482860583766379176421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154338575256446754022274245 28938482860583766379176421)
      ·
        refine ⟨5425965536359456196095579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28938482860583766379176421 5425965536359456196095579)
        ·
          refine ⟨8138948304539184294143369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5425965536359456196095579 8138948304539184294143369)
          ·
            refine ⟨6104211228404388220607527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8138948304539184294143369 6104211228404388220607527)
            ·
              refine ⟨9156316842606582330911291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104211228404388220607527 9156316842606582330911291)
              ·
                refine ⟨13734475263909873496366937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9156316842606582330911291 13734475263909873496366937)
                ·
                  refine ⟨10300856447932405122275203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13734475263909873496366937 10300856447932405122275203)
                  ·
                    refine ⟨15451284671898607683412805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10300856447932405122275203 15451284671898607683412805)
                    ·
                      refine ⟨2897115875980988940639901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15451284671898607683412805 2897115875980988940639901)
                      ·
                        rfl

theorem cell23_5642113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5642113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642113 prefixEnd_5642113 := by exact prefixLift 5642113
  have htrace : WordTrace (prefixWord ++ tailWord_5642113) baseStart_5642113 baseEnd_5642113 := by
    simpa [prefixWord, tailWord_5642113, baseEnd_5642113] using wordTrace_append hprefix tailTrace_5642113
  have hstable : (prefixWord ++ tailWord_5642113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642113).length < 2 ^ (prefixWord ++ tailWord_5642113).sum := by decide
  have hdescent : baseEnd_5642113 < baseStart_5642113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642169 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5642169 : Nat := 118140960795 + 5642169 * 2 ^ 59
def prefixEnd_5642169 : Nat := 4983230072969 + 3 ^ 40 * 5642169 * 2
def baseEnd_5642169 : Nat := 2897144630897640721539643

theorem tailTrace_5642169 : CollatzResearch.WordTrace tailWord_5642169 prefixEnd_5642169 2897144630897640721539643 := by
  unfold tailWord_5642169
  simp only [CollatzResearch.WordTrace]
  refine ⟨205786809496392793593737561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137191206330928529062491707 205786809496392793593737561)
  ·
    refine ⟨154340107122294595195303171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205786809496392793593737561 154340107122294595195303171)
    ·
      refine ⟨231510160683441892792954757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154340107122294595195303171 231510160683441892792954757)
      ·
        refine ⟨43408155128145354898679017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231510160683441892792954757 43408155128145354898679017)
        ·
          refine ⟨32556116346109016174009263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43408155128145354898679017 32556116346109016174009263)
          ·
            refine ⟨48834174519163524261013895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32556116346109016174009263 48834174519163524261013895)
            ·
              refine ⟨73251261778745286391520843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48834174519163524261013895 73251261778745286391520843)
              ·
                refine ⟨109876892668117929587281265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73251261778745286391520843 109876892668117929587281265)
                ·
                  refine ⟨82407669501088447190460949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109876892668117929587281265 82407669501088447190460949)
                  ·
                    refine ⟨3862859507863520962052857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82407669501088447190460949 3862859507863520962052857)
                    ·
                      refine ⟨2897144630897640721539643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862859507863520962052857 2897144630897640721539643)
                      ·
                        rfl

theorem cell23_5642169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5642169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642169 prefixEnd_5642169 := by exact prefixLift 5642169
  have htrace : WordTrace (prefixWord ++ tailWord_5642169) baseStart_5642169 baseEnd_5642169 := by
    simpa [prefixWord, tailWord_5642169, baseEnd_5642169] using wordTrace_append hprefix tailTrace_5642169
  have hstable : (prefixWord ++ tailWord_5642169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642169).length < 2 ^ (prefixWord ++ tailWord_5642169).sum := by decide
  have hdescent : baseEnd_5642169 < baseStart_5642169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642186 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2]
def baseStart_5642186 : Nat := 118140960795 + 5642186 * 2 ^ 59
def prefixEnd_5642186 : Nat := 4983230072969 + 3 ^ 40 * 5642186 * 2
def baseEnd_5642186 : Nat := 2897153360068767155027065

theorem tailTrace_5642186 : CollatzResearch.WordTrace tailWord_5642186 prefixEnd_5642186 2897153360068767155027065 := by
  unfold tailWord_5642186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51446857384332801374276603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137191619691554136998070941 51446857384332801374276603)
  ·
    refine ⟨77170286076499202061414905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51446857384332801374276603 77170286076499202061414905)
    ·
      refine ⟨57877714557374401546061179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77170286076499202061414905 57877714557374401546061179)
      ·
        refine ⟨86816571836061602319091769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57877714557374401546061179 86816571836061602319091769)
        ·
          refine ⟨65112428877046201739318827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86816571836061602319091769 65112428877046201739318827)
          ·
            refine ⟨97668643315569302608978241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65112428877046201739318827 97668643315569302608978241)
            ·
              refine ⟨73251482486676976956733681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97668643315569302608978241 73251482486676976956733681)
              ·
                refine ⟨54938611865007732717550261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73251482486676976956733681 54938611865007732717550261)
                ·
                  refine ⟨5150494862344474942270337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54938611865007732717550261 5150494862344474942270337)
                  ·
                    refine ⟨3862871146758356206702753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150494862344474942270337 3862871146758356206702753)
                    ·
                      refine ⟨2897153360068767155027065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862871146758356206702753 2897153360068767155027065)
                      ·
                        rfl

theorem cell23_5642186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_5642186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642186 prefixEnd_5642186 := by exact prefixLift 5642186
  have htrace : WordTrace (prefixWord ++ tailWord_5642186) baseStart_5642186 baseEnd_5642186 := by
    simpa [prefixWord, tailWord_5642186, baseEnd_5642186] using wordTrace_append hprefix tailTrace_5642186
  have hstable : (prefixWord ++ tailWord_5642186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642186).length < 2 ^ (prefixWord ++ tailWord_5642186).sum := by decide
  have hdescent : baseEnd_5642186 < baseStart_5642186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642196 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_5642196 : Nat := 118140960795 + 5642196 * 2 ^ 59
def prefixEnd_5642196 : Nat := 4983230072969 + 3 ^ 40 * 5642196 * 2
def baseEnd_5642196 : Nat := 965719498291770705300673

theorem tailTrace_5642196 : CollatzResearch.WordTrace tailWord_5642196 prefixEnd_5642196 965719498291770705300673 := by
  unfold tailWord_5642196
  simp only [CollatzResearch.WordTrace]
  refine ⟨102893897133647488602485221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137191862844863318136646961 102893897133647488602485221)
  ·
    refine ⟨19292605712558904112965979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102893897133647488602485221 19292605712558904112965979)
    ·
      refine ⟨28938908568838356169448969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19292605712558904112965979 28938908568838356169448969)
      ·
        refine ⟨21704181426628767127086727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28938908568838356169448969 21704181426628767127086727)
        ·
          refine ⟨32556272139943150690630091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21704181426628767127086727 32556272139943150690630091)
          ·
            refine ⟨48834408209914726035945137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32556272139943150690630091 48834408209914726035945137)
            ·
              refine ⟨36625806157436044526958853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48834408209914726035945137 36625806157436044526958853)
              ·
                refine ⟨6867338654519258348804785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36625806157436044526958853 6867338654519258348804785)
                ·
                  refine ⟨5150503990889443761603589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6867338654519258348804785 5150503990889443761603589)
                  ·
                    refine ⟨965719498291770705300673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150503990889443761603589 965719498291770705300673)
                    ·
                      rfl

theorem cell23_5642196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_5642196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642196 prefixEnd_5642196 := by exact prefixLift 5642196
  have htrace : WordTrace (prefixWord ++ tailWord_5642196) baseStart_5642196 baseEnd_5642196 := by
    simpa [prefixWord, tailWord_5642196, baseEnd_5642196] using wordTrace_append hprefix tailTrace_5642196
  have hstable : (prefixWord ++ tailWord_5642196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642196).length < 2 ^ (prefixWord ++ tailWord_5642196).sum := by decide
  have hdescent : baseEnd_5642196 < baseStart_5642196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642212 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_5642212 : Nat := 118140960795 + 5642212 * 2 ^ 59
def prefixEnd_5642212 : Nat := 4983230072969 + 3 ^ 40 * 5642212 * 2
def baseEnd_5642212 : Nat := 2897166710565784053301945

theorem tailTrace_5642212 : CollatzResearch.WordTrace tailWord_5642212 prefixEnd_5642212 2897166710565784053301945 := by
  unfold tailWord_5642212
  simp only [CollatzResearch.WordTrace]
  refine ⟨102894188917618505968776445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137192251890158007958368593 102894188917618505968776445)
  ·
    refine ⟨38585320844106939738291167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102894188917618505968776445 38585320844106939738291167)
    ·
      refine ⟨57877981266160409607436751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38585320844106939738291167 57877981266160409607436751)
      ·
        refine ⟨86816971899240614411155127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57877981266160409607436751 86816971899240614411155127)
        ·
          refine ⟨130225457848860921616732691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86816971899240614411155127 130225457848860921616732691)
          ·
            refine ⟨195338186773291382425099037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130225457848860921616732691 195338186773291382425099037)
            ·
              refine ⟨73251820039984268409412139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195338186773291382425099037 73251820039984268409412139)
              ·
                refine ⟨109877730059976402614118209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73251820039984268409412139 109877730059976402614118209)
                ·
                  refine ⟨82408297544982301960588657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109877730059976402614118209 82408297544982301960588657)
                  ·
                    refine ⟨61806223158736726470441493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82408297544982301960588657 61806223158736726470441493)
                    ·
                      refine ⟨2897166710565784053301945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61806223158736726470441493 2897166710565784053301945)
                      ·
                        rfl

theorem cell23_5642212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_5642212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642212 prefixEnd_5642212 := by exact prefixLift 5642212
  have htrace : WordTrace (prefixWord ++ tailWord_5642212) baseStart_5642212 baseEnd_5642212 := by
    simpa [prefixWord, tailWord_5642212, baseEnd_5642212] using wordTrace_append hprefix tailTrace_5642212
  have hstable : (prefixWord ++ tailWord_5642212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642212).length < 2 ^ (prefixWord ++ tailWord_5642212).sum := by decide
  have hdescent : baseEnd_5642212 < baseStart_5642212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642232 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_5642232 : Nat := 118140960795 + 5642232 * 2 ^ 59
def prefixEnd_5642232 : Nat := 4983230072969 + 3 ^ 40 * 5642232 * 2
def baseEnd_5642232 : Nat := 2897176980178873975051853

theorem tailTrace_5642232 : CollatzResearch.WordTrace tailWord_5642232 prefixEnd_5642232 2897176980178873975051853 := by
  unfold tailWord_5642232
  simp only [CollatzResearch.WordTrace]
  refine ⟨102894553647582277676640475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137192738196776370235520633 102894553647582277676640475)
  ·
    refine ⟨154341830471373416514960713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102894553647582277676640475 154341830471373416514960713)
    ·
      refine ⟨115756372853530062386220535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154341830471373416514960713 115756372853530062386220535)
      ·
        refine ⟨173634559280295093579330803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115756372853530062386220535 173634559280295093579330803)
        ·
          refine ⟨260451838920442640368996205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173634559280295093579330803 260451838920442640368996205)
          ·
            refine ⟨97669439595165990138373577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260451838920442640368996205 97669439595165990138373577)
            ·
              refine ⟨73252079696374492603780183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97669439595165990138373577 73252079696374492603780183)
              ·
                refine ⟨109878119544561738905670275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73252079696374492603780183 109878119544561738905670275)
                ·
                  refine ⟨164817179316842608358505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109878119544561738905670275 164817179316842608358505413)
                  ·
                    refine ⟨30903221121907989067219765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164817179316842608358505413 30903221121907989067219765)
                    ·
                      refine ⟨2897176980178873975051853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30903221121907989067219765 2897176980178873975051853)
                      ·
                        rfl

theorem cell23_5642232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_5642232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642232 prefixEnd_5642232 := by exact prefixLift 5642232
  have htrace : WordTrace (prefixWord ++ tailWord_5642232) baseStart_5642232 baseEnd_5642232 := by
    simpa [prefixWord, tailWord_5642232, baseEnd_5642232] using wordTrace_append hprefix tailTrace_5642232
  have hstable : (prefixWord ++ tailWord_5642232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642232).length < 2 ^ (prefixWord ++ tailWord_5642232).sum := by decide
  have hdescent : baseEnd_5642232 < baseStart_5642232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642260 : List Nat := [2, 4, 3, 2, 2, 1, 1, 8]
def baseStart_5642260 : Nat := 118140960795 + 5642260 * 2 ^ 59
def prefixEnd_5642260 : Nat := 4983230072969 + 3 ^ 40 * 5642260 * 2
def baseEnd_5642260 : Nat := 107303383616192587611175

theorem tailTrace_5642260 : CollatzResearch.WordTrace tailWord_5642260 prefixEnd_5642260 107303383616192587611175 := by
  unfold tailWord_5642260
  simp only [CollatzResearch.WordTrace]
  refine ⟨102895064269531558067650117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137193419026042077423533489 102895064269531558067650117)
  ·
    refine ⟨19292824550537167137684397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102895064269531558067650117 19292824550537167137684397)
    ·
      refine ⟨7234809206451437676631649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19292824550537167137684397 7234809206451437676631649)
      ·
        refine ⟨5426106904838578257473737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7234809206451437676631649 5426106904838578257473737)
        ·
          refine ⟨4069580178628933693105303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5426106904838578257473737 4069580178628933693105303)
          ·
            refine ⟨6104370267943400539657955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069580178628933693105303 6104370267943400539657955)
            ·
              refine ⟨9156555401915100809486933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104370267943400539657955 9156555401915100809486933)
              ·
                refine ⟨107303383616192587611175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9156555401915100809486933 107303383616192587611175)
                ·
                  rfl

theorem cell23_5642260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 8].length) (baseStart_5642260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642260 prefixEnd_5642260 := by exact prefixLift 5642260
  have htrace : WordTrace (prefixWord ++ tailWord_5642260) baseStart_5642260 baseEnd_5642260 := by
    simpa [prefixWord, tailWord_5642260, baseEnd_5642260] using wordTrace_append hprefix tailTrace_5642260
  have hstable : (prefixWord ++ tailWord_5642260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642260).length < 2 ^ (prefixWord ++ tailWord_5642260).sum := by decide
  have hdescent : baseEnd_5642260 < baseStart_5642260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642269 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5642269 : Nat := 118140960795 + 5642269 * 2 ^ 59
def prefixEnd_5642269 : Nat := 4983230072969 + 3 ^ 40 * 5642269 * 2
def baseEnd_5642269 : Nat := 965731992987696776763061

theorem tailTrace_5642269 : CollatzResearch.WordTrace tailWord_5642269 prefixEnd_5642269 965731992987696776763061 := by
  unfold tailWord_5642269
  simp only [CollatzResearch.WordTrace]
  refine ⟨205790456796030510672377861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137193637864020340448251907 205790456796030510672377861)
  ·
    refine ⟨38585710649255720751070849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205790456796030510672377861 38585710649255720751070849)
    ·
      refine ⟨28939282986941790563303137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38585710649255720751070849 28939282986941790563303137)
      ·
        refine ⟨21704462240206342922477353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28939282986941790563303137 21704462240206342922477353)
        ·
          refine ⟨16278346680154757191858015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21704462240206342922477353 16278346680154757191858015)
          ·
            refine ⟨24417520020232135787787023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16278346680154757191858015 24417520020232135787787023)
            ·
              refine ⟨36626280030348203681680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24417520020232135787787023 36626280030348203681680535)
              ·
                refine ⟨54939420045522305522520803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36626280030348203681680535 54939420045522305522520803)
                ·
                  refine ⟨82409130068283458283781205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54939420045522305522520803 82409130068283458283781205)
                  ·
                    refine ⟨965731992987696776763061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82409130068283458283781205 965731992987696776763061)
                    ·
                      rfl

theorem cell23_5642269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5642269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642269 prefixEnd_5642269 := by exact prefixLift 5642269
  have htrace : WordTrace (prefixWord ++ tailWord_5642269) baseStart_5642269 baseEnd_5642269 := by
    simpa [prefixWord, tailWord_5642269, baseEnd_5642269] using wordTrace_append hprefix tailTrace_5642269
  have hstable : (prefixWord ++ tailWord_5642269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642269).length < 2 ^ (prefixWord ++ tailWord_5642269).sum := by decide
  have hdescent : baseEnd_5642269 < baseStart_5642269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642297 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5642297 : Nat := 118140960795 + 5642297 * 2 ^ 59
def prefixEnd_5642297 : Nat := 4983230072969 + 3 ^ 40 * 5642297 * 2
def baseEnd_5642297 : Nat := 2897210356421416220739055

theorem tailTrace_5642297 : CollatzResearch.WordTrace tailWord_5642297 prefixEnd_5642297 2897210356421416220739055 := by
  unfold tailWord_5642297
  simp only [CollatzResearch.WordTrace]
  refine ⟨205791478039929071454397145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137194318693286047636264763 205791478039929071454397145)
  ·
    refine ⟨154343608529946803590797859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205791478039929071454397145 154343608529946803590797859)
    ·
      refine ⟨231515412794920205386196789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154343608529946803590797859 231515412794920205386196789)
      ·
        refine ⟨21704569949523769254955949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231515412794920205386196789 21704569949523769254955949)
        ·
          refine ⟨8139213731071413470608481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21704569949523769254955949 8139213731071413470608481)
          ·
            refine ⟨6104410298303560102956361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139213731071413470608481 6104410298303560102956361)
            ·
              refine ⟨4578307723727670077217271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104410298303560102956361 4578307723727670077217271)
              ·
                refine ⟨6867461585591505115825907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578307723727670077217271 6867461585591505115825907)
                ·
                  refine ⟨10301192378387257673738861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867461585591505115825907 10301192378387257673738861)
                  ·
                    refine ⟨3862947141895221627652073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10301192378387257673738861 3862947141895221627652073)
                    ·
                      refine ⟨2897210356421416220739055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3862947141895221627652073 2897210356421416220739055)
                      ·
                        rfl

theorem cell23_5642297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5642297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642297 prefixEnd_5642297 := by exact prefixLift 5642297
  have htrace : WordTrace (prefixWord ++ tailWord_5642297) baseStart_5642297 baseEnd_5642297 := by
    simpa [prefixWord, tailWord_5642297, baseEnd_5642297] using wordTrace_append hprefix tailTrace_5642297
  have hstable : (prefixWord ++ tailWord_5642297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642297).length < 2 ^ (prefixWord ++ tailWord_5642297).sum := by decide
  have hdescent : baseEnd_5642297 < baseStart_5642297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642316 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 5]
def baseStart_5642316 : Nat := 118140960795 + 5642316 * 2 ^ 59
def prefixEnd_5642316 : Nat := 4983230072969 + 3 ^ 40 * 5642316 * 2
def baseEnd_5642316 : Nat := 321913345839316849600163

theorem tailTrace_5642316 : CollatzResearch.WordTrace tailWord_5642316 prefixEnd_5642316 321913345839316849600163 := by
  unfold tailWord_5642316
  simp only [CollatzResearch.WordTrace]
  refine ⟨102896085513430118849669401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137194780684573491799559201 102896085513430118849669401)
  ·
    refine ⟨77172064135072589137252051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102896085513430118849669401 77172064135072589137252051)
    ·
      refine ⟨115758096202608883705878077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77172064135072589137252051 115758096202608883705878077)
      ·
        refine ⟨43409286075978331389704279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115758096202608883705878077 43409286075978331389704279)
        ·
          refine ⟨65113929113967497084556419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43409286075978331389704279 65113929113967497084556419)
          ·
            refine ⟨97670893670951245626834629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65113929113967497084556419 97670893670951245626834629)
            ·
              refine ⟨18313292563303358555031493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97670893670951245626834629 18313292563303358555031493)
              ·
                refine ⟨3433742355619379729068405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18313292563303358555031493 3433742355619379729068405)
                ·
                  refine ⟨321913345839316849600163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433742355619379729068405 321913345839316849600163)
                  ·
                    rfl

theorem cell23_5642316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_5642316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642316 prefixEnd_5642316 := by exact prefixLift 5642316
  have htrace : WordTrace (prefixWord ++ tailWord_5642316) baseStart_5642316 baseEnd_5642316 := by
    simpa [prefixWord, tailWord_5642316, baseEnd_5642316] using wordTrace_append hprefix tailTrace_5642316
  have hstable : (prefixWord ++ tailWord_5642316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642316).length < 2 ^ (prefixWord ++ tailWord_5642316).sum := by decide
  have hdescent : baseEnd_5642316 < baseStart_5642316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642450 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5642450 : Nat := 118140960795 + 5642450 * 2 ^ 59
def prefixEnd_5642450 : Nat := 4983230072969 + 3 ^ 40 * 5642450 * 2
def baseEnd_5642450 : Nat := 2897288918961554122125851

theorem tailTrace_5642450 : CollatzResearch.WordTrace tailWord_5642450 prefixEnd_5642450 2897288918961554122125851 := by
  unfold tailWord_5642450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449264602093694646179201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137198038938916519056477869 51449264602093694646179201)
  ·
    refine ⟨38586948451570270984634401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51449264602093694646179201 38586948451570270984634401)
    ·
      refine ⟨28940211338677703238475801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38586948451570270984634401 28940211338677703238475801)
      ·
        refine ⟨21705158504008277428856851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28940211338677703238475801 21705158504008277428856851)
        ·
          refine ⟨32557737756012416143285277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21705158504008277428856851 32557737756012416143285277)
          ·
            refine ⟨12209151658504656053731979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32557737756012416143285277 12209151658504656053731979)
            ·
              refine ⟨18313727487756984080597969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12209151658504656053731979 18313727487756984080597969)
              ·
                refine ⟨13735295615817738060448477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18313727487756984080597969 13735295615817738060448477)
                ·
                  refine ⟨5150735855931651772668179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13735295615817738060448477 5150735855931651772668179)
                  ·
                    refine ⟨7726103783897477659002269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150735855931651772668179 7726103783897477659002269)
                    ·
                      refine ⟨2897288918961554122125851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7726103783897477659002269 2897288918961554122125851)
                      ·
                        rfl

theorem cell23_5642450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5642450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642450 prefixEnd_5642450 := by exact prefixLift 5642450
  have htrace : WordTrace (prefixWord ++ tailWord_5642450) baseStart_5642450 baseEnd_5642450 := by
    simpa [prefixWord, tailWord_5642450, baseEnd_5642450] using wordTrace_append hprefix tailTrace_5642450
  have hstable : (prefixWord ++ tailWord_5642450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642450).length < 2 ^ (prefixWord ++ tailWord_5642450).sum := by decide
  have hdescent : baseEnd_5642450 < baseStart_5642450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642476 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5642476 : Nat := 118140960795 + 5642476 * 2 ^ 59
def prefixEnd_5642476 : Nat := 4983230072969 + 3 ^ 40 * 5642476 * 2
def baseEnd_5642476 : Nat := 2897302269458571020400731

theorem tailTrace_5642476 : CollatzResearch.WordTrace tailWord_5642476 prefixEnd_5642476 2897302269458571020400731 := by
  unfold tailWord_5642476
  simp only [CollatzResearch.WordTrace]
  refine ⟨102899003353140292512581641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137198671137520390016775521 102899003353140292512581641)
  ·
    refine ⟨77174252514855219384436231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102899003353140292512581641 77174252514855219384436231)
    ·
      refine ⟨115761378772282829076654347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77174252514855219384436231 115761378772282829076654347)
      ·
        refine ⟨173642068158424243614981521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115761378772282829076654347 173642068158424243614981521)
        ·
          refine ⟨130231551118818182711236141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173642068158424243614981521 130231551118818182711236141)
          ·
            refine ⟨48836831669556818516713553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130231551118818182711236141 48836831669556818516713553)
            ·
              refine ⟨36627623752167613887535165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48836831669556818516713553 36627623752167613887535165)
              ·
                refine ⟨13735358907062855207825687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36627623752167613887535165 13735358907062855207825687)
                ·
                  refine ⟨20603038360594282811738531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13735358907062855207825687 20603038360594282811738531)
                  ·
                    refine ⟨30904557540891424217607797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20603038360594282811738531 30904557540891424217607797)
                    ·
                      refine ⟨2897302269458571020400731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30904557540891424217607797 2897302269458571020400731)
                      ·
                        rfl

theorem cell23_5642476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5642476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642476 prefixEnd_5642476 := by exact prefixLift 5642476
  have htrace : WordTrace (prefixWord ++ tailWord_5642476) baseStart_5642476 baseEnd_5642476 := by
    simpa [prefixWord, tailWord_5642476, baseEnd_5642476] using wordTrace_append hprefix tailTrace_5642476
  have hstable : (prefixWord ++ tailWord_5642476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642476).length < 2 ^ (prefixWord ++ tailWord_5642476).sum := by decide
  have hdescent : baseEnd_5642476 < baseStart_5642476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642490 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2]
def baseStart_5642490 : Nat := 118140960795 + 5642490 * 2 ^ 59
def prefixEnd_5642490 : Nat := 4983230072969 + 3 ^ 40 * 5642490 * 2
def baseEnd_5642490 : Nat := 2897309458187733965625667

theorem tailTrace_5642490 : CollatzResearch.WordTrace tailWord_5642490 prefixEnd_5642490 2897309458187733965625667 := by
  unfold tailWord_5642490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449629332057466354043231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137199011552153243610781949 51449629332057466354043231)
  ·
    refine ⟨77174443998086199531064847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51449629332057466354043231 77174443998086199531064847)
    ·
      refine ⟨115761665997129299296597271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77174443998086199531064847 115761665997129299296597271)
      ·
        refine ⟨173642498995693948944895907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115761665997129299296597271 173642498995693948944895907)
        ·
          refine ⟨260463748493540923417343861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173642498995693948944895907 260463748493540923417343861)
          ·
            refine ⟨24418476421269461570375987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260463748493540923417343861 24418476421269461570375987)
            ·
              refine ⟨36627714631904192355563981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24418476421269461570375987 36627714631904192355563981)
              ·
                refine ⟨13735392986964072133336493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36627714631904192355563981 13735392986964072133336493)
                ·
                  refine ⟨5150772370111527050001185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13735392986964072133336493 5150772370111527050001185)
                  ·
                    refine ⟨3863079277583645287500889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150772370111527050001185 3863079277583645287500889)
                    ·
                      refine ⟨2897309458187733965625667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863079277583645287500889 2897309458187733965625667)
                      ·
                        rfl

theorem cell23_5642490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_5642490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642490 prefixEnd_5642490 := by exact prefixLift 5642490
  have htrace : WordTrace (prefixWord ++ tailWord_5642490) baseStart_5642490 baseEnd_5642490 := by
    simpa [prefixWord, tailWord_5642490, baseEnd_5642490] using wordTrace_append hprefix tailTrace_5642490
  have hstable : (prefixWord ++ tailWord_5642490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642490).length < 2 ^ (prefixWord ++ tailWord_5642490).sum := by decide
  have hdescent : baseEnd_5642490 < baseStart_5642490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642500 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_5642500 : Nat := 118140960795 + 5642500 * 2 ^ 59
def prefixEnd_5642500 : Nat := 4983230072969 + 3 ^ 40 * 5642500 * 2
def baseEnd_5642500 : Nat := 965771530998092975500207

theorem tailTrace_5642500 : CollatzResearch.WordTrace tailWord_5642500 prefixEnd_5642500 965771530998092975500207 := by
  unfold tailWord_5642500
  simp only [CollatzResearch.WordTrace]
  refine ⟨102899441029096818562018477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137199254705462424749357969 102899441029096818562018477)
  ·
    refine ⟨38587290385911306960756929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102899441029096818562018477 38587290385911306960756929)
    ·
      refine ⟨28940467789433480220567697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38587290385911306960756929 28940467789433480220567697)
      ·
        refine ⟨21705350842075110165425773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28940467789433480220567697 21705350842075110165425773)
        ·
          refine ⟨8139506565778166312034665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21705350842075110165425773 8139506565778166312034665)
          ·
            refine ⟨6104629924333624734025999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139506565778166312034665 6104629924333624734025999)
            ·
              refine ⟨9156944886500437101038999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104629924333624734025999 9156944886500437101038999)
              ·
                refine ⟨13735417329750655651558499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9156944886500437101038999 13735417329750655651558499)
                ·
                  refine ⟨20603125994625983477337749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13735417329750655651558499 20603125994625983477337749)
                  ·
                    refine ⟨965771530998092975500207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20603125994625983477337749 965771530998092975500207)
                    ·
                      rfl

theorem cell23_5642500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_5642500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642500 prefixEnd_5642500 := by exact prefixLift 5642500
  have htrace : WordTrace (prefixWord ++ tailWord_5642500) baseStart_5642500 baseEnd_5642500 := by
    simpa [prefixWord, tailWord_5642500, baseEnd_5642500] using wordTrace_append hprefix tailTrace_5642500
  have hstable : (prefixWord ++ tailWord_5642500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642500).length < 2 ^ (prefixWord ++ tailWord_5642500).sum := by decide
  have hdescent : baseEnd_5642500 < baseStart_5642500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642510 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_5642510 : Nat := 118140960795 + 5642510 * 2 ^ 59
def prefixEnd_5642510 : Nat := 4983230072969 + 3 ^ 40 * 5642510 * 2
def baseEnd_5642510 : Nat := 2897319727800823887375575

theorem tailTrace_5642510 : CollatzResearch.WordTrace tailWord_5642510 prefixEnd_5642510 2897319727800823887375575 := by
  unfold tailWord_5642510
  simp only [CollatzResearch.WordTrace]
  refine ⟨25724905848519676103987623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137199497858771605887933989 25724905848519676103987623)
  ·
    refine ⟨38587358772779514155981435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25724905848519676103987623 38587358772779514155981435)
    ·
      refine ⟨57881038159169271233972153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38587358772779514155981435 57881038159169271233972153)
      ·
        refine ⟨43410778619376953425479115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57881038159169271233972153 43410778619376953425479115)
        ·
          refine ⟨65116167929065430138218673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43410778619376953425479115 65116167929065430138218673)
          ·
            refine ⟨48837125946799072603664005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65116167929065430138218673 48837125946799072603664005)
            ·
              refine ⟨9156961115024826113187001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48837125946799072603664005 9156961115024826113187001)
              ·
                refine ⟨6867720836268619584890251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9156961115024826113187001 6867720836268619584890251)
                ·
                  refine ⟨10301581254402929377335377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867720836268619584890251 10301581254402929377335377)
                  ·
                    refine ⟨7726185940802197033001533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10301581254402929377335377 7726185940802197033001533)
                    ·
                      refine ⟨2897319727800823887375575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7726185940802197033001533 2897319727800823887375575)
                      ·
                        rfl

theorem cell23_5642510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_5642510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642510 prefixEnd_5642510 := by exact prefixLift 5642510
  have htrace : WordTrace (prefixWord ++ tailWord_5642510) baseStart_5642510 baseEnd_5642510 := by
    simpa [prefixWord, tailWord_5642510, baseEnd_5642510] using wordTrace_append hprefix tailTrace_5642510
  have hstable : (prefixWord ++ tailWord_5642510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642510).length < 2 ^ (prefixWord ++ tailWord_5642510).sum := by decide
  have hdescent : baseEnd_5642510 < baseStart_5642510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642513 : List Nat := [1, 2, 2, 1, 1, 7, 2, 7]
def baseStart_5642513 : Nat := 118140960795 + 5642513 * 2 ^ 59
def prefixEnd_5642513 : Nat := 4983230072969 + 3 ^ 40 * 5642513 * 2
def baseEnd_5642513 : Nat := 107308195120103236134743

theorem tailTrace_5642513 : CollatzResearch.WordTrace tailWord_5642513 prefixEnd_5642513 107308195120103236134743 := by
  unfold tailWord_5642513
  simp only [CollatzResearch.WordTrace]
  refine ⟨205799356207146540344260193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137199570804764360229506795 205799356207146540344260193)
  ·
    refine ⟨154349517155359905258195145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205799356207146540344260193 154349517155359905258195145)
    ·
      refine ⟨115762137866519928943646359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154349517155359905258195145 115762137866519928943646359)
      ·
        refine ⟨173643206799779893415469539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115762137866519928943646359 173643206799779893415469539)
        ·
          refine ⟨260464810199669840123204309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173643206799779893415469539 260464810199669840123204309)
          ·
            refine ⟨6104643989054761877887601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 260464810199669840123204309 6104643989054761877887601)
            ·
              refine ⟨4578482991791071408415701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104643989054761877887601 4578482991791071408415701)
              ·
                refine ⟨107308195120103236134743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4578482991791071408415701 107308195120103236134743)
                ·
                  rfl

theorem cell23_5642513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 7].length) (baseStart_5642513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642513 prefixEnd_5642513 := by exact prefixLift 5642513
  have htrace : WordTrace (prefixWord ++ tailWord_5642513) baseStart_5642513 baseEnd_5642513 := by
    simpa [prefixWord, tailWord_5642513, baseEnd_5642513] using wordTrace_append hprefix tailTrace_5642513
  have hstable : (prefixWord ++ tailWord_5642513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642513).length < 2 ^ (prefixWord ++ tailWord_5642513).sum := by decide
  have hdescent : baseEnd_5642513 < baseStart_5642513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642523 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 3]
def baseStart_5642523 : Nat := 118140960795 + 5642523 * 2 ^ 59
def prefixEnd_5642523 : Nat := 4983230072969 + 3 ^ 40 * 5642523 * 2
def baseEnd_5642523 : Nat := 2897326403049332336513015

theorem tailTrace_5642523 : CollatzResearch.WordTrace tailWord_5642523 prefixEnd_5642523 2897326403049332336513015 := by
  unfold tailWord_5642523
  simp only [CollatzResearch.WordTrace]
  refine ⟨205799720937110312052124223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137199813958073541368082815 205799720937110312052124223)
  ·
    refine ⟨308699581405665468078186335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205799720937110312052124223 308699581405665468078186335)
    ·
      refine ⟨463049372108498202117279503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308699581405665468078186335 463049372108498202117279503)
      ·
        refine ⟨694574058162747303175919255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463049372108498202117279503 694574058162747303175919255)
        ·
          refine ⟨1041861087244120954763878883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694574058162747303175919255 1041861087244120954763878883)
          ·
            refine ⟨1562791630866181432145818325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041861087244120954763878883 1562791630866181432145818325)
            ·
              refine ⟨36627928848426127315917617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1562791630866181432145818325 36627928848426127315917617)
              ·
                refine ⟨27470946636319595486938213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36627928848426127315917617 27470946636319595486938213)
                ·
                  refine ⟨5150802494309924153800915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27470946636319595486938213 5150802494309924153800915)
                  ·
                    refine ⟨7726203741464886230701373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150802494309924153800915 7726203741464886230701373)
                    ·
                      refine ⟨2897326403049332336513015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7726203741464886230701373 2897326403049332336513015)
                      ·
                        rfl

theorem cell23_5642523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 3].length) (baseStart_5642523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642523 prefixEnd_5642523 := by exact prefixLift 5642523
  have htrace : WordTrace (prefixWord ++ tailWord_5642523) baseStart_5642523 baseEnd_5642523 := by
    simpa [prefixWord, tailWord_5642523, baseEnd_5642523] using wordTrace_append hprefix tailTrace_5642523
  have hstable : (prefixWord ++ tailWord_5642523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642523).length < 2 ^ (prefixWord ++ tailWord_5642523).sum := by decide
  have hdescent : baseEnd_5642523 < baseStart_5642523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642541 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5642541 : Nat := 118140960795 + 5642541 * 2 ^ 59
def prefixEnd_5642541 : Nat := 4983230072969 + 3 ^ 40 * 5642541 * 2
def baseEnd_5642541 : Nat := 2897335645701113266087933

theorem tailTrace_5642541 : CollatzResearch.WordTrace tailWord_5642541 prefixEnd_5642541 2897335645701113266087933 := by
  unfold tailWord_5642541
  simp only [CollatzResearch.WordTrace]
  refine ⟨205800377451045101126279477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137200251634030067417519651 205800377451045101126279477)
  ·
    refine ⟨19293785386035478230588701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205800377451045101126279477 19293785386035478230588701)
    ·
      refine ⟨7235169519763304336470763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19293785386035478230588701 7235169519763304336470763)
      ·
        refine ⟨10852754279644956504706145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7235169519763304336470763 10852754279644956504706145)
        ·
          refine ⟨8139565709733717378529609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10852754279644956504706145 8139565709733717378529609)
          ·
            refine ⟨6104674282300288033897207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139565709733717378529609 6104674282300288033897207)
            ·
              refine ⟨9157011423450432050845811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104674282300288033897207 9157011423450432050845811)
              ·
                refine ⟨13735517135175648076268717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157011423450432050845811 13735517135175648076268717)
                ·
                  refine ⟨5150818925690868028600769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13735517135175648076268717 5150818925690868028600769)
                  ·
                    refine ⟨3863114194268151021450577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150818925690868028600769 3863114194268151021450577)
                    ·
                      refine ⟨2897335645701113266087933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863114194268151021450577 2897335645701113266087933)
                      ·
                        rfl

theorem cell23_5642541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5642541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642541 prefixEnd_5642541 := by exact prefixLift 5642541
  have htrace : WordTrace (prefixWord ++ tailWord_5642541) baseStart_5642541 baseEnd_5642541 := by
    simpa [prefixWord, tailWord_5642541, baseEnd_5642541] using wordTrace_append hprefix tailTrace_5642541
  have hstable : (prefixWord ++ tailWord_5642541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642541).length < 2 ^ (prefixWord ++ tailWord_5642541).sum := by decide
  have hdescent : baseEnd_5642541 < baseStart_5642541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642556 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_5642556 : Nat := 118140960795 + 5642556 * 2 ^ 59
def prefixEnd_5642556 : Nat := 4983230072969 + 3 ^ 40 * 5642556 * 2
def baseEnd_5642556 : Nat := 965781115970310235800121

theorem tailTrace_5642556 : CollatzResearch.WordTrace tailWord_5642556 prefixEnd_5642556 965781115970310235800121 := by
  unfold tailWord_5642556
  simp only [CollatzResearch.WordTrace]
  refine ⟨102900462272995379344037761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137200616363993839125383681 102900462272995379344037761)
  ·
    refine ⟨77175346704746534508028321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102900462272995379344037761 77175346704746534508028321)
    ·
      refine ⟨57881510028559900881021241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77175346704746534508028321 57881510028559900881021241)
      ·
        refine ⟨43411132521419925660765931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57881510028559900881021241 43411132521419925660765931)
        ·
          refine ⟨65116698782129888491148897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43411132521419925660765931 65116698782129888491148897)
          ·
            refine ⟨48837524086597416368361673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65116698782129888491148897 48837524086597416368361673)
            ·
              refine ⟨36628143064948062276271255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48837524086597416368361673 36628143064948062276271255)
              ·
                refine ⟨54942214597422093414406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36628143064948062276271255 54942214597422093414406883)
                ·
                  refine ⟨82413321896133140121610325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54942214597422093414406883 82413321896133140121610325)
                  ·
                    refine ⟨965781115970310235800121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82413321896133140121610325 965781115970310235800121)
                    ·
                      rfl

theorem cell23_5642556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_5642556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642556 prefixEnd_5642556 := by exact prefixLift 5642556
  have htrace : WordTrace (prefixWord ++ tailWord_5642556) baseStart_5642556 baseEnd_5642556 := by
    simpa [prefixWord, tailWord_5642556, baseEnd_5642556] using wordTrace_append hprefix tailTrace_5642556
  have hstable : (prefixWord ++ tailWord_5642556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642556).length < 2 ^ (prefixWord ++ tailWord_5642556).sum := by decide
  have hdescent : baseEnd_5642556 < baseStart_5642556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642580 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_5642580 : Nat := 118140960795 + 5642580 * 2 ^ 59
def prefixEnd_5642580 : Nat := 4983230072969 + 3 ^ 40 * 5642580 * 2
def baseEnd_5642580 : Nat := 2897355671446638613500253

theorem tailTrace_5642580 : CollatzResearch.WordTrace tailWord_5642580 prefixEnd_5642580 2897355671446638613500253 := by
  unfold tailWord_5642580
  simp only [CollatzResearch.WordTrace]
  refine ⟨102900899948951905393474597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137201199931935873857966129 102900899948951905393474597)
  ·
    refine ⟨19293918740428482261276487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102900899948951905393474597 19293918740428482261276487)
    ·
      refine ⟨28940878110642723391914731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293918740428482261276487 28940878110642723391914731)
      ·
        refine ⟨43411317165964085087872097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28940878110642723391914731 43411317165964085087872097)
        ·
          refine ⟨32558487874473063815904073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43411317165964085087872097 32558487874473063815904073)
          ·
            refine ⟨24418865905854797861928055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32558487874473063815904073 24418865905854797861928055)
            ·
              refine ⟨36628298858782196792892083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24418865905854797861928055 36628298858782196792892083)
              ·
                refine ⟨54942448288173295189338125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36628298858782196792892083 54942448288173295189338125)
                ·
                  refine ⟨20603418108064985696001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54942448288173295189338125 20603418108064985696001797)
                  ·
                    refine ⟨3863140895262184818000337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20603418108064985696001797 3863140895262184818000337)
                    ·
                      refine ⟨2897355671446638613500253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863140895262184818000337 2897355671446638613500253)
                      ·
                        rfl

theorem cell23_5642580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_5642580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642580 prefixEnd_5642580 := by exact prefixLift 5642580
  have htrace : WordTrace (prefixWord ++ tailWord_5642580) baseStart_5642580 baseEnd_5642580 := by
    simpa [prefixWord, tailWord_5642580, baseEnd_5642580] using wordTrace_append hprefix tailTrace_5642580
  have hstable : (prefixWord ++ tailWord_5642580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642580).length < 2 ^ (prefixWord ++ tailWord_5642580).sum := by decide
  have hdescent : baseEnd_5642580 < baseStart_5642580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642597 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_5642597 : Nat := 118140960795 + 5642597 * 2 ^ 59
def prefixEnd_5642597 : Nat := 4983230072969 + 3 ^ 40 * 5642597 * 2
def baseEnd_5642597 : Nat := 2897364400617765046987675

theorem tailTrace_5642597 : CollatzResearch.WordTrace tailWord_5642597 prefixEnd_5642597 2897364400617765046987675 := by
  unfold tailWord_5642597
  simp only [CollatzResearch.WordTrace]
  refine ⟨205802419938842222690318045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137201613292561481793545363 205802419938842222690318045)
  ·
    refine ⟨77175907477065833508869267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205802419938842222690318045 77175907477065833508869267)
    ·
      refine ⟨115763861215598750263303901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77175907477065833508869267 115763861215598750263303901)
      ·
        refine ⟨43411447955849531348738963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115763861215598750263303901 43411447955849531348738963)
        ·
          refine ⟨65117171933774297023108445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43411447955849531348738963 65117171933774297023108445)
          ·
            refine ⟨24418939475165361383665667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65117171933774297023108445 24418939475165361383665667)
            ·
              refine ⟨36628409212748042075498501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24418939475165361383665667 36628409212748042075498501)
              ·
                refine ⟨6867826727390257889155969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36628409212748042075498501 6867826727390257889155969)
                ·
                  refine ⟨5150870045542693416866977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6867826727390257889155969 5150870045542693416866977)
                  ·
                    refine ⟨3863152534157020062650233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5150870045542693416866977 3863152534157020062650233)
                    ·
                      refine ⟨2897364400617765046987675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863152534157020062650233 2897364400617765046987675)
                      ·
                        rfl

theorem cell23_5642597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_5642597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642597 prefixEnd_5642597 := by exact prefixLift 5642597
  have htrace : WordTrace (prefixWord ++ tailWord_5642597) baseStart_5642597 baseEnd_5642597 := by
    simpa [prefixWord, tailWord_5642597, baseEnd_5642597] using wordTrace_append hprefix tailTrace_5642597
  have hstable : (prefixWord ++ tailWord_5642597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642597).length < 2 ^ (prefixWord ++ tailWord_5642597).sum := by decide
  have hdescent : baseEnd_5642597 < baseStart_5642597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642603 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 5]
def baseStart_5642603 : Nat := 118140960795 + 5642603 * 2 ^ 59
def prefixEnd_5642603 : Nat := 4983230072969 + 3 ^ 40 * 5642603 * 2
def baseEnd_5642603 : Nat := 321929720166854669279183

theorem tailTrace_5642603 : CollatzResearch.WordTrace tailWord_5642603 prefixEnd_5642603 321929720166854669279183 := by
  unfold tailWord_5642603
  simp only [CollatzResearch.WordTrace]
  refine ⟨205802638776820485715036463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137201759184546990476690975 205802638776820485715036463)
  ·
    refine ⟨308703958165230728572554695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205802638776820485715036463 308703958165230728572554695)
    ·
      refine ⟨463055937247846092858832043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308703958165230728572554695 463055937247846092858832043)
      ·
        refine ⟨694583905871769139288248065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463055937247846092858832043 694583905871769139288248065)
        ·
          refine ⟨520937929403826854466186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694583905871769139288248065 520937929403826854466186049)
          ·
            refine ⟨390703447052870140849639537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520937929403826854466186049 390703447052870140849639537)
            ·
              refine ⟨293027585289652605637229653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390703447052870140849639537 293027585289652605637229653)
              ·
                refine ⟨3433917015113116472311285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 293027585289652605637229653 3433917015113116472311285)
                ·
                  refine ⟨321929720166854669279183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433917015113116472311285 321929720166854669279183)
                  ·
                    rfl

theorem cell23_5642603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 5].length) (baseStart_5642603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642603 prefixEnd_5642603 := by exact prefixLift 5642603
  have htrace : WordTrace (prefixWord ++ tailWord_5642603) baseStart_5642603 baseEnd_5642603 := by
    simpa [prefixWord, tailWord_5642603, baseEnd_5642603] using wordTrace_append hprefix tailTrace_5642603
  have hstable : (prefixWord ++ tailWord_5642603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642603).length < 2 ^ (prefixWord ++ tailWord_5642603).sum := by decide
  have hdescent : baseEnd_5642603 < baseStart_5642603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642633 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_5642633 : Nat := 118140960795 + 5642633 * 2 ^ 59
def prefixEnd_5642633 : Nat := 4983230072969 + 3 ^ 40 * 5642633 * 2
def baseEnd_5642633 : Nat := 965794295307108968712503

theorem tailTrace_5642633 : CollatzResearch.WordTrace tailWord_5642633 prefixEnd_5642633 965794295307108968712503 := by
  unfold tailWord_5642633
  simp only [CollatzResearch.WordTrace]
  refine ⟨205803732966711800838628553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137202488644474533892419035 205803732966711800838628553)
  ·
    refine ⟨154352799725033850628971415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205803732966711800838628553 154352799725033850628971415)
    ·
      refine ⟨231529199587550775943457123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154352799725033850628971415 231529199587550775943457123)
      ·
        refine ⟨347293799381326163915185685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231529199587550775943457123 347293799381326163915185685)
        ·
          refine ⟨16279396845999663933524329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 347293799381326163915185685 16279396845999663933524329)
          ·
            refine ⟨12209547634499747950143247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16279396845999663933524329 12209547634499747950143247)
            ·
              refine ⟨18314321451749621925214871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12209547634499747950143247 18314321451749621925214871)
              ·
                refine ⟨27471482177624432887822307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18314321451749621925214871 27471482177624432887822307)
                ·
                  refine ⟨41207223266436649331733461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27471482177624432887822307 41207223266436649331733461)
                  ·
                    refine ⟨965794295307108968712503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41207223266436649331733461 965794295307108968712503)
                    ·
                      rfl

theorem cell23_5642633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_5642633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642633 prefixEnd_5642633 := by exact prefixLift 5642633
  have htrace : WordTrace (prefixWord ++ tailWord_5642633) baseStart_5642633 baseEnd_5642633 := by
    simpa [prefixWord, tailWord_5642633, baseEnd_5642633] using wordTrace_append hprefix tailTrace_5642633
  have hstable : (prefixWord ++ tailWord_5642633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642633).length < 2 ^ (prefixWord ++ tailWord_5642633).sum := by decide
  have hdescent : baseEnd_5642633 < baseStart_5642633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642697 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 1, 4]
def baseStart_5642697 : Nat := 118140960795 + 5642697 * 2 ^ 59
def prefixEnd_5642697 : Nat := 4983230072969 + 3 ^ 40 * 5642697 * 2
def baseEnd_5642697 : Nat := 965805249561071551912405

theorem tailTrace_5642697 : CollatzResearch.WordTrace tailWord_5642697 prefixEnd_5642697 965805249561071551912405 := by
  unfold tailWord_5642697
  simp only [CollatzResearch.WordTrace]
  refine ⟨205806067238479939768958345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137204044825653293179305563 205806067238479939768958345)
  ·
    refine ⟨154354550428859954826718759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205806067238479939768958345 154354550428859954826718759)
    ·
      refine ⟨231531825643289932240078139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154354550428859954826718759 231531825643289932240078139)
      ·
        refine ⟨347297738464934898360117209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231531825643289932240078139 347297738464934898360117209)
        ·
          refine ⟨260473303848701173770087907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347297738464934898360117209 260473303848701173770087907)
          ·
            refine ⟨390709955773051760655131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260473303848701173770087907 390709955773051760655131861)
            ·
              refine ⟨9157264588430900640354653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 390709955773051760655131861 9157264588430900640354653)
              ·
                refine ⟨3433974220661587740132995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9157264588430900640354653 3433974220661587740132995)
                ·
                  refine ⟨5150961330992381610199493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433974220661587740132995 5150961330992381610199493)
                  ·
                    refine ⟨965805249561071551912405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150961330992381610199493 965805249561071551912405)
                    ·
                      rfl

theorem cell23_5642697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_5642697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642697 prefixEnd_5642697 := by exact prefixLift 5642697
  have htrace : WordTrace (prefixWord ++ tailWord_5642697) baseStart_5642697 baseEnd_5642697 := by
    simpa [prefixWord, tailWord_5642697, baseEnd_5642697] using wordTrace_append hprefix tailTrace_5642697
  have hstable : (prefixWord ++ tailWord_5642697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642697).length < 2 ^ (prefixWord ++ tailWord_5642697).sum := by decide
  have hdescent : baseEnd_5642697 < baseStart_5642697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642710 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5642710 : Nat := 118140960795 + 5642710 * 2 ^ 59
def prefixEnd_5642710 : Nat := 4983230072969 + 3 ^ 40 * 5642710 * 2
def baseEnd_5642710 : Nat := 321935824881302567208295

theorem tailTrace_5642710 : CollatzResearch.WordTrace tailWord_5642710 prefixEnd_5642710 321935824881302567208295 := by
  unfold tailWord_5642710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862908836714552686823849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137204360924955228659454389 12862908836714552686823849)
  ·
    refine ⟨9647181627535914515117887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12862908836714552686823849 9647181627535914515117887)
    ·
      refine ⟨14470772441303871772676831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647181627535914515117887 14470772441303871772676831)
      ·
        refine ⟨21706158661955807659015247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470772441303871772676831 21706158661955807659015247)
        ·
          refine ⟨32559237992933711488522871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21706158661955807659015247 32559237992933711488522871)
          ·
            refine ⟨48838856989400567232784307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32559237992933711488522871 48838856989400567232784307)
            ·
              refine ⟨73258285484100850849176461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48838856989400567232784307 73258285484100850849176461)
              ·
                refine ⟨27471857056537819068441173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73258285484100850849176461 27471857056537819068441173)
                ·
                  refine ⟨321935824881302567208295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27471857056537819068441173 321935824881302567208295)
                  ·
                    rfl

theorem cell23_5642710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5642710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642710 prefixEnd_5642710 := by exact prefixLift 5642710
  have htrace : WordTrace (prefixWord ++ tailWord_5642710) baseStart_5642710 baseEnd_5642710 := by
    simpa [prefixWord, tailWord_5642710, baseEnd_5642710] using wordTrace_append hprefix tailTrace_5642710
  have hstable : (prefixWord ++ tailWord_5642710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642710).length < 2 ^ (prefixWord ++ tailWord_5642710).sum := by decide
  have hdescent : baseEnd_5642710 < baseStart_5642710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642714 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_5642714 : Nat := 118140960795 + 5642714 * 2 ^ 59
def prefixEnd_5642714 : Nat := 4983230072969 + 3 ^ 40 * 5642714 * 2
def baseEnd_5642714 : Nat := 965808159284780363074879

theorem tailTrace_5642714 : CollatzResearch.WordTrace tailWord_5642714 prefixEnd_5642714 965808159284780363074879 := by
  unfold tailWord_5642714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51451671819854587918081799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137204458186278901114884797 51451671819854587918081799)
  ·
    refine ⟨77177507729781881877122699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51451671819854587918081799 77177507729781881877122699)
    ·
      refine ⟨115766261594672822815684049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77177507729781881877122699 115766261594672822815684049)
      ·
        refine ⟨86824696196004617111763037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115766261594672822815684049 86824696196004617111763037)
        ·
          refine ⟨32559261073501731416911139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86824696196004617111763037 32559261073501731416911139)
          ·
            refine ⟨48838891610252597125366709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32559261073501731416911139 48838891610252597125366709)
            ·
              refine ⟨4578646088461180980503129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48838891610252597125366709 4578646088461180980503129)
              ·
                refine ⟨3433984566345885735377347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578646088461180980503129 3433984566345885735377347)
                ·
                  refine ⟨5150976849518828603066021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433984566345885735377347 5150976849518828603066021)
                  ·
                    refine ⟨965808159284780363074879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150976849518828603066021 965808159284780363074879)
                    ·
                      rfl

theorem cell23_5642714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_5642714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642714 prefixEnd_5642714 := by exact prefixLift 5642714
  have htrace : WordTrace (prefixWord ++ tailWord_5642714) baseStart_5642714 baseEnd_5642714 := by
    simpa [prefixWord, tailWord_5642714, baseEnd_5642714] using wordTrace_append hprefix tailTrace_5642714
  have hstable : (prefixWord ++ tailWord_5642714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642714).length < 2 ^ (prefixWord ++ tailWord_5642714).sum := by decide
  have hdescent : baseEnd_5642714 < baseStart_5642714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642765 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5642765 : Nat := 118140960795 + 5642765 * 2 ^ 59
def prefixEnd_5642765 : Nat := 4983230072969 + 3 ^ 40 * 5642765 * 2
def baseEnd_5642765 : Nat := 965816888455906796562301

theorem tailTrace_5642765 : CollatzResearch.WordTrace tailWord_5642765 prefixEnd_5642765 965816888455906796562301 := by
  unfold tailWord_5642765
  simp only [CollatzResearch.WordTrace]
  refine ⟨205808547402233587382433749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137205698268155724921622499 205808547402233587382433749)
  ·
    refine ⟨4823637829739849704275791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 205808547402233587382433749 4823637829739849704275791)
    ·
      refine ⟨7235456744609774556413687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823637829739849704275791 7235456744609774556413687)
      ·
        refine ⟨10853185116914661834620531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7235456744609774556413687 10853185116914661834620531)
        ·
          refine ⟨16279777675371992751930797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853185116914661834620531 16279777675371992751930797)
          ·
            refine ⟨6104916628264497281974049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16279777675371992751930797 6104916628264497281974049)
            ·
              refine ⟨4578687471198372961480537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104916628264497281974049 4578687471198372961480537)
              ·
                refine ⟨3434015603398779721110403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578687471198372961480537 3434015603398779721110403)
                ·
                  refine ⟨5151023405098169581665605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434015603398779721110403 5151023405098169581665605)
                  ·
                    refine ⟨965816888455906796562301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151023405098169581665605 965816888455906796562301)
                    ·
                      rfl

theorem cell23_5642765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5642765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642765 prefixEnd_5642765 := by exact prefixLift 5642765
  have htrace : WordTrace (prefixWord ++ tailWord_5642765) baseStart_5642765 baseEnd_5642765 := by
    simpa [prefixWord, tailWord_5642765, baseEnd_5642765] using wordTrace_append hprefix tailTrace_5642765
  have hstable : (prefixWord ++ tailWord_5642765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642765).length < 2 ^ (prefixWord ++ tailWord_5642765).sum := by decide
  have hdescent : baseEnd_5642765 < baseStart_5642765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642787 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 2, 4]
def baseStart_5642787 : Nat := 118140960795 + 5642787 * 2 ^ 59
def prefixEnd_5642787 : Nat := 4983230072969 + 3 ^ 40 * 5642787 * 2
def baseEnd_5642787 : Nat := 965820653980706434537267

theorem tailTrace_5642787 : CollatzResearch.WordTrace tailWord_5642787 prefixEnd_5642787 965820653980706434537267 := by
  unfold tailWord_5642787
  simp only [CollatzResearch.WordTrace]
  refine ⟨205809349808153885139734615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137206233205435923426489743 205809349808153885139734615)
  ·
    refine ⟨308714024712230827709601923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205809349808153885139734615 308714024712230827709601923)
    ·
      refine ⟨463071037068346241564402885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308714024712230827709601923 463071037068346241564402885)
      ·
        refine ⟨86825819450314920293325541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463071037068346241564402885 86825819450314920293325541)
        ·
          refine ⟨16279841146934047554998539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86825819450314920293325541 16279841146934047554998539)
          ·
            refine ⟨24419761720401071332497809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16279841146934047554998539 24419761720401071332497809)
            ·
              refine ⟨18314821290300803499373357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24419761720401071332497809 18314821290300803499373357)
              ·
                refine ⟨6868057983862801312265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18314821290300803499373357 6868057983862801312265009)
                ·
                  refine ⟨5151043487897100984198757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868057983862801312265009 5151043487897100984198757)
                  ·
                    refine ⟨965820653980706434537267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151043487897100984198757 965820653980706434537267)
                    ·
                      rfl

theorem cell23_5642787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 4].length) (baseStart_5642787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642787 prefixEnd_5642787 := by exact prefixLift 5642787
  have htrace : WordTrace (prefixWord ++ tailWord_5642787) baseStart_5642787 baseEnd_5642787 := by
    simpa [prefixWord, tailWord_5642787, baseEnd_5642787] using wordTrace_append hprefix tailTrace_5642787
  have hstable : (prefixWord ++ tailWord_5642787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642787).length < 2 ^ (prefixWord ++ tailWord_5642787).sum := by decide
  have hdescent : baseEnd_5642787 < baseStart_5642787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642794 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5642794 : Nat := 118140960795 + 5642794 * 2 ^ 59
def prefixEnd_5642794 : Nat := 4983230072969 + 3 ^ 40 * 5642794 * 2
def baseEnd_5642794 : Nat := 2897465556306700776224269

theorem tailTrace_5642794 : CollatzResearch.WordTrace tailWord_5642794 prefixEnd_5642794 2897465556306700776224269 := by
  unfold tailWord_5642794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51452401279782131333809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137206403412752350223492957 51452401279782131333809859)
  ·
    refine ⟨77178601919673197000714789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51452401279782131333809859 77178601919673197000714789)
    ·
      refine ⟨14470987859938724437634023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77178601919673197000714789 14470987859938724437634023)
      ·
        refine ⟨21706481789908086656451035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470987859938724437634023 21706481789908086656451035)
        ·
          refine ⟨32559722684862129984676553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21706481789908086656451035 32559722684862129984676553)
          ·
            refine ⟨24419792013646597488507415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32559722684862129984676553 24419792013646597488507415)
            ·
              refine ⟨36629688020469896232761123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24419792013646597488507415 36629688020469896232761123)
              ·
                refine ⟨54944532030704844349141685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36629688020469896232761123 54944532030704844349141685)
                ·
                  refine ⟨5151049877878579157732033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54944532030704844349141685 5151049877878579157732033)
                  ·
                    refine ⟨3863287408408934368299025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5151049877878579157732033 3863287408408934368299025)
                    ·
                      refine ⟨2897465556306700776224269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863287408408934368299025 2897465556306700776224269)
                      ·
                        rfl

theorem cell23_5642794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5642794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642794 prefixEnd_5642794 := by exact prefixLift 5642794
  have htrace : WordTrace (prefixWord ++ tailWord_5642794) baseStart_5642794 baseEnd_5642794 := by
    simpa [prefixWord, tailWord_5642794, baseEnd_5642794] using wordTrace_append hprefix tailTrace_5642794
  have hstable : (prefixWord ++ tailWord_5642794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642794).length < 2 ^ (prefixWord ++ tailWord_5642794).sum := by decide
  have hdescent : baseEnd_5642794 < baseStart_5642794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642798 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_5642798 : Nat := 118140960795 + 5642798 * 2 ^ 59
def prefixEnd_5642798 : Nat := 4983230072969 + 3 ^ 40 * 5642798 * 2
def baseEnd_5642798 : Nat := 2897467610229318760574251

theorem tailTrace_5642798 : CollatzResearch.WordTrace tailWord_5642798 prefixEnd_5642798 2897467610229318760574251 := by
  unfold tailWord_5642798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25726218876389254252298131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137206500674076022678923365 25726218876389254252298131)
  ·
    refine ⟨38589328314583881378447197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25726218876389254252298131 38589328314583881378447197)
    ·
      refine ⟨14470998117968955516917699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38589328314583881378447197 14470998117968955516917699)
      ·
        refine ⟨21706497176953433275376549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470998117968955516917699 21706497176953433275376549)
        ·
          refine ⟨4069968220678768739133103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21706497176953433275376549 4069968220678768739133103)
          ·
            refine ⟨6104952331018153108699655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069968220678768739133103 6104952331018153108699655)
            ·
              refine ⟨9157428496527229663049483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104952331018153108699655 9157428496527229663049483)
              ·
                refine ⟨13736142744790844494574225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157428496527229663049483 13736142744790844494574225)
                ·
                  refine ⟨10302107058593133370930669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13736142744790844494574225 10302107058593133370930669)
                  ·
                    refine ⟨3863290146972425014099001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10302107058593133370930669 3863290146972425014099001)
                    ·
                      refine ⟨2897467610229318760574251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863290146972425014099001 2897467610229318760574251)
                      ·
                        rfl

theorem cell23_5642798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_5642798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642798 prefixEnd_5642798 := by exact prefixLift 5642798
  have htrace : WordTrace (prefixWord ++ tailWord_5642798) baseStart_5642798 baseEnd_5642798 := by
    simpa [prefixWord, tailWord_5642798, baseEnd_5642798] using wordTrace_append hprefix tailTrace_5642798
  have hstable : (prefixWord ++ tailWord_5642798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642798).length < 2 ^ (prefixWord ++ tailWord_5642798).sum := by decide
  have hdescent : baseEnd_5642798 < baseStart_5642798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642837 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5642837 : Nat := 118140960795 + 5642837 * 2 ^ 59
def prefixEnd_5642837 : Nat := 4983230072969 + 3 ^ 40 * 5642837 * 2
def baseEnd_5642837 : Nat := 2897487635974844107986571

theorem tailTrace_5642837 : CollatzResearch.WordTrace tailWord_5642837 prefixEnd_5642837 2897487635974844107986571 := by
  unfold tailWord_5642837
  simp only [CollatzResearch.WordTrace]
  refine ⟨205811173457972743679054765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137207448971981829119369843 205811173457972743679054765)
  ·
    refine ⟨77179190046739778879645537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205811173457972743679054765 77179190046739778879645537)
    ·
      refine ⟨57884392535054834159734153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77179190046739778879645537 57884392535054834159734153)
      ·
        refine ⟨43413294401291125619800615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57884392535054834159734153 43413294401291125619800615)
        ·
          refine ⟨65119941601936688429700923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43413294401291125619800615 65119941601936688429700923)
          ·
            refine ⟨97679912402905032644551385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65119941601936688429700923 97679912402905032644551385)
            ·
              refine ⟨73259934302178774483413539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97679912402905032644551385 73259934302178774483413539)
              ·
                refine ⟨109889901453268161725120309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73259934302178774483413539 109889901453268161725120309)
                ·
                  refine ⟨10302178261243890161730029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109889901453268161725120309 10302178261243890161730029)
                  ·
                    refine ⟨3863316847966458810648761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10302178261243890161730029 3863316847966458810648761)
                    ·
                      refine ⟨2897487635974844107986571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863316847966458810648761 2897487635974844107986571)
                      ·
                        rfl

theorem cell23_5642837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5642837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642837 prefixEnd_5642837 := by exact prefixLift 5642837
  have htrace : WordTrace (prefixWord ++ tailWord_5642837) baseStart_5642837 baseEnd_5642837 := by
    simpa [prefixWord, tailWord_5642837, baseEnd_5642837] using wordTrace_append hprefix tailTrace_5642837
  have hstable : (prefixWord ++ tailWord_5642837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642837).length < 2 ^ (prefixWord ++ tailWord_5642837).sum := by decide
  have hdescent : baseEnd_5642837 < baseStart_5642837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642941 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 5]
def baseStart_5642941 : Nat := 118140960795 + 5642941 * 2 ^ 59
def prefixEnd_5642941 : Nat := 4983230072969 + 3 ^ 40 * 5642941 * 2
def baseEnd_5642941 : Nat := 321949004218101300120677

theorem tailTrace_5642941 : CollatzResearch.WordTrace tailWord_5642941 prefixEnd_5642941 321949004218101300120677 := by
  unfold tailWord_5642941
  simp only [CollatzResearch.WordTrace]
  refine ⟨205814966649595969440840677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137209977766397312960560451 205814966649595969440840677)
  ·
    refine ⟨38590306246799244270157627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205814966649595969440840677 38590306246799244270157627)
    ·
      refine ⟨57885459370198866405236441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38590306246799244270157627 57885459370198866405236441)
      ·
        refine ⟨43414094527649149803927331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57885459370198866405236441 43414094527649149803927331)
        ·
          refine ⟨65121141791473724705890997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43414094527649149803927331 65121141791473724705890997)
          ·
            refine ⟨6105107042950661691177281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65121141791473724705890997 6105107042950661691177281)
            ·
              refine ⟨4578830282212996268382961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6105107042950661691177281 4578830282212996268382961)
              ·
                refine ⟨3434122711659747201287221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578830282212996268382961 3434122711659747201287221)
                ·
                  refine ⟨321949004218101300120677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3434122711659747201287221 321949004218101300120677)
                  ·
                    rfl

theorem cell23_5642941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_5642941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642941 prefixEnd_5642941 := by exact prefixLift 5642941
  have htrace : WordTrace (prefixWord ++ tailWord_5642941) baseStart_5642941 baseEnd_5642941 := by
    simpa [prefixWord, tailWord_5642941, baseEnd_5642941] using wordTrace_append hprefix tailTrace_5642941
  have hstable : (prefixWord ++ tailWord_5642941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642941).length < 2 ^ (prefixWord ++ tailWord_5642941).sum := by decide
  have hdescent : baseEnd_5642941 < baseStart_5642941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5642967 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 5, 4]
def baseStart_5642967 : Nat := 118140960795 + 5642967 * 2 ^ 59
def prefixEnd_5642967 : Nat := 4983230072969 + 3 ^ 40 * 5642967 * 2
def baseEnd_5642967 : Nat := 965851462819976199786991

theorem tailTrace_5642967 : CollatzResearch.WordTrace tailWord_5642967 prefixEnd_5642967 965851462819976199786991 := by
  unfold tailWord_5642967
  simp only [CollatzResearch.WordTrace]
  refine ⟨205815914947501775881287155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137210609965001183920858103 205815914947501775881287155)
  ·
    refine ⟨308723872421252663821930733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205815914947501775881287155 308723872421252663821930733)
    ·
      refine ⟨115771452157969748933224025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308723872421252663821930733 115771452157969748933224025)
      ·
        refine ⟨86828589118477311699918019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115771452157969748933224025 86828589118477311699918019)
        ·
          refine ⟨130242883677715967549877029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86828589118477311699918019 130242883677715967549877029)
          ·
            refine ⟨24420540689571743915601943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130242883677715967549877029 24420540689571743915601943)
            ·
              refine ⟨36630811034357615873402915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24420540689571743915601943 36630811034357615873402915)
              ·
                refine ⟨54946216551536423810104373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36630811034357615873402915 54946216551536423810104373)
                ·
                  refine ⟨5151207801706539732197285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54946216551536423810104373 5151207801706539732197285)
                  ·
                    refine ⟨965851462819976199786991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151207801706539732197285 965851462819976199786991)
                    ·
                      rfl

theorem cell23_5642967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_5642967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5642967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5642967 prefixEnd_5642967 := by exact prefixLift 5642967
  have htrace : WordTrace (prefixWord ++ tailWord_5642967) baseStart_5642967 baseEnd_5642967 := by
    simpa [prefixWord, tailWord_5642967, baseEnd_5642967] using wordTrace_append hprefix tailTrace_5642967
  have hstable : (prefixWord ++ tailWord_5642967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5642967).length < 2 ^ (prefixWord ++ tailWord_5642967).sum := by decide
  have hdescent : baseEnd_5642967 < baseStart_5642967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5642967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643000 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_5643000 : Nat := 118140960795 + 5643000 * 2 ^ 59
def prefixEnd_5643000 : Nat := 4983230072969 + 3 ^ 40 * 5643000 * 2
def baseEnd_5643000 : Nat := 2897571333321526970248321

theorem tailTrace_5643000 : CollatzResearch.WordTrace tailWord_5643000 prefixEnd_5643000 2897571333321526970248321 := by
  unfold tailWord_5643000
  simp only [CollatzResearch.WordTrace]
  refine ⟨102908559278191111258619227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137211412370921481678158969 102908559278191111258619227)
  ·
    refine ⟨154362838917286666887928841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102908559278191111258619227 154362838917286666887928841)
    ·
      refine ⟨115772129187965000165946631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154362838917286666887928841 115772129187965000165946631)
      ·
        refine ⟨173658193781947500248919947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115772129187965000165946631 173658193781947500248919947)
        ·
          refine ⟨260487290672921250373379921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173658193781947500248919947 260487290672921250373379921)
          ·
            refine ⟨195365468004690937780034941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260487290672921250373379921 195365468004690937780034941)
            ·
              refine ⟨73262050501759101667513103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195365468004690937780034941 73262050501759101667513103)
              ·
                refine ⟨109893075752638652501269655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73262050501759101667513103 109893075752638652501269655)
                ·
                  refine ⟨164839613628957978751904483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109893075752638652501269655 164839613628957978751904483)
                  ·
                    refine ⟨247259420443436968127856725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164839613628957978751904483 247259420443436968127856725)
                    ·
                      refine ⟨2897571333321526970248321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 247259420443436968127856725 2897571333321526970248321)
                      ·
                        rfl

theorem cell23_5643000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_5643000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643000 prefixEnd_5643000 := by exact prefixLift 5643000
  have htrace : WordTrace (prefixWord ++ tailWord_5643000) baseStart_5643000 baseEnd_5643000 := by
    simpa [prefixWord, tailWord_5643000, baseEnd_5643000] using wordTrace_append hprefix tailTrace_5643000
  have hstable : (prefixWord ++ tailWord_5643000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643000).length < 2 ^ (prefixWord ++ tailWord_5643000).sum := by decide
  have hdescent : baseEnd_5643000 < baseStart_5643000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643034 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2]
def baseStart_5643034 : Nat := 118140960795 + 5643034 * 2 ^ 59
def prefixEnd_5643034 : Nat := 4983230072969 + 3 ^ 40 * 5643034 * 2
def baseEnd_5643034 : Nat := 2897588791663779837223165

theorem tailTrace_5643034 : CollatzResearch.WordTrace tailWord_5643034 prefixEnd_5643034 2897588791663779837223165 := by
  unfold tailWord_5643034
  simp only [CollatzResearch.WordTrace]
  refine ⟨51454589659564761580994039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137212239092172697549317437 51454589659564761580994039)
  ·
    refine ⟨77181884489347142371491059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51454589659564761580994039 77181884489347142371491059)
    ·
      refine ⟨115772826734020713557236589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77181884489347142371491059 115772826734020713557236589)
      ·
        refine ⟨43414810025257767583963721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115772826734020713557236589 43414810025257767583963721)
        ·
          refine ⟨32561107518943325687972791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43414810025257767583963721 32561107518943325687972791)
          ·
            refine ⟨48841661278414988531959187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32561107518943325687972791 48841661278414988531959187)
            ·
              refine ⟨73262491917622482797938781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48841661278414988531959187 73262491917622482797938781)
              ·
                refine ⟨27473434469108431049227043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73262491917622482797938781 27473434469108431049227043)
                ·
                  refine ⟨41210151703662646573840565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27473434469108431049227043 41210151703662646573840565)
                  ·
                    refine ⟨3863451722218373116297553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41210151703662646573840565 3863451722218373116297553)
                    ·
                      refine ⟨2897588791663779837223165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863451722218373116297553 2897588791663779837223165)
                      ·
                        rfl

theorem cell23_5643034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_5643034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643034 prefixEnd_5643034 := by exact prefixLift 5643034
  have htrace : WordTrace (prefixWord ++ tailWord_5643034) baseStart_5643034 baseEnd_5643034 := by
    simpa [prefixWord, tailWord_5643034, baseEnd_5643034] using wordTrace_append hprefix tailTrace_5643034
  have hstable : (prefixWord ++ tailWord_5643034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643034).length < 2 ^ (prefixWord ++ tailWord_5643034).sum := by decide
  have hdescent : baseEnd_5643034 < baseStart_5643034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643078 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_5643078 : Nat := 118140960795 + 5643078 * 2 ^ 59
def prefixEnd_5643078 : Nat := 4983230072969 + 3 ^ 40 * 5643078 * 2
def baseEnd_5643078 : Nat := 965870461604192555024321

theorem tailTrace_5643078 : CollatzResearch.WordTrace tailWord_5643078 prefixEnd_5643078 965870461604192555024321 := by
  unfold tailWord_5643078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431873857815613807455559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137213308966733094559051925 6431873857815613807455559)
  ·
    refine ⟨9647810786723420711183339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6431873857815613807455559 9647810786723420711183339)
    ·
      refine ⟨14471716180085131066775009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647810786723420711183339 14471716180085131066775009)
      ·
        refine ⟨10853787135063848300081257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14471716180085131066775009 10853787135063848300081257)
        ·
          refine ⟨8140340351297886225060943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10853787135063848300081257 8140340351297886225060943)
          ·
            refine ⟨12210510526946829337591415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140340351297886225060943 12210510526946829337591415)
            ·
              refine ⟨18315765790420244006387123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12210510526946829337591415 18315765790420244006387123)
              ·
                refine ⟨27473648685630366009580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18315765790420244006387123 27473648685630366009580685)
                ·
                  refine ⟨10302618257111387253592757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27473648685630366009580685 10302618257111387253592757)
                  ·
                    refine ⟨965870461604192555024321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10302618257111387253592757 965870461604192555024321)
                    ·
                      rfl

theorem cell23_5643078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_5643078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643078 prefixEnd_5643078 := by exact prefixLift 5643078
  have htrace : WordTrace (prefixWord ++ tailWord_5643078) baseStart_5643078 baseEnd_5643078 := by
    simpa [prefixWord, tailWord_5643078, baseEnd_5643078] using wordTrace_append hprefix tailTrace_5643078
  have hstable : (prefixWord ++ tailWord_5643078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643078).length < 2 ^ (prefixWord ++ tailWord_5643078).sum := by decide
  have hdescent : baseEnd_5643078 < baseStart_5643078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643081 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_5643081 : Nat := 118140960795 + 5643081 * 2 ^ 59
def prefixEnd_5643081 : Nat := 4983230072969 + 3 ^ 40 * 5643081 * 2
def baseEnd_5643081 : Nat := 2897612925254541153335449

theorem tailTrace_5643081 : CollatzResearch.WordTrace tailWord_5643081 prefixEnd_5643081 2897612925254541153335449 := by
  unfold tailWord_5643081
  simp only [CollatzResearch.WordTrace]
  refine ⟨205820072869088773350937097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137213381912725848900624731 205820072869088773350937097)
  ·
    refine ⟨154365054651816580013202823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205820072869088773350937097 154365054651816580013202823)
    ·
      refine ⟨231547581977724870019804235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154365054651816580013202823 231547581977724870019804235)
      ·
        refine ⟨347321372966587305029706353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231547581977724870019804235 347321372966587305029706353)
        ·
          refine ⟨260491029724940478772279765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347321372966587305029706353 260491029724940478772279765)
          ·
            refine ⟨6105258509178292471225307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 260491029724940478772279765 6105258509178292471225307)
            ·
              refine ⟨9157887763767438706837961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105258509178292471225307 9157887763767438706837961)
              ·
                refine ⟨6868415822825579030128471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9157887763767438706837961 6868415822825579030128471)
                ·
                  refine ⟨10302623734238368545192707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868415822825579030128471 10302623734238368545192707)
                  ·
                    refine ⟨15453935601357552817789061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10302623734238368545192707 15453935601357552817789061)
                    ·
                      refine ⟨2897612925254541153335449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15453935601357552817789061 2897612925254541153335449)
                      ·
                        rfl

theorem cell23_5643081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_5643081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643081 prefixEnd_5643081 := by exact prefixLift 5643081
  have htrace : WordTrace (prefixWord ++ tailWord_5643081) baseStart_5643081 baseEnd_5643081 := by
    simpa [prefixWord, tailWord_5643081, baseEnd_5643081] using wordTrace_append hprefix tailTrace_5643081
  have hstable : (prefixWord ++ tailWord_5643081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643081).length < 2 ^ (prefixWord ++ tailWord_5643081).sum := by decide
  have hdescent : baseEnd_5643081 < baseStart_5643081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643085 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5643085 : Nat := 118140960795 + 5643085 * 2 ^ 59
def prefixEnd_5643085 : Nat := 4983230072969 + 3 ^ 40 * 5643085 * 2
def baseEnd_5643085 : Nat := 2897614979177159137685431

theorem tailTrace_5643085 : CollatzResearch.WordTrace tailWord_5643085 prefixEnd_5643085 2897614979177159137685431 := by
  unfold tailWord_5643085
  simp only [CollatzResearch.WordTrace]
  refine ⟨205820218761074282034082709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137213479174049521356055139 205820218761074282034082709)
  ·
    refine ⟨9647822754425356970347627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205820218761074282034082709 9647822754425356970347627)
    ·
      refine ⟨14471734131638035455521441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647822754425356970347627 14471734131638035455521441)
      ·
        refine ⟨10853800598728526591641081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14471734131638035455521441 10853800598728526591641081)
        ·
          refine ⟨8140350449046394943730811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10853800598728526591641081 8140350449046394943730811)
          ·
            refine ⟨12210525673569592415596217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140350449046394943730811 12210525673569592415596217)
            ·
              refine ⟨9157894255177194311697163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12210525673569592415596217 9157894255177194311697163)
              ·
                refine ⟨13736841382765791467545745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157894255177194311697163 13736841382765791467545745)
                ·
                  refine ⟨10302631037074343600659309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13736841382765791467545745 10302631037074343600659309)
                  ·
                    refine ⟨3863486638902878850247241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10302631037074343600659309 3863486638902878850247241)
                    ·
                      refine ⟨2897614979177159137685431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863486638902878850247241 2897614979177159137685431)
                      ·
                        rfl

theorem cell23_5643085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5643085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643085 prefixEnd_5643085 := by exact prefixLift 5643085
  have htrace : WordTrace (prefixWord ++ tailWord_5643085) baseStart_5643085 baseEnd_5643085 := by
    simpa [prefixWord, tailWord_5643085, baseEnd_5643085] using wordTrace_append hprefix tailTrace_5643085
  have hstable : (prefixWord ++ tailWord_5643085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643085).length < 2 ^ (prefixWord ++ tailWord_5643085).sum := by decide
  have hdescent : baseEnd_5643085 < baseStart_5643085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643115 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 1, 2, 2]
def baseStart_5643115 : Nat := 118140960795 + 5643115 * 2 ^ 59
def prefixEnd_5643115 : Nat := 4983230072969 + 3 ^ 40 * 5643115 * 2
def baseEnd_5643115 : Nat := 2897630383596794020310293

theorem tailTrace_5643115 : CollatzResearch.WordTrace tailWord_5643115 prefixEnd_5643115 2897630383596794020310293 := by
  unfold tailWord_5643115
  simp only [CollatzResearch.WordTrace]
  refine ⟨205821312950965597157674799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137214208633977064771783199 205821312950965597157674799)
  ·
    refine ⟨308731969426448395736512199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205821312950965597157674799 308731969426448395736512199)
    ·
      refine ⟨463097954139672593604768299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308731969426448395736512199 463097954139672593604768299)
      ·
        refine ⟨694646931209508890407152449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463097954139672593604768299 694646931209508890407152449)
        ·
          refine ⟨520985198407131667805364337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694646931209508890407152449 520985198407131667805364337)
          ·
            refine ⟨390738898805348750854023253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520985198407131667805364337 390738898805348750854023253)
            ·
              refine ⟨4578971470375180674070585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 390738898805348750854023253 4578971470375180674070585)
              ·
                refine ⟨3434228602781385505552939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578971470375180674070585 3434228602781385505552939)
                ·
                  refine ⟨5151342904172078258329409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434228602781385505552939 5151342904172078258329409)
                  ·
                    refine ⟨3863507178129058693747057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5151342904172078258329409 3863507178129058693747057)
                    ·
                      refine ⟨2897630383596794020310293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863507178129058693747057 2897630383596794020310293)
                      ·
                        rfl

theorem cell23_5643115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 1, 2, 2].length) (baseStart_5643115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643115 prefixEnd_5643115 := by exact prefixLift 5643115
  have htrace : WordTrace (prefixWord ++ tailWord_5643115) baseStart_5643115 baseEnd_5643115 := by
    simpa [prefixWord, tailWord_5643115, baseEnd_5643115] using wordTrace_append hprefix tailTrace_5643115
  have hstable : (prefixWord ++ tailWord_5643115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643115).length < 2 ^ (prefixWord ++ tailWord_5643115).sum := by decide
  have hdescent : baseEnd_5643115 < baseStart_5643115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643131 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 3]
def baseStart_5643131 : Nat := 118140960795 + 5643131 * 2 ^ 59
def prefixEnd_5643131 : Nat := 4983230072969 + 3 ^ 40 * 5643131 * 2
def baseEnd_5643131 : Nat := 2897638599287265957710219

theorem tailTrace_5643131 : CollatzResearch.WordTrace tailWord_5643131 prefixEnd_5643131 2897638599287265957710219 := by
  unfold tailWord_5643131
  simp only [CollatzResearch.WordTrace]
  refine ⟨205821896518907631890257247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137214597679271754593504831 205821896518907631890257247)
  ·
    refine ⟨308732844778361447835385871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205821896518907631890257247 308732844778361447835385871)
    ·
      refine ⟨463099267167542171753078807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308732844778361447835385871 463099267167542171753078807)
      ·
        refine ⟨694648900751313257629618211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463099267167542171753078807 694648900751313257629618211)
        ·
          refine ⟨1041973351126969886444427317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694648900751313257629618211 1041973351126969886444427317)
          ·
            refine ⟨97685001668153426854165061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1041973351126969886444427317 97685001668153426854165061)
            ·
              refine ⟨18315937812778767535155949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97685001668153426854165061 18315937812778767535155949)
              ·
                refine ⟨6868476679792037825683481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18315937812778767535155949 6868476679792037825683481)
                ·
                  refine ⟨5151357509844028369262611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868476679792037825683481 5151357509844028369262611)
                  ·
                    refine ⟨7727036264766042553893917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151357509844028369262611 7727036264766042553893917)
                    ·
                      refine ⟨2897638599287265957710219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727036264766042553893917 2897638599287265957710219)
                      ·
                        rfl

theorem cell23_5643131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 3].length) (baseStart_5643131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643131 prefixEnd_5643131 := by exact prefixLift 5643131
  have htrace : WordTrace (prefixWord ++ tailWord_5643131) baseStart_5643131 baseEnd_5643131 := by
    simpa [prefixWord, tailWord_5643131, baseEnd_5643131] using wordTrace_append hprefix tailTrace_5643131
  have hstable : (prefixWord ++ tailWord_5643131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643131).length < 2 ^ (prefixWord ++ tailWord_5643131).sum := by decide
  have hdescent : baseEnd_5643131 < baseStart_5643131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643141 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_5643141 : Nat := 118140960795 + 5643141 * 2 ^ 59
def prefixEnd_5643141 : Nat := 4983230072969 + 3 ^ 40 * 5643141 * 2
def baseEnd_5643141 : Nat := 2897643734093810918585173

theorem tailTrace_5643141 : CollatzResearch.WordTrace tailWord_5643141 prefixEnd_5643141 2897643734093810918585173 := by
  unfold tailWord_5643141
  simp only [CollatzResearch.WordTrace]
  refine ⟨205822261248871403598121277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137214840832580935732080851 205822261248871403598121277)
  ·
    refine ⟨77183347968326776349295479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205822261248871403598121277 77183347968326776349295479)
    ·
      refine ⟨115775021952490164523943219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77183347968326776349295479 115775021952490164523943219)
      ·
        refine ⟨173662532928735246785914829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115775021952490164523943219 173662532928735246785914829)
        ·
          refine ⟨65123449848275717544718061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173662532928735246785914829 65123449848275717544718061)
          ·
            refine ⟨24421293693103394079269273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65123449848275717544718061 24421293693103394079269273)
            ·
              refine ⟨18315970269827545559451955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24421293693103394079269273 18315970269827545559451955)
              ·
                refine ⟨27473955404741318339177933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18315970269827545559451955 27473955404741318339177933)
                ·
                  refine ⟨10302733276777994377191725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27473955404741318339177933 10302733276777994377191725)
                  ·
                    refine ⟨3863524978791747891446897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10302733276777994377191725 3863524978791747891446897)
                    ·
                      refine ⟨2897643734093810918585173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863524978791747891446897 2897643734093810918585173)
                      ·
                        rfl

theorem cell23_5643141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_5643141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643141 prefixEnd_5643141 := by exact prefixLift 5643141
  have htrace : WordTrace (prefixWord ++ tailWord_5643141) baseStart_5643141 baseEnd_5643141 := by
    simpa [prefixWord, tailWord_5643141, baseEnd_5643141] using wordTrace_append hprefix tailTrace_5643141
  have hstable : (prefixWord ++ tailWord_5643141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643141).length < 2 ^ (prefixWord ++ tailWord_5643141).sum := by decide
  have hdescent : baseEnd_5643141 < baseStart_5643141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643211 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 5]
def baseStart_5643211 : Nat := 118140960795 + 5643211 * 2 ^ 59
def prefixEnd_5643211 : Nat := 4983230072969 + 3 ^ 40 * 5643211 * 2
def baseEnd_5643211 : Nat := 321964408637736182745539

theorem tailTrace_5643211 : CollatzResearch.WordTrace tailWord_5643211 prefixEnd_5643211 321964408637736182745539 := by
  unfold tailWord_5643211
  simp only [CollatzResearch.WordTrace]
  refine ⟨205824814358617805553169487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137216542905745203702112991 205824814358617805553169487)
  ·
    refine ⟨308737221537926708329754231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205824814358617805553169487 308737221537926708329754231)
    ·
      refine ⟨463105832306890062494631347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308737221537926708329754231 463105832306890062494631347)
      ·
        refine ⟨694658748460335093741947021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463105832306890062494631347 694658748460335093741947021)
        ·
          refine ⟨260497030672625660153230133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 694658748460335093741947021 260497030672625660153230133)
          ·
            refine ⟨24421596625558655639365325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260497030672625660153230133 24421596625558655639365325)
            ·
              refine ⟨9158098734584495864761997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24421596625558655639365325 9158098734584495864761997)
              ·
                refine ⟨3434287025469185949285749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9158098734584495864761997 3434287025469185949285749)
                ·
                  refine ⟨321964408637736182745539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3434287025469185949285749 321964408637736182745539)
                  ·
                    rfl

theorem cell23_5643211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 5].length) (baseStart_5643211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643211 prefixEnd_5643211 := by exact prefixLift 5643211
  have htrace : WordTrace (prefixWord ++ tailWord_5643211) baseStart_5643211 baseEnd_5643211 := by
    simpa [prefixWord, tailWord_5643211, baseEnd_5643211] using wordTrace_append hprefix tailTrace_5643211
  have hstable : (prefixWord ++ tailWord_5643211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643211).length < 2 ^ (prefixWord ++ tailWord_5643211).sum := by decide
  have hdescent : baseEnd_5643211 < baseStart_5643211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643224 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 4, 5]
def baseStart_5643224 : Nat := 118140960795 + 5643224 * 2 ^ 59
def prefixEnd_5643224 : Nat := 4983230072969 + 3 ^ 40 * 5643224 * 2
def baseEnd_5643224 : Nat := 965895450996044697949097

theorem tailTrace_5643224 : CollatzResearch.WordTrace tailWord_5643224 prefixEnd_5643224 965895450996044697949097 := by
  unfold tailWord_5643224
  simp only [CollatzResearch.WordTrace]
  refine ⟨102912644253785354386696363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137216859005047139182261817 102912644253785354386696363)
  ·
    refine ⟨154368966380678031580044545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102912644253785354386696363 154368966380678031580044545)
    ·
      refine ⟨115776724785508523685033409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154368966380678031580044545 115776724785508523685033409)
      ·
        refine ⟨86832543589131392763775057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115776724785508523685033409 86832543589131392763775057)
        ·
          refine ⟨65124407691848544572831293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86832543589131392763775057 65124407691848544572831293)
          ·
            refine ⟨24421652884443204214811735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65124407691848544572831293 24421652884443204214811735)
            ·
              refine ⟨36632479326664806322217603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24421652884443204214811735 36632479326664806322217603)
              ·
                refine ⟨54948718989997209483326405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36632479326664806322217603 54948718989997209483326405)
                ·
                  refine ⟨10302884810624476778123701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54948718989997209483326405 10302884810624476778123701)
                  ·
                    refine ⟨965895450996044697949097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10302884810624476778123701 965895450996044697949097)
                    ·
                      rfl

theorem cell23_5643224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_5643224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643224 prefixEnd_5643224 := by exact prefixLift 5643224
  have htrace : WordTrace (prefixWord ++ tailWord_5643224) baseStart_5643224 baseEnd_5643224 := by
    simpa [prefixWord, tailWord_5643224, baseEnd_5643224] using wordTrace_append hprefix tailTrace_5643224
  have hstable : (prefixWord ++ tailWord_5643224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643224).length < 2 ^ (prefixWord ++ tailWord_5643224).sum := by decide
  have hdescent : baseEnd_5643224 < baseStart_5643224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_5643261 : Nat := 118140960795 + 5643261 * 2 ^ 59
def prefixEnd_5643261 : Nat := 4983230072969 + 3 ^ 40 * 5643261 * 2
def baseEnd_5643261 : Nat := 2897705351772350449084621

theorem tailTrace_5643261 : CollatzResearch.WordTrace tailWord_5643261 prefixEnd_5643261 2897705351772350449084621 := by
  unfold tailWord_5643261
  simp only [CollatzResearch.WordTrace]
  refine ⟨205826638008436664092489637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137217758672291109394993091 205826638008436664092489637)
  ·
    refine ⟨38592494626581874517341807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205826638008436664092489637 38592494626581874517341807)
    ·
      refine ⟨57888741939872811776012711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38592494626581874517341807 57888741939872811776012711)
      ·
        refine ⟨86833112909809217664019067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57888741939872811776012711 86833112909809217664019067)
        ·
          refine ⟨130249669364713826496028601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86833112909809217664019067 130249669364713826496028601)
          ·
            refine ⟨97687252023535369872021451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130249669364713826496028601 97687252023535369872021451)
            ·
              refine ⟨146530878035303054808032177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97687252023535369872021451 146530878035303054808032177)
              ·
                refine ⟨109898158526477291106024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146530878035303054808032177 109898158526477291106024133)
                ·
                  refine ⟨20605904723714492082379525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109898158526477291106024133 20605904723714492082379525)
                  ·
                    refine ⟨3863607135696467265446161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20605904723714492082379525 3863607135696467265446161)
                    ·
                      refine ⟨2897705351772350449084621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863607135696467265446161 2897705351772350449084621)
                      ·
                        rfl

theorem cell23_5643261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_5643261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643261 prefixEnd_5643261 := by exact prefixLift 5643261
  have htrace : WordTrace (prefixWord ++ tailWord_5643261) baseStart_5643261 baseEnd_5643261 := by
    simpa [prefixWord, tailWord_5643261, baseEnd_5643261] using wordTrace_append hprefix tailTrace_5643261
  have hstable : (prefixWord ++ tailWord_5643261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643261).length < 2 ^ (prefixWord ++ tailWord_5643261).sum := by decide
  have hdescent : baseEnd_5643261 < baseStart_5643261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643264 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3]
def baseStart_5643264 : Nat := 118140960795 + 5643264 * 2 ^ 59
def prefixEnd_5643264 : Nat := 4983230072969 + 3 ^ 40 * 5643264 * 2
def baseEnd_5643264 : Nat := 2897706892214313937347107

theorem tailTrace_5643264 : CollatzResearch.WordTrace tailWord_5643264 prefixEnd_5643264 2897706892214313937347107 := by
  unfold tailWord_5643264
  simp only [CollatzResearch.WordTrace]
  refine ⟨102913373713712897802424423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137217831618283863736565897 102913373713712897802424423)
  ·
    refine ⟨154370060570569346703636635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102913373713712897802424423 154370060570569346703636635)
    ·
      refine ⟨231555090855854020055454953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154370060570569346703636635 231555090855854020055454953)
      ·
        refine ⟨173666318141890515041591215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231555090855854020055454953 173666318141890515041591215)
        ·
          refine ⟨260499477212835772562386823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173666318141890515041591215 260499477212835772562386823)
          ·
            refine ⟨390749215819253658843580235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260499477212835772562386823 390749215819253658843580235)
            ·
              refine ⟨586123823728880488265370353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390749215819253658843580235 586123823728880488265370353)
              ·
                refine ⟨439592867796660366199027765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586123823728880488265370353 439592867796660366199027765)
                ·
                  refine ⟨41211831355936909331158853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 439592867796660366199027765 41211831355936909331158853)
                  ·
                    refine ⟨7727218379238170499592285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41211831355936909331158853 7727218379238170499592285)
                    ·
                      refine ⟨2897706892214313937347107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727218379238170499592285 2897706892214313937347107)
                      ·
                        rfl

theorem cell23_5643264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_5643264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643264 prefixEnd_5643264 := by exact prefixLift 5643264
  have htrace : WordTrace (prefixWord ++ tailWord_5643264) baseStart_5643264 baseEnd_5643264 := by
    simpa [prefixWord, tailWord_5643264, baseEnd_5643264] using wordTrace_append hprefix tailTrace_5643264
  have hstable : (prefixWord ++ tailWord_5643264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643264).length < 2 ^ (prefixWord ++ tailWord_5643264).sum := by decide
  have hdescent : baseEnd_5643264 < baseStart_5643264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643331 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 1, 5]
def baseStart_5643331 : Nat := 118140960795 + 5643331 * 2 ^ 59
def prefixEnd_5643331 : Nat := 4983230072969 + 3 ^ 40 * 5643331 * 2
def baseEnd_5643331 : Nat := 965913765139388391736433

theorem tailTrace_5643331 : CollatzResearch.WordTrace tailWord_5643331 prefixEnd_5643331 965913765139388391736433 := by
  unfold tailWord_5643331
  simp only [CollatzResearch.WordTrace]
  refine ⟨205829191118183066047537847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137219460745455377365025231 205829191118183066047537847)
  ·
    refine ⟨308743786677274599071306771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205829191118183066047537847 308743786677274599071306771)
    ·
      refine ⟨463115680015911898606960157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308743786677274599071306771 463115680015911898606960157)
      ·
        refine ⟨173668380005966961977610059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463115680015911898606960157 173668380005966961977610059)
        ·
          refine ⟨260502570008950442966415089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173668380005966961977610059 260502570008950442966415089)
          ·
            refine ⟨195376927506712832224811317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260502570008950442966415089 195376927506712832224811317)
            ·
              refine ⟨18316586953754328021076061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195376927506712832224811317 18316586953754328021076061)
              ·
                refine ⟨6868720107657873007903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18316586953754328021076061 6868720107657873007903523)
                ·
                  refine ⟨10303080161486809511855285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868720107657873007903523 10303080161486809511855285)
                  ·
                    refine ⟨965913765139388391736433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10303080161486809511855285 965913765139388391736433)
                    ·
                      rfl

theorem cell23_5643331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 5].length) (baseStart_5643331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643331 prefixEnd_5643331 := by exact prefixLift 5643331
  have htrace : WordTrace (prefixWord ++ tailWord_5643331) baseStart_5643331 baseEnd_5643331 := by
    simpa [prefixWord, tailWord_5643331, baseEnd_5643331] using wordTrace_append hprefix tailTrace_5643331
  have hstable : (prefixWord ++ tailWord_5643331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643331).length < 2 ^ (prefixWord ++ tailWord_5643331).sum := by decide
  have hdescent : baseEnd_5643331 < baseStart_5643331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643338 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2]
def baseStart_5643338 : Nat := 118140960795 + 5643338 * 2 ^ 59
def prefixEnd_5643338 : Nat := 4983230072969 + 3 ^ 40 * 5643338 * 2
def baseEnd_5643338 : Nat := 2897744889782746647821767

theorem tailTrace_5643338 : CollatzResearch.WordTrace tailWord_5643338 prefixEnd_5643338 2897744889782746647821767 := by
  unfold tailWord_5643338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51457361607289426560760667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137219630952771804162028445 51457361607289426560760667)
  ·
    refine ⟨77186042410934139841141001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51457361607289426560760667 77186042410934139841141001)
    ·
      refine ⟨57889531808200604880855751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77186042410934139841141001 57889531808200604880855751)
      ·
        refine ⟨86834297712300907321283627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57889531808200604880855751 86834297712300907321283627)
        ·
          refine ⟨130251446568451360981925441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86834297712300907321283627 130251446568451360981925441)
          ·
            refine ⟨97688584926338520736444081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130251446568451360981925441 97688584926338520736444081)
            ·
              refine ⟨73266438694753890552333061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97688584926338520736444081 73266438694753890552333061)
              ·
                refine ⟨13737457255266354478562449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73266438694753890552333061 13737457255266354478562449)
                ·
                  refine ⟨10303092941449765858921837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13737457255266354478562449 10303092941449765858921837)
                  ·
                    refine ⟨3863659853043662197095689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10303092941449765858921837 3863659853043662197095689)
                    ·
                      refine ⟨2897744889782746647821767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863659853043662197095689 2897744889782746647821767)
                      ·
                        rfl

theorem cell23_5643338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_5643338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643338 prefixEnd_5643338 := by exact prefixLift 5643338
  have htrace : WordTrace (prefixWord ++ tailWord_5643338) baseStart_5643338 baseEnd_5643338 := by
    simpa [prefixWord, tailWord_5643338, baseEnd_5643338] using wordTrace_append hprefix tailTrace_5643338
  have hstable : (prefixWord ++ tailWord_5643338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643338).length < 2 ^ (prefixWord ++ tailWord_5643338).sum := by decide
  have hdescent : baseEnd_5643338 < baseStart_5643338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643344 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 6]
def baseStart_5643344 : Nat := 118140960795 + 5643344 * 2 ^ 59
def prefixEnd_5643344 : Nat := 4983230072969 + 3 ^ 40 * 5643344 * 2
def baseEnd_5643344 : Nat := 965915990222224541448913

theorem tailTrace_5643344 : CollatzResearch.WordTrace tailWord_5643344 prefixEnd_5643344 965915990222224541448913 := by
  unfold tailWord_5643344
  simp only [CollatzResearch.WordTrace]
  refine ⟨102914832633567984633880543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137219776844757312845174057 102914832633567984633880543)
  ·
    refine ⟨154372248950351976950820815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102914832633567984633880543 154372248950351976950820815)
    ·
      refine ⟨231558373425527965426231223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154372248950351976950820815 231558373425527965426231223)
      ·
        refine ⟨347337560138291948139346835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231558373425527965426231223 347337560138291948139346835)
        ·
          refine ⟨521006340207437922209020253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347337560138291948139346835 521006340207437922209020253)
          ·
            refine ⟨195377377577789220828382595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521006340207437922209020253 195377377577789220828382595)
            ·
              refine ⟨293066066366683831242573893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195377377577789220828382595 293066066366683831242573893)
              ·
                refine ⟨54949887443753218357982605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293066066366683831242573893 54949887443753218357982605)
                ·
                  refine ⟨20606207791407456884243477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54949887443753218357982605 20606207791407456884243477)
                  ·
                    refine ⟨965915990222224541448913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20606207791407456884243477 965915990222224541448913)
                    ·
                      rfl

theorem cell23_5643344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 6].length) (baseStart_5643344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643344 prefixEnd_5643344 := by exact prefixLift 5643344
  have htrace : WordTrace (prefixWord ++ tailWord_5643344) baseStart_5643344 baseEnd_5643344 := by
    simpa [prefixWord, tailWord_5643344, baseEnd_5643344] using wordTrace_append hprefix tailTrace_5643344
  have hstable : (prefixWord ++ tailWord_5643344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643344).length < 2 ^ (prefixWord ++ tailWord_5643344).sum := by decide
  have hdescent : baseEnd_5643344 < baseStart_5643344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643345 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_5643345 : Nat := 118140960795 + 5643345 * 2 ^ 59
def prefixEnd_5643345 : Nat := 4983230072969 + 3 ^ 40 * 5643345 * 2
def baseEnd_5643345 : Nat := 2897748484147328120434235

theorem tailTrace_5643345 : CollatzResearch.WordTrace tailWord_5643345 prefixEnd_5643345 2897748484147328120434235 := by
  unfold tailWord_5643345
  simp only [CollatzResearch.WordTrace]
  refine ⟨205829701740132346438547489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137219801160088230959031659 205829701740132346438547489)
  ·
    refine ⟨154372276305099259828910617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205829701740132346438547489 154372276305099259828910617)
    ·
      refine ⟨115779207228824444871682963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154372276305099259828910617 115779207228824444871682963)
      ·
        refine ⟨173668810843236667307524445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115779207228824444871682963 173668810843236667307524445)
        ·
          refine ⟨65125804066213750240321667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173668810843236667307524445 65125804066213750240321667)
          ·
            refine ⟨97688706099320625360482501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65125804066213750240321667 97688706099320625360482501)
            ·
              refine ⟨18316632393622617255090469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97688706099320625360482501 18316632393622617255090469)
              ·
                refine ⟨3434368573804240735329463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18316632393622617255090469 3434368573804240735329463)
                ·
                  refine ⟨5151552860706361102994195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434368573804240735329463 5151552860706361102994195)
                  ·
                    refine ⟨7727329291059541654491293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151552860706361102994195 7727329291059541654491293)
                    ·
                      refine ⟨2897748484147328120434235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727329291059541654491293 2897748484147328120434235)
                      ·
                        rfl

theorem cell23_5643345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_5643345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643345 prefixEnd_5643345 := by exact prefixLift 5643345
  have htrace : WordTrace (prefixWord ++ tailWord_5643345) baseStart_5643345 baseEnd_5643345 := by
    simpa [prefixWord, tailWord_5643345, baseEnd_5643345] using wordTrace_append hprefix tailTrace_5643345
  have hstable : (prefixWord ++ tailWord_5643345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643345).length < 2 ^ (prefixWord ++ tailWord_5643345).sum := by decide
  have hdescent : baseEnd_5643345 < baseStart_5643345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643361 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 6]
def baseStart_5643361 : Nat := 118140960795 + 5643361 * 2 ^ 59
def prefixEnd_5643361 : Nat := 4983230072969 + 3 ^ 40 * 5643361 * 2
def baseEnd_5643361 : Nat := 965918899945933352611387

theorem tailTrace_5643361 : CollatzResearch.WordTrace tailWord_5643361 prefixEnd_5643361 965918899945933352611387 := by
  unfold tailWord_5643361
  simp only [CollatzResearch.WordTrace]
  refine ⟨205830285308074381171129937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137220190205382920780753291 205830285308074381171129937)
  ·
    refine ⟨154372713981055785878347453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205830285308074381171129937 154372713981055785878347453)
    ·
      refine ⟨57889767742895919704380295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154372713981055785878347453 57889767742895919704380295)
      ·
        refine ⟨86834651614343879556570443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57889767742895919704380295 86834651614343879556570443)
        ·
          refine ⟨130251977421515819334855665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86834651614343879556570443 130251977421515819334855665)
          ·
            refine ⟨97688983066136864501141749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130251977421515819334855665 97688983066136864501141749)
            ·
              refine ⟨9158342162450331046982039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97688983066136864501141749 9158342162450331046982039)
              ·
                refine ⟨13737513243675496570473059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9158342162450331046982039 13737513243675496570473059)
                ·
                  refine ⟨20606269865513244855709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13737513243675496570473059 20606269865513244855709589)
                  ·
                    refine ⟨965918899945933352611387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20606269865513244855709589 965918899945933352611387)
                    ·
                      rfl

theorem cell23_5643361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_5643361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643361 prefixEnd_5643361 := by exact prefixLift 5643361
  have htrace : WordTrace (prefixWord ++ tailWord_5643361) baseStart_5643361 baseEnd_5643361 := by
    simpa [prefixWord, tailWord_5643361, baseEnd_5643361] using wordTrace_append hprefix tailTrace_5643361
  have hstable : (prefixWord ++ tailWord_5643361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643361).length < 2 ^ (prefixWord ++ tailWord_5643361).sum := by decide
  have hdescent : baseEnd_5643361 < baseStart_5643361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643388 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_5643388 : Nat := 118140960795 + 5643388 * 2 ^ 59
def prefixEnd_5643388 : Nat := 4983230072969 + 3 ^ 40 * 5643388 * 2
def baseEnd_5643388 : Nat := 2897770563815471452196537

theorem tailTrace_5643388 : CollatzResearch.WordTrace tailWord_5643388 prefixEnd_5643388 2897770563815471452196537 := by
  unfold tailWord_5643388
  simp only [CollatzResearch.WordTrace]
  refine ⟨102915635039488282391181409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137220846719317709854908545 102915635039488282391181409)
  ·
    refine ⟨77186726279616211793386057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102915635039488282391181409 77186726279616211793386057)
    ·
      refine ⟨57890044709712158845039543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77186726279616211793386057 57890044709712158845039543)
      ·
        refine ⟨86835067064568238267559315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57890044709712158845039543 86835067064568238267559315)
        ·
          refine ⟨130252600596852357401338973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86835067064568238267559315 130252600596852357401338973)
          ·
            refine ⟨48844725223819634025502115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130252600596852357401338973 48844725223819634025502115)
            ·
              refine ⟨73267087835729451038253173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48844725223819634025502115 73267087835729451038253173)
              ·
                refine ⟨6868789484599636034836235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73267087835729451038253173 6868789484599636034836235)
                ·
                  refine ⟨10303184226899454052254353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868789484599636034836235 10303184226899454052254353)
                  ·
                    refine ⟨7727388170174590539190765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10303184226899454052254353 7727388170174590539190765)
                    ·
                      refine ⟨2897770563815471452196537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727388170174590539190765 2897770563815471452196537)
                      ·
                        rfl

theorem cell23_5643388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_5643388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643388 prefixEnd_5643388 := by exact prefixLift 5643388
  have htrace : WordTrace (prefixWord ++ tailWord_5643388) baseStart_5643388 baseEnd_5643388 := by
    simpa [prefixWord, tailWord_5643388, baseEnd_5643388] using wordTrace_append hprefix tailTrace_5643388
  have hstable : (prefixWord ++ tailWord_5643388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643388).length < 2 ^ (prefixWord ++ tailWord_5643388).sum := by decide
  have hdescent : baseEnd_5643388 < baseStart_5643388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643422 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5643422 : Nat := 118140960795 + 5643422 * 2 ^ 59
def prefixEnd_5643422 : Nat := 4983230072969 + 3 ^ 40 * 5643422 * 2
def baseEnd_5643422 : Nat := 2897788022157724319171381

theorem tailTrace_5643422 : CollatzResearch.WordTrace tailWord_5643422 prefixEnd_5643422 2897788022157724319171381 := by
  unfold tailWord_5643422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25729063770106673573637565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137221673440568925726067013 25729063770106673573637565)
  ·
    refine ⟨9648398913790002590114087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25729063770106673573637565 9648398913790002590114087)
    ·
      refine ⟨14472598370685003885171131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9648398913790002590114087 14472598370685003885171131)
      ·
        refine ⟨21708897556027505827756697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472598370685003885171131 21708897556027505827756697)
        ·
          refine ⟨16281673167020629370817523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21708897556027505827756697 16281673167020629370817523)
          ·
            refine ⟨24422509750530944056226285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16281673167020629370817523 24422509750530944056226285)
            ·
              refine ⟨9158441156449104021084857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24422509750530944056226285 9158441156449104021084857)
              ·
                refine ⟨6868830867336828015813643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158441156449104021084857 6868830867336828015813643)
                ·
                  refine ⟨10303246301005242023720465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868830867336828015813643 10303246301005242023720465)
                  ·
                    refine ⟨7727434725753931517790349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10303246301005242023720465 7727434725753931517790349)
                    ·
                      refine ⟨2897788022157724319171381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727434725753931517790349 2897788022157724319171381)
                      ·
                        rfl

theorem cell23_5643422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5643422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643422 prefixEnd_5643422 := by exact prefixLift 5643422
  have htrace : WordTrace (prefixWord ++ tailWord_5643422) baseStart_5643422 baseEnd_5643422 := by
    simpa [prefixWord, tailWord_5643422, baseEnd_5643422] using wordTrace_append hprefix tailTrace_5643422
  have hstable : (prefixWord ++ tailWord_5643422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643422).length < 2 ^ (prefixWord ++ tailWord_5643422).sum := by decide
  have hdescent : baseEnd_5643422 < baseStart_5643422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643452 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5643452 : Nat := 118140960795 + 5643452 * 2 ^ 59
def prefixEnd_5643452 : Nat := 4983230072969 + 3 ^ 40 * 5643452 * 2
def baseEnd_5643452 : Nat := 2897803426577359201796243

theorem tailTrace_5643452 : CollatzResearch.WordTrace tailWord_5643452 prefixEnd_5643452 2897803426577359201796243 := by
  unfold tailWord_5643452
  simp only [CollatzResearch.WordTrace]
  refine ⟨102916802175372351856346305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137222402900496469141795073 102916802175372351856346305)
  ·
    refine ⟨77187601631529263892259729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102916802175372351856346305 77187601631529263892259729)
    ·
      refine ⟨57890701223646947919194797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77187601631529263892259729 57890701223646947919194797)
      ·
        refine ⟨21709012958867605469698049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57890701223646947919194797 21709012958867605469698049)
        ·
          refine ⟨16281759719150704102273537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21709012958867605469698049 16281759719150704102273537)
          ·
            refine ⟨12211319789363028076705153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16281759719150704102273537 12211319789363028076705153)
            ·
              refine ⟨9158489842022271057528865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12211319789363028076705153 9158489842022271057528865)
              ·
                refine ⟨6868867381516703293146649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158489842022271057528865 6868867381516703293146649)
                ·
                  refine ⟨5151650536137527469859987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868867381516703293146649 5151650536137527469859987)
                  ·
                    refine ⟨7727475804206291204789981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151650536137527469859987 7727475804206291204789981)
                    ·
                      refine ⟨2897803426577359201796243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727475804206291204789981 2897803426577359201796243)
                      ·
                        rfl

theorem cell23_5643452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5643452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643452 prefixEnd_5643452 := by exact prefixLift 5643452
  have htrace : WordTrace (prefixWord ++ tailWord_5643452) baseStart_5643452 baseEnd_5643452 := by
    simpa [prefixWord, tailWord_5643452, baseEnd_5643452] using wordTrace_append hprefix tailTrace_5643452
  have hstable : (prefixWord ++ tailWord_5643452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643452).length < 2 ^ (prefixWord ++ tailWord_5643452).sum := by decide
  have hdescent : baseEnd_5643452 < baseStart_5643452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643469 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5643469 : Nat := 118140960795 + 5643469 * 2 ^ 59
def prefixEnd_5643469 : Nat := 4983230072969 + 3 ^ 40 * 5643469 * 2
def baseEnd_5643469 : Nat := 2897812155748485635283665

theorem tailTrace_5643469 : CollatzResearch.WordTrace tailWord_5643469 prefixEnd_5643469 2897812155748485635283665 := by
  unfold tailWord_5643469
  simp only [CollatzResearch.WordTrace]
  refine ⟨205834224391683115616061461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137222816261122077077374307 205834224391683115616061461)
  ·
    refine ⟨9648479268360146044502881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205834224391683115616061461 9648479268360146044502881)
    ·
      refine ⟨7236359451270109533377161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9648479268360146044502881 7236359451270109533377161)
      ·
        refine ⟨5427269588452582150032871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7236359451270109533377161 5427269588452582150032871)
        ·
          refine ⟨8140904382678873225049307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427269588452582150032871 8140904382678873225049307)
          ·
            refine ⟨12211356574018309837573961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140904382678873225049307 12211356574018309837573961)
            ·
              refine ⟨9158517430513732378180471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12211356574018309837573961 9158517430513732378180471)
              ·
                refine ⟨13737776145770598567270707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9158517430513732378180471 13737776145770598567270707)
                ·
                  refine ⟨20606664218655897850906061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13737776145770598567270707 20606664218655897850906061)
                  ·
                    refine ⟨7727499081995961694089773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20606664218655897850906061 7727499081995961694089773)
                    ·
                      refine ⟨2897812155748485635283665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727499081995961694089773 2897812155748485635283665)
                      ·
                        rfl

theorem cell23_5643469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5643469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643469 prefixEnd_5643469 := by exact prefixLift 5643469
  have htrace : WordTrace (prefixWord ++ tailWord_5643469) baseStart_5643469 baseEnd_5643469 := by
    simpa [prefixWord, tailWord_5643469, baseEnd_5643469] using wordTrace_append hprefix tailTrace_5643469
  have hstable : (prefixWord ++ tailWord_5643469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643469).length < 2 ^ (prefixWord ++ tailWord_5643469).sum := by decide
  have hdescent : baseEnd_5643469 < baseStart_5643469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643541 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_5643541 : Nat := 118140960795 + 5643541 * 2 ^ 59
def prefixEnd_5643541 : Nat := 4983230072969 + 3 ^ 40 * 5643541 * 2
def baseEnd_5643541 : Nat := 965949708785203117861111

theorem tailTrace_5643541 : CollatzResearch.WordTrace tailWord_5643541 prefixEnd_5643541 965949708785203117861111 := by
  unfold tailWord_5643541
  simp only [CollatzResearch.WordTrace]
  refine ⟨205836850447422271912682477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137224566964948181275121651 205836850447422271912682477)
  ·
    refine ⟨77188818917783351967255929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205836850447422271912682477 77188818917783351967255929)
    ·
      refine ⟨57891614188337513975441947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77188818917783351967255929 57891614188337513975441947)
      ·
        refine ⟨86837421282506270963162921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57891614188337513975441947 86837421282506270963162921)
        ·
          refine ⟨65128065961879703222372191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86837421282506270963162921 65128065961879703222372191)
          ·
            refine ⟨97692098942819554833558287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65128065961879703222372191 97692098942819554833558287)
            ·
              refine ⟨146538148414229332250337431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97692098942819554833558287 146538148414229332250337431)
              ·
                refine ⟨219807222621343998375506147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146538148414229332250337431 219807222621343998375506147)
                ·
                  refine ⟨329710833932015997563259221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219807222621343998375506147 329710833932015997563259221)
                  ·
                    refine ⟨965949708785203117861111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 329710833932015997563259221 965949708785203117861111)
                    ·
                      rfl

theorem cell23_5643541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_5643541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643541 prefixEnd_5643541 := by exact prefixLift 5643541
  have htrace : WordTrace (prefixWord ++ tailWord_5643541) baseStart_5643541 baseEnd_5643541 := by
    simpa [prefixWord, tailWord_5643541, baseEnd_5643541] using wordTrace_append hprefix tailTrace_5643541
  have hstable : (prefixWord ++ tailWord_5643541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643541).length < 2 ^ (prefixWord ++ tailWord_5643541).sum := by decide
  have hdescent : baseEnd_5643541 < baseStart_5643541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643548 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_5643548 : Nat := 118140960795 + 5643548 * 2 ^ 59
def prefixEnd_5643548 : Nat := 4983230072969 + 3 ^ 40 * 5643548 * 2
def baseEnd_5643548 : Nat := 2897852720720190826195801

theorem tailTrace_5643548 : CollatzResearch.WordTrace tailWord_5643548 prefixEnd_5643548 2897852720720190826195801 := by
  unfold tailWord_5643548
  simp only [CollatzResearch.WordTrace]
  refine ⟨102918552879198456054093649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137224737172264608072124865 102918552879198456054093649)
  ·
    refine ⟨77188914659398842040570237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102918552879198456054093649 77188914659398842040570237)
    ·
      refine ⟨28945842997274565765213839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77188914659398842040570237 28945842997274565765213839)
      ·
        refine ⟨43418764495911848647820759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28945842997274565765213839 43418764495911848647820759)
        ·
          refine ⟨65128146743867772971731139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43418764495911848647820759 65128146743867772971731139)
          ·
            refine ⟨97692220115801659457596709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65128146743867772971731139 97692220115801659457596709)
            ·
              refine ⟨18317291271712811148299383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97692220115801659457596709 18317291271712811148299383)
              ·
                refine ⟨27475936907569216722449075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18317291271712811148299383 27475936907569216722449075)
                ·
                  refine ⟨41213905361353825083673613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27475936907569216722449075 41213905361353825083673613)
                  ·
                    refine ⟨15455214510507684406377605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41213905361353825083673613 15455214510507684406377605)
                    ·
                      refine ⟨2897852720720190826195801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15455214510507684406377605 2897852720720190826195801)
                      ·
                        rfl

theorem cell23_5643548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_5643548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643548 prefixEnd_5643548 := by exact prefixLift 5643548
  have htrace : WordTrace (prefixWord ++ tailWord_5643548) baseStart_5643548 baseEnd_5643548 := by
    simpa [prefixWord, tailWord_5643548, baseEnd_5643548] using wordTrace_append hprefix tailTrace_5643548
  have hstable : (prefixWord ++ tailWord_5643548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643548).length < 2 ^ (prefixWord ++ tailWord_5643548).sum := by decide
  have hdescent : baseEnd_5643548 < baseStart_5643548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643561 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_5643561 : Nat := 118140960795 + 5643561 * 2 ^ 59
def prefixEnd_5643561 : Nat := 4983230072969 + 3 ^ 40 * 5643561 * 2
def baseEnd_5643561 : Nat := 2897859395968699275333241

theorem tailTrace_5643561 : CollatzResearch.WordTrace tailWord_5643561 prefixEnd_5643561 2897859395968699275333241 := by
  unfold tailWord_5643561
  simp only [CollatzResearch.WordTrace]
  refine ⟨205837579907349815328410537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137225053271566543552273691 205837579907349815328410537)
  ·
    refine ⟨154378184930512361496307903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205837579907349815328410537 154378184930512361496307903)
    ·
      refine ⟨231567277395768542244461855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154378184930512361496307903 231567277395768542244461855)
      ·
        refine ⟨347350916093652813366692783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231567277395768542244461855 347350916093652813366692783)
        ·
          refine ⟨521026374140479220050039175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347350916093652813366692783 521026374140479220050039175)
          ·
            refine ⟨781539561210718830075058763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521026374140479220050039175 781539561210718830075058763)
            ·
              refine ⟨1172309341816078245112588145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781539561210718830075058763 1172309341816078245112588145)
              ·
                refine ⟨879232006362058683834441109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172309341816078245112588145 879232006362058683834441109)
                ·
                  refine ⟨41214000298221500804739427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879232006362058683834441109 41214000298221500804739427)
                  ·
                    refine ⟨61821000447332251207109141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41214000298221500804739427 61821000447332251207109141)
                    ·
                      refine ⟨2897859395968699275333241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61821000447332251207109141 2897859395968699275333241)
                      ·
                        rfl

theorem cell23_5643561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_5643561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643561 prefixEnd_5643561 := by exact prefixLift 5643561
  have htrace : WordTrace (prefixWord ++ tailWord_5643561) baseStart_5643561 baseEnd_5643561 := by
    simpa [prefixWord, tailWord_5643561, baseEnd_5643561] using wordTrace_append hprefix tailTrace_5643561
  have hstable : (prefixWord ++ tailWord_5643561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643561).length < 2 ^ (prefixWord ++ tailWord_5643561).sum := by decide
  have hdescent : baseEnd_5643561 < baseStart_5643561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643625 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 4, 3, 2]
def baseStart_5643625 : Nat := 118140960795 + 5643625 * 2 ^ 59
def prefixEnd_5643625 : Nat := 4983230072969 + 3 ^ 40 * 5643625 * 2
def baseEnd_5643625 : Nat := 2897892258730587024932947

theorem tailTrace_5643625 : CollatzResearch.WordTrace tailWord_5643625 prefixEnd_5643625 2897892258730587024932947 := by
  unfold tailWord_5643625
  simp only [CollatzResearch.WordTrace]
  refine ⟨205839914179117954258740329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137226609452745302839160219 205839914179117954258740329)
  ·
    refine ⟨154379935634338465694055247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205839914179117954258740329 154379935634338465694055247)
    ·
      refine ⟨231569903451507698541082871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154379935634338465694055247 231569903451507698541082871)
      ·
        refine ⟨347354855177261547811624307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231569903451507698541082871 347354855177261547811624307)
        ·
          refine ⟨521032282765892321717436461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347354855177261547811624307 521032282765892321717436461)
          ·
            refine ⟨195387106037209620644038673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521032282765892321717436461 195387106037209620644038673)
            ·
              refine ⟨146540329527907215483029005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195387106037209620644038673 146540329527907215483029005)
              ·
                refine ⟨54952623572965205806135877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146540329527907215483029005 54952623572965205806135877)
                ·
                  refine ⟨10303616919930976088650477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54952623572965205806135877 10303616919930976088650477)
                  ·
                    refine ⟨3863856344974116033243929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10303616919930976088650477 3863856344974116033243929)
                    ·
                      refine ⟨2897892258730587024932947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863856344974116033243929 2897892258730587024932947)
                      ·
                        rfl

theorem cell23_5643625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3, 2].length) (baseStart_5643625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643625 prefixEnd_5643625 := by exact prefixLift 5643625
  have htrace : WordTrace (prefixWord ++ tailWord_5643625) baseStart_5643625 baseEnd_5643625 := by
    simpa [prefixWord, tailWord_5643625, baseEnd_5643625] using wordTrace_append hprefix tailTrace_5643625
  have hstable : (prefixWord ++ tailWord_5643625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643625).length < 2 ^ (prefixWord ++ tailWord_5643625).sum := by decide
  have hdescent : baseEnd_5643625 < baseStart_5643625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643649 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5643649 : Nat := 118140960795 + 5643649 * 2 ^ 59
def prefixEnd_5643649 : Nat := 4983230072969 + 3 ^ 40 * 5643649 * 2
def baseEnd_5643649 : Nat := 2897904582266294931032837

theorem tailTrace_5643649 : CollatzResearch.WordTrace tailWord_5643649 prefixEnd_5643649 2897904582266294931032837 := by
  unfold tailWord_5643649
  simp only [CollatzResearch.WordTrace]
  refine ⟨205840789531031006357614001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137227193020687337571742667 205840789531031006357614001)
  ·
    refine ⟨154380592148273254768210501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205840789531031006357614001 154380592148273254768210501)
    ·
      refine ⟨28946361027801235269039469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154380592148273254768210501 28946361027801235269039469)
      ·
        refine ⟨10854885385425463225889801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28946361027801235269039469 10854885385425463225889801)
        ·
          refine ⟨8141164039069097419417351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10854885385425463225889801 8141164039069097419417351)
          ·
            refine ⟨12211746058603646129126027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8141164039069097419417351 12211746058603646129126027)
            ·
              refine ⟨18317619087905469193689041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12211746058603646129126027 18317619087905469193689041)
              ·
                refine ⟨13738214315929101895266781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18317619087905469193689041 13738214315929101895266781)
                ·
                  refine ⟨5151830368473413210725043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13738214315929101895266781 5151830368473413210725043)
                  ·
                    refine ⟨7727745552710119816087565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151830368473413210725043 7727745552710119816087565)
                    ·
                      refine ⟨2897904582266294931032837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727745552710119816087565 2897904582266294931032837)
                      ·
                        rfl

theorem cell23_5643649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5643649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643649 prefixEnd_5643649 := by exact prefixLift 5643649
  have htrace : WordTrace (prefixWord ++ tailWord_5643649) baseStart_5643649 baseEnd_5643649 := by
    simpa [prefixWord, tailWord_5643649, baseEnd_5643649] using wordTrace_append hprefix tailTrace_5643649
  have hstable : (prefixWord ++ tailWord_5643649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643649).length < 2 ^ (prefixWord ++ tailWord_5643649).sum := by decide
  have hdescent : baseEnd_5643649 < baseStart_5643649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643655 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5643655 : Nat := 118140960795 + 5643655 * 2 ^ 59
def prefixEnd_5643655 : Nat := 4983230072969 + 3 ^ 40 * 5643655 * 2
def baseEnd_5643655 : Nat := 2897907663150221907557809

theorem tailTrace_5643655 : CollatzResearch.WordTrace tailWord_5643655 prefixEnd_5643655 2897907663150221907557809 := by
  unfold tailWord_5643655
  simp only [CollatzResearch.WordTrace]
  refine ⟨205841008369009269382332419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137227338912672846254888279 205841008369009269382332419)
  ·
    refine ⟨308761512553513904073498629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205841008369009269382332419 308761512553513904073498629)
    ·
      refine ⟨57892783603783857013780993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308761512553513904073498629 57892783603783857013780993)
      ·
        refine ⟨43419587702837892760335745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57892783603783857013780993 43419587702837892760335745)
        ·
          refine ⟨32564690777128419570251809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43419587702837892760335745 32564690777128419570251809)
          ·
            refine ⟨24423518082846314677688857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32564690777128419570251809 24423518082846314677688857)
            ·
              refine ⟨18317638562134736008266643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24423518082846314677688857 18317638562134736008266643)
              ·
                refine ⟨27476457843202104012399965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18317638562134736008266643 27476457843202104012399965)
                ·
                  refine ⟨10303671691200789004649987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27476457843202104012399965 10303671691200789004649987)
                  ·
                    refine ⟨15455507536801183506974981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10303671691200789004649987 15455507536801183506974981)
                    ·
                      refine ⟨2897907663150221907557809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15455507536801183506974981 2897907663150221907557809)
                      ·
                        rfl

theorem cell23_5643655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5643655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643655 prefixEnd_5643655 := by exact prefixLift 5643655
  have htrace : WordTrace (prefixWord ++ tailWord_5643655) baseStart_5643655 baseEnd_5643655 := by
    simpa [prefixWord, tailWord_5643655, baseEnd_5643655] using wordTrace_append hprefix tailTrace_5643655
  have hstable : (prefixWord ++ tailWord_5643655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643655).length < 2 ^ (prefixWord ++ tailWord_5643655).sum := by decide
  have hdescent : baseEnd_5643655 < baseStart_5643655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643682 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5643682 : Nat := 118140960795 + 5643682 * 2 ^ 59
def prefixEnd_5643682 : Nat := 4983230072969 + 3 ^ 40 * 5643682 * 2
def baseEnd_5643682 : Nat := 965973842375964433973395

theorem tailTrace_5643682 : CollatzResearch.WordTrace tailWord_5643682 prefixEnd_5643682 965973842375964433973395 := by
  unfold tailWord_5643682
  simp only [CollatzResearch.WordTrace]
  refine ⟨51460498284977863248391325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137227995426607635329043533 51460498284977863248391325)
  ·
    refine ⟨19297686856866698718146747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51460498284977863248391325 19297686856866698718146747)
    ·
      refine ⟨28946530285300048077220121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297686856866698718146747 28946530285300048077220121)
      ·
        refine ⟨21709897713975036057915091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28946530285300048077220121 21709897713975036057915091)
        ·
          refine ⟨32564846570962554086872637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21709897713975036057915091 32564846570962554086872637)
          ·
            refine ⟨12211817464110957782577239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32564846570962554086872637 12211817464110957782577239)
            ·
              refine ⟨18317726196166436673865859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12211817464110957782577239 18317726196166436673865859)
              ·
                refine ⟨27476589294249655010798789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18317726196166436673865859 27476589294249655010798789)
                ·
                  refine ⟨5151860492671810314524773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27476589294249655010798789 5151860492671810314524773)
                  ·
                    refine ⟨965973842375964433973395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151860492671810314524773 965973842375964433973395)
                    ·
                      rfl

theorem cell23_5643682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5643682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643682 prefixEnd_5643682 := by exact prefixLift 5643682
  have htrace : WordTrace (prefixWord ++ tailWord_5643682) baseStart_5643682 baseEnd_5643682 := by
    simpa [prefixWord, tailWord_5643682, baseEnd_5643682] using wordTrace_append hprefix tailTrace_5643682
  have hstable : (prefixWord ++ tailWord_5643682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643682).length < 2 ^ (prefixWord ++ tailWord_5643682).sum := by decide
  have hdescent : baseEnd_5643682 < baseStart_5643682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5643698 : Nat := 118140960795 + 5643698 * 2 ^ 59
def prefixEnd_5643698 : Nat := 4983230072969 + 3 ^ 40 * 5643698 * 2
def baseEnd_5643698 : Nat := 2897929742818365239320111

theorem tailTrace_5643698 : CollatzResearch.WordTrace tailWord_5643698 prefixEnd_5643698 2897929742818365239320111 := by
  unfold tailWord_5643698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51460644176963371931536937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137228384471902325150765165 51460644176963371931536937)
  ·
    refine ⟨38595483132722528948652703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51460644176963371931536937 38595483132722528948652703)
    ·
      refine ⟨57893224699083793422979055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38595483132722528948652703 57893224699083793422979055)
      ·
        refine ⟨86839837048625690134468583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57893224699083793422979055 86839837048625690134468583)
        ·
          refine ⟨130259755572938535201702875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86839837048625690134468583 130259755572938535201702875)
          ·
            refine ⟨195389633359407802802554313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130259755572938535201702875 195389633359407802802554313)
            ·
              refine ⟨146542225019555852101915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195389633359407802802554313 146542225019555852101915735)
              ·
                refine ⟨219813337529333778152873603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146542225019555852101915735 219813337529333778152873603)
                ·
                  refine ⟨329720006294000667229310405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219813337529333778152873603 329720006294000667229310405)
                  ·
                    refine ⟨61822501180125125105495701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 329720006294000667229310405 61822501180125125105495701)
                    ·
                      refine ⟨2897929742818365239320111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61822501180125125105495701 2897929742818365239320111)
                      ·
                        rfl

theorem cell23_5643698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5643698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643698 prefixEnd_5643698 := by exact prefixLift 5643698
  have htrace : WordTrace (prefixWord ++ tailWord_5643698) baseStart_5643698 baseEnd_5643698 := by
    simpa [prefixWord, tailWord_5643698, baseEnd_5643698] using wordTrace_append hprefix tailTrace_5643698
  have hstable : (prefixWord ++ tailWord_5643698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643698).length < 2 ^ (prefixWord ++ tailWord_5643698).sum := by decide
  have hdescent : baseEnd_5643698 < baseStart_5643698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643722 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_5643722 : Nat := 118140960795 + 5643722 * 2 ^ 59
def prefixEnd_5643722 : Nat := 4983230072969 + 3 ^ 40 * 5643722 * 2
def baseEnd_5643722 : Nat := 2897942066354073145420001

theorem tailTrace_5643722 : CollatzResearch.WordTrace tailWord_5643722 prefixEnd_5643722 2897942066354073145420001 := by
  unfold tailWord_5643722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51460863014941634956255355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137228968039844359883347613 51460863014941634956255355)
  ·
    refine ⟨77191294522412452434383033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51460863014941634956255355 77191294522412452434383033)
    ·
      refine ⟨57893470891809339325787275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77191294522412452434383033 57893470891809339325787275)
      ·
        refine ⟨86840206337714008988680913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57893470891809339325787275 86840206337714008988680913)
        ·
          refine ⟨65130154753285506741510685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86840206337714008988680913 65130154753285506741510685)
          ·
            refine ⟨24423808032482065028066507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65130154753285506741510685 24423808032482065028066507)
            ·
              refine ⟨36635712048723097542099761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24423808032482065028066507 36635712048723097542099761)
              ·
                refine ⟨27476784036542323156574821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36635712048723097542099761 27476784036542323156574821)
                ·
                  refine ⟨5151897006851685591857779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27476784036542323156574821 5151897006851685591857779)
                  ·
                    refine ⟨7727845510277528387786669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151897006851685591857779 7727845510277528387786669)
                    ·
                      refine ⟨2897942066354073145420001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7727845510277528387786669 2897942066354073145420001)
                      ·
                        rfl

theorem cell23_5643722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_5643722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643722 prefixEnd_5643722 := by exact prefixLift 5643722
  have htrace : WordTrace (prefixWord ++ tailWord_5643722) baseStart_5643722 baseEnd_5643722 := by
    simpa [prefixWord, tailWord_5643722, baseEnd_5643722] using wordTrace_append hprefix tailTrace_5643722
  have hstable : (prefixWord ++ tailWord_5643722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643722).length < 2 ^ (prefixWord ++ tailWord_5643722).sum := by decide
  have hdescent : baseEnd_5643722 < baseStart_5643722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643766 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5643766 : Nat := 118140960795 + 5643766 * 2 ^ 59
def prefixEnd_5643766 : Nat := 4983230072969 + 3 ^ 40 * 5643766 * 2
def baseEnd_5643766 : Nat := 2897964659502870973269799

theorem tailTrace_5643766 : CollatzResearch.WordTrace tailWord_5643766 prefixEnd_5643766 2897964659502870973269799 := by
  unfold tailWord_5643766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865316054475445958726447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137230037914404756893082101 12865316054475445958726447)
  ·
    refine ⟨19297974081713168938089671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12865316054475445958726447 19297974081713168938089671)
    ·
      refine ⟨28946961122569753407134507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297974081713168938089671 28946961122569753407134507)
      ·
        refine ⟨43420441683854630110701761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28946961122569753407134507 43420441683854630110701761)
        ·
          refine ⟨32565331262890972583026321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43420441683854630110701761 32565331262890972583026321)
          ·
            refine ⟨24423998447168229437269741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32565331262890972583026321 24423998447168229437269741)
            ·
              refine ⟨9158999417688086038976153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24423998447168229437269741 9158999417688086038976153)
              ·
                refine ⟨6869249563266064529232115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158999417688086038976153 6869249563266064529232115)
                ·
                  refine ⟨10303874344899096793848173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869249563266064529232115 10303874344899096793848173)
                  ·
                    refine ⟨3863952879337161297693065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10303874344899096793848173 3863952879337161297693065)
                    ·
                      refine ⟨2897964659502870973269799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3863952879337161297693065 2897964659502870973269799)
                      ·
                        rfl

theorem cell23_5643766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5643766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643766 prefixEnd_5643766 := by exact prefixLift 5643766
  have htrace : WordTrace (prefixWord ++ tailWord_5643766) baseStart_5643766 baseEnd_5643766 := by
    simpa [prefixWord, tailWord_5643766, baseEnd_5643766] using wordTrace_append hprefix tailTrace_5643766
  have hstable : (prefixWord ++ tailWord_5643766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643766).length < 2 ^ (prefixWord ++ tailWord_5643766).sum := by decide
  have hdescent : baseEnd_5643766 < baseStart_5643766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643832 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_5643832 : Nat := 118140960795 + 5643832 * 2 ^ 59
def prefixEnd_5643832 : Nat := 4983230072969 + 3 ^ 40 * 5643832 * 2
def baseEnd_5643832 : Nat := 965999516408689238348165

theorem tailTrace_5643832 : CollatzResearch.WordTrace tailWord_5643832 prefixEnd_5643832 965999516408689238348165 := by
  unfold tailWord_5643832
  simp only [CollatzResearch.WordTrace]
  refine ⟨102923732044684014305762875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137231642726245352407683833 102923732044684014305762875)
  ·
    refine ⟨154385598067026021458644313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102923732044684014305762875 154385598067026021458644313)
    ·
      refine ⟨115789198550269516093983235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154385598067026021458644313 115789198550269516093983235)
      ·
        refine ⟨173683797825404274140974853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115789198550269516093983235 173683797825404274140974853)
        ·
          refine ⟨32565712092263301401432785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173683797825404274140974853 32565712092263301401432785)
          ·
            refine ⟨24424284069197476051074589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32565712092263301401432785 24424284069197476051074589)
            ·
              refine ⟨9159106525949053519152971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24424284069197476051074589 9159106525949053519152971)
              ·
                refine ⟨13738659788923580278729457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159106525949053519152971 13738659788923580278729457)
                ·
                  refine ⟨10303994841692685209047093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13738659788923580278729457 10303994841692685209047093)
                  ·
                    refine ⟨965999516408689238348165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10303994841692685209047093 965999516408689238348165)
                    ·
                      rfl

theorem cell23_5643832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_5643832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643832 prefixEnd_5643832 := by exact prefixLift 5643832
  have htrace : WordTrace (prefixWord ++ tailWord_5643832) baseStart_5643832 baseEnd_5643832 := by
    simpa [prefixWord, tailWord_5643832, baseEnd_5643832] using wordTrace_append hprefix tailTrace_5643832
  have hstable : (prefixWord ++ tailWord_5643832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643832).length < 2 ^ (prefixWord ++ tailWord_5643832).sum := by decide
  have hdescent : baseEnd_5643832 < baseStart_5643832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643952 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_5643952 : Nat := 118140960795 + 5643952 * 2 ^ 59
def prefixEnd_5643952 : Nat := 4983230072969 + 3 ^ 40 * 5643952 * 2
def baseEnd_5643952 : Nat := 966020055634869081847981

theorem tailTrace_5643952 : CollatzResearch.WordTrace tailWord_5643952 prefixEnd_5643952 966020055634869081847981 := by
  unfold tailWord_5643952
  simp only [CollatzResearch.WordTrace]
  refine ⟨102925920424466644552947055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137234560565955526070596073 102925920424466644552947055)
  ·
    refine ⟨154388880636699966829420583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102925920424466644552947055 154388880636699966829420583)
    ·
      refine ⟨231583320955049950244130875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154388880636699966829420583 231583320955049950244130875)
      ·
        refine ⟨347374981432574925366196313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231583320955049950244130875 347374981432574925366196313)
        ·
          refine ⟨260531236074431194024647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347374981432574925366196313 260531236074431194024647235)
          ·
            refine ⟨390796854111646791036970853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260531236074431194024647235 390796854111646791036970853)
            ·
              refine ⟨73274410145933773319432035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 390796854111646791036970853 73274410145933773319432035)
              ·
                refine ⟨109911615218900659979148053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73274410145933773319432035 109911615218900659979148053)
                ·
                  refine ⟨5152106963385968436522565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109911615218900659979148053 5152106963385968436522565)
                  ·
                    refine ⟨966020055634869081847981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152106963385968436522565 966020055634869081847981)
                    ·
                      rfl

theorem cell23_5643952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_5643952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643952 prefixEnd_5643952 := by exact prefixLift 5643952
  have htrace : WordTrace (prefixWord ++ tailWord_5643952) baseStart_5643952 baseEnd_5643952 := by
    simpa [prefixWord, tailWord_5643952, baseEnd_5643952] using wordTrace_append hprefix tailTrace_5643952
  have hstable : (prefixWord ++ tailWord_5643952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643952).length < 2 ^ (prefixWord ++ tailWord_5643952).sum := by decide
  have hdescent : baseEnd_5643952 < baseStart_5643952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643976 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_5643976 : Nat := 118140960795 + 5643976 * 2 ^ 59
def prefixEnd_5643976 : Nat := 4983230072969 + 3 ^ 40 * 5643976 * 2
def baseEnd_5643976 : Nat := 2898072490440315151643833

theorem tailTrace_5643976 : CollatzResearch.WordTrace tailWord_5643976 prefixEnd_5643976 2898072490440315151643833 := by
  unfold tailWord_5643976
  simp only [CollatzResearch.WordTrace]
  refine ⟨102926358100423170602383891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137235144133897560803178521 102926358100423170602383891)
  ·
    refine ⟨154389537150634755903575837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102926358100423170602383891 154389537150634755903575837)
    ·
      refine ⟨57896076431488033463840939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154389537150634755903575837 57896076431488033463840939)
      ·
        refine ⟨86844114647232050195761409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57896076431488033463840939 86844114647232050195761409)
        ·
          refine ⟨65133085985424037646821057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86844114647232050195761409 65133085985424037646821057)
          ·
            refine ⟨48849814489068028235115793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65133085985424037646821057 48849814489068028235115793)
            ·
              refine ⟨36637360866801021176336845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48849814489068028235115793 36637360866801021176336845)
              ·
                refine ⟨13739010325050382941126317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36637360866801021176336845 13739010325050382941126317)
                ·
                  refine ⟨5152128871893893602922369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13739010325050382941126317 5152128871893893602922369)
                  ·
                    refine ⟨3864096653920420202191777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152128871893893602922369 3864096653920420202191777)
                    ·
                      refine ⟨2898072490440315151643833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864096653920420202191777 2898072490440315151643833)
                      ·
                        rfl

theorem cell23_5643976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_5643976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643976 prefixEnd_5643976 := by exact prefixLift 5643976
  have htrace : WordTrace (prefixWord ++ tailWord_5643976) baseStart_5643976 baseEnd_5643976 := by
    simpa [prefixWord, tailWord_5643976, baseEnd_5643976] using wordTrace_append hprefix tailTrace_5643976
  have hstable : (prefixWord ++ tailWord_5643976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643976).length < 2 ^ (prefixWord ++ tailWord_5643976).sum := by decide
  have hdescent : baseEnd_5643976 < baseStart_5643976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643986 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_5643986 : Nat := 118140960795 + 5643986 * 2 ^ 59
def prefixEnd_5643986 : Nat := 4983230072969 + 3 ^ 40 * 5643986 * 2
def baseEnd_5643986 : Nat := 966025875082286704172929

theorem tailTrace_5643986 : CollatzResearch.WordTrace tailWord_5643986 prefixEnd_5643986 966025875082286704172929 := by
  unfold tailWord_5643986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51463270232702528228157953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137235387287206741941754541 51463270232702528228157953)
  ·
    refine ⟨38597452674526896171118465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51463270232702528228157953 38597452674526896171118465)
    ·
      refine ⟨28948089505895172128338849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38597452674526896171118465 28948089505895172128338849)
      ·
        refine ⟨21711067129421379096254137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28948089505895172128338849 21711067129421379096254137)
        ·
          refine ⟨16283300347066034322190603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21711067129421379096254137 16283300347066034322190603)
          ·
            refine ⟨24424950520599051483285905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16283300347066034322190603 24424950520599051483285905)
            ·
              refine ⟨18318712890449288612464429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24424950520599051483285905 18318712890449288612464429)
              ·
                refine ⟨6869517333918483229674161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18318712890449288612464429 6869517333918483229674161)
                ·
                  refine ⟨5152138000438862422255621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869517333918483229674161 5152138000438862422255621)
                  ·
                    refine ⟨966025875082286704172929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152138000438862422255621 966025875082286704172929)
                    ·
                      rfl

theorem cell23_5643986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_5643986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643986 prefixEnd_5643986 := by exact prefixLift 5643986
  have htrace : WordTrace (prefixWord ++ tailWord_5643986) baseStart_5643986 baseEnd_5643986 := by
    simpa [prefixWord, tailWord_5643986, baseEnd_5643986] using wordTrace_append hprefix tailTrace_5643986
  have hstable : (prefixWord ++ tailWord_5643986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643986).length < 2 ^ (prefixWord ++ tailWord_5643986).sum := by decide
  have hdescent : baseEnd_5643986 < baseStart_5643986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5643997 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5643997 : Nat := 118140960795 + 5643997 * 2 ^ 59
def prefixEnd_5643997 : Nat := 4983230072969 + 3 ^ 40 * 5643997 * 2
def baseEnd_5643997 : Nat := 2898083273534059569481237

theorem tailTrace_5643997 : CollatzResearch.WordTrace tailWord_5643997 prefixEnd_5643997 2898083273534059569481237 := by
  unfold tailWord_5643997
  simp only [CollatzResearch.WordTrace]
  refine ⟨205853482133770261791282245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137235654755846841194188163 205853482133770261791282245)
  ·
    refine ⟨38597527900081924085865421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205853482133770261791282245 38597527900081924085865421)
    ·
      refine ⟨14474072962530721532199533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38597527900081924085865421 14474072962530721532199533)
      ·
        refine ⟨5427777360949020574574825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14474072962530721532199533 5427777360949020574574825)
        ·
          refine ⟨4070833020711765430931119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5427777360949020574574825 4070833020711765430931119)
          ·
            refine ⟨6106249531067648146396679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070833020711765430931119 6106249531067648146396679)
            ·
              refine ⟨9159374296601472219595019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106249531067648146396679 9159374296601472219595019)
              ·
                refine ⟨13739061444902208329392529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159374296601472219595019 13739061444902208329392529)
                ·
                  refine ⟨10304296083676656247044397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739061444902208329392529 10304296083676656247044397)
                  ·
                    refine ⟨3864111031378746092641649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10304296083676656247044397 3864111031378746092641649)
                    ·
                      refine ⟨2898083273534059569481237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864111031378746092641649 2898083273534059569481237)
                      ·
                        rfl

theorem cell23_5643997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5643997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5643997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5643997 prefixEnd_5643997 := by exact prefixLift 5643997
  have htrace : WordTrace (prefixWord ++ tailWord_5643997) baseStart_5643997 baseEnd_5643997 := by
    simpa [prefixWord, tailWord_5643997, baseEnd_5643997] using wordTrace_append hprefix tailTrace_5643997
  have hstable : (prefixWord ++ tailWord_5643997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5643997).length < 2 ^ (prefixWord ++ tailWord_5643997).sum := by decide
  have hdescent : baseEnd_5643997 < baseStart_5643997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5643997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644009 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_5644009 : Nat := 118140960795 + 5644009 * 2 ^ 59
def prefixEnd_5644009 : Nat := 4983230072969 + 3 ^ 40 * 5644009 * 2
def baseEnd_5644009 : Nat := 2898089435301913522531181

theorem tailTrace_5644009 : CollatzResearch.WordTrace tailWord_5644009 prefixEnd_5644009 2898089435301913522531181 := by
  unfold tailWord_5644009
  simp only [CollatzResearch.WordTrace]
  refine ⟨205853919809726787840719081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137235946539817858560479387 205853919809726787840719081)
  ·
    refine ⟨154390439857295090880539311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205853919809726787840719081 154390439857295090880539311)
    ·
      refine ⟨231585659785942636320808967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154390439857295090880539311 231585659785942636320808967)
      ·
        refine ⟨347378489678913954481213451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231585659785942636320808967 347378489678913954481213451)
        ·
          refine ⟨521067734518370931721820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347378489678913954481213451 521067734518370931721820177)
          ·
            refine ⟨390800800888778198791365133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521067734518370931721820177 390800800888778198791365133)
            ·
              refine ⟨146550300333291824546761925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390800800888778198791365133 146550300333291824546761925)
              ·
                refine ⟨27478181312492217102517861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146550300333291824546761925 27478181312492217102517861)
                ·
                  refine ⟨5152158996092290706722099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27478181312492217102517861 5152158996092290706722099)
                  ·
                    refine ⟨7728238494138436060083149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5152158996092290706722099 7728238494138436060083149)
                    ·
                      refine ⟨2898089435301913522531181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728238494138436060083149 2898089435301913522531181)
                      ·
                        rfl

theorem cell23_5644009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_5644009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644009 prefixEnd_5644009 := by exact prefixLift 5644009
  have htrace : WordTrace (prefixWord ++ tailWord_5644009) baseStart_5644009 baseEnd_5644009 := by
    simpa [prefixWord, tailWord_5644009, baseEnd_5644009] using wordTrace_append hprefix tailTrace_5644009
  have hstable : (prefixWord ++ tailWord_5644009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644009).length < 2 ^ (prefixWord ++ tailWord_5644009).sum := by decide
  have hdescent : baseEnd_5644009 < baseStart_5644009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644013 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5644013 : Nat := 118140960795 + 5644013 * 2 ^ 59
def prefixEnd_5644013 : Nat := 4983230072969 + 3 ^ 40 * 5644013 * 2
def baseEnd_5644013 : Nat := 2898091489224531506881163

theorem tailTrace_5644013 : CollatzResearch.WordTrace tailWord_5644013 prefixEnd_5644013 2898091489224531506881163 := by
  unfold tailWord_5644013
  simp only [CollatzResearch.WordTrace]
  refine ⟨205854065701712296523864693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137236043801141531015909795 205854065701712296523864693)
  ·
    refine ⟨19298818659535527799112315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205854065701712296523864693 19298818659535527799112315)
    ·
      refine ⟨28948227989303291698668473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298818659535527799112315 28948227989303291698668473)
      ·
        refine ⟨21711170991977468774001355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28948227989303291698668473 21711170991977468774001355)
        ·
          refine ⟨32566756487966203161002033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21711170991977468774001355 32566756487966203161002033)
          ·
            refine ⟨24425067365974652370751525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32566756487966203161002033 24425067365974652370751525)
            ·
              refine ⟨4579700131120247319515911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24425067365974652370751525 4579700131120247319515911)
              ·
                refine ⟨6869550196680370979273867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579700131120247319515911 6869550196680370979273867)
                ·
                  refine ⟨10304325295020556468910801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869550196680370979273867 10304325295020556468910801)
                  ·
                    refine ⟨7728243971265417351683101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10304325295020556468910801 7728243971265417351683101)
                    ·
                      refine ⟨2898091489224531506881163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728243971265417351683101 2898091489224531506881163)
                      ·
                        rfl

theorem cell23_5644013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5644013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644013 prefixEnd_5644013 := by exact prefixLift 5644013
  have htrace : WordTrace (prefixWord ++ tailWord_5644013) baseStart_5644013 baseEnd_5644013 := by
    simpa [prefixWord, tailWord_5644013, baseEnd_5644013] using wordTrace_append hprefix tailTrace_5644013
  have hstable : (prefixWord ++ tailWord_5644013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644013).length < 2 ^ (prefixWord ++ tailWord_5644013).sum := by decide
  have hdescent : baseEnd_5644013 < baseStart_5644013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644020 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5644020 : Nat := 118140960795 + 5644020 * 2 ^ 59
def prefixEnd_5644020 : Nat := 4983230072969 + 3 ^ 40 * 5644020 * 2
def baseEnd_5644020 : Nat := 966031694529704326497877

theorem tailTrace_5644020 : CollatzResearch.WordTrace tailWord_5644020 prefixEnd_5644020 966031694529704326497877 := by
  unfold tailWord_5644020
  simp only [CollatzResearch.WordTrace]
  refine ⟨102927160506343468359684757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137236214008457957812913009 102927160506343468359684757)
  ·
    refine ⟨4824710648734850079360223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102927160506343468359684757 4824710648734850079360223)
    ·
      refine ⟨7237065973102275119040335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824710648734850079360223 7237065973102275119040335)
      ·
        refine ⟨10855598959653412678560503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237065973102275119040335 10855598959653412678560503)
        ·
          refine ⟨16283398439480119017840755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10855598959653412678560503 16283398439480119017840755)
          ·
            refine ⟨24425097659220178526761133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16283398439480119017840755 24425097659220178526761133)
            ·
              refine ⟨9159411622207566947535425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24425097659220178526761133 9159411622207566947535425)
              ·
                refine ⟨6869558716655675210651569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159411622207566947535425 6869558716655675210651569)
                ·
                  refine ⟨5152169037491756407988677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869558716655675210651569 5152169037491756407988677)
                  ·
                    refine ⟨966031694529704326497877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152169037491756407988677 966031694529704326497877)
                    ·
                      rfl

theorem cell23_5644020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5644020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644020 prefixEnd_5644020 := by exact prefixLift 5644020
  have htrace : WordTrace (prefixWord ++ tailWord_5644020) baseStart_5644020 baseEnd_5644020 := by
    simpa [prefixWord, tailWord_5644020, baseEnd_5644020] using wordTrace_append hprefix tailTrace_5644020
  have hstable : (prefixWord ++ tailWord_5644020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644020).length < 2 ^ (prefixWord ++ tailWord_5644020).sum := by decide
  have hdescent : baseEnd_5644020 < baseStart_5644020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644053 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_5644053 : Nat := 118140960795 + 5644053 * 2 ^ 59
def prefixEnd_5644053 : Nat := 4983230072969 + 3 ^ 40 * 5644053 * 2
def baseEnd_5644053 : Nat := 2898112028450711350380979

theorem tailTrace_5644053 : CollatzResearch.WordTrace tailWord_5644053 prefixEnd_5644053 2898112028450711350380979 := by
  unfold tailWord_5644053
  simp only [CollatzResearch.WordTrace]
  refine ⟨205855524621567383355320813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137237016414378255570213875 205855524621567383355320813)
  ·
    refine ⟨77195821733087768758245305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205855524621567383355320813 77195821733087768758245305)
    ·
      refine ⟨57896866299815826568683979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77195821733087768758245305 57896866299815826568683979)
      ·
        refine ⟨86845299449723739853025969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57896866299815826568683979 86845299449723739853025969)
        ·
          refine ⟨65133974587292804889769477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86845299449723739853025969 65133974587292804889769477)
          ·
            refine ⟨12212620235117400916831777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65133974587292804889769477 12212620235117400916831777)
            ·
              refine ⟨9159465176338050687623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12212620235117400916831777 9159465176338050687623833)
              ·
                refine ⟨6869598882253538015717875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159465176338050687623833 6869598882253538015717875)
                ·
                  refine ⟨10304398323380307023576813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869598882253538015717875 10304398323380307023576813)
                  ·
                    refine ⟨3864149371267615133841305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10304398323380307023576813 3864149371267615133841305)
                    ·
                      refine ⟨2898112028450711350380979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864149371267615133841305 2898112028450711350380979)
                      ·
                        rfl

theorem cell23_5644053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_5644053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644053 prefixEnd_5644053 := by exact prefixLift 5644053
  have htrace : WordTrace (prefixWord ++ tailWord_5644053) baseStart_5644053 baseEnd_5644053 := by
    simpa [prefixWord, tailWord_5644053, baseEnd_5644053] using wordTrace_append hprefix tailTrace_5644053
  have hstable : (prefixWord ++ tailWord_5644053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644053).length < 2 ^ (prefixWord ++ tailWord_5644053).sum := by decide
  have hdescent : baseEnd_5644053 < baseStart_5644053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644066 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_5644066 : Nat := 118140960795 + 5644066 * 2 ^ 59
def prefixEnd_5644066 : Nat := 4983230072969 + 3 ^ 40 * 5644066 * 2
def baseEnd_5644066 : Nat := 2898118703699219799518419

theorem tailTrace_5644066 : CollatzResearch.WordTrace tailWord_5644066 prefixEnd_5644066 2898118703699219799518419 := by
  unfold tailWord_5644066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51463999692630071643886013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137237332513680191050362701 51463999692630071643886013)
  ·
    refine ⟨19298999884736276866457255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51463999692630071643886013 19298999884736276866457255)
    ·
      refine ⟨28948499827104415299685883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298999884736276866457255 28948499827104415299685883)
      ·
        refine ⟨43422749740656622949528825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28948499827104415299685883 43422749740656622949528825)
        ·
          refine ⟨32567062305492467212146619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43422749740656622949528825 32567062305492467212146619)
          ·
            refine ⟨48850593458238700818219929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32567062305492467212146619 48850593458238700818219929)
            ·
              refine ⟨36637945093679025613664947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48850593458238700818219929 36637945093679025613664947)
              ·
                refine ⟨54956917640518538420497421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36637945093679025613664947 54956917640518538420497421)
                ·
                  refine ⟨20608844115194451907686533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54956917640518538420497421 20608844115194451907686533)
                  ·
                    refine ⟨3864158271598959732691225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20608844115194451907686533 3864158271598959732691225)
                    ·
                      refine ⟨2898118703699219799518419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864158271598959732691225 2898118703699219799518419)
                      ·
                        rfl

theorem cell23_5644066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_5644066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644066 prefixEnd_5644066 := by exact prefixLift 5644066
  have htrace : WordTrace (prefixWord ++ tailWord_5644066) baseStart_5644066 baseEnd_5644066 := by
    simpa [prefixWord, tailWord_5644066, baseEnd_5644066] using wordTrace_append hprefix tailTrace_5644066
  have hstable : (prefixWord ++ tailWord_5644066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644066).length < 2 ^ (prefixWord ++ tailWord_5644066).sum := by decide
  have hdescent : baseEnd_5644066 < baseStart_5644066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644069 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_5644069 : Nat := 118140960795 + 5644069 * 2 ^ 59
def prefixEnd_5644069 : Nat := 4983230072969 + 3 ^ 40 * 5644069 * 2
def baseEnd_5644069 : Nat := 2898120244141183287780905

theorem tailTrace_5644069 : CollatzResearch.WordTrace tailWord_5644069 prefixEnd_5644069 2898120244141183287780905 := by
  unfold tailWord_5644069
  simp only [CollatzResearch.WordTrace]
  refine ⟨205856108189509418087903261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137237405459672945391935507 205856108189509418087903261)
  ·
    refine ⟨77196040571066031782963723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205856108189509418087903261 77196040571066031782963723)
    ·
      refine ⟨115794060856599047674445585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77196040571066031782963723 115794060856599047674445585)
      ·
        refine ⟨86845545642449285755834189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115794060856599047674445585 86845545642449285755834189)
        ·
          refine ⟨32567079615918482158437821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86845545642449285755834189 32567079615918482158437821)
          ·
            refine ⟨12212654855969430809414183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32567079615918482158437821 12212654855969430809414183)
            ·
              refine ⟨18318982283954146214121275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12212654855969430809414183 18318982283954146214121275)
              ·
                refine ⟨27478473425931219321181913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18318982283954146214121275 27478473425931219321181913)
                ·
                  refine ⟨20608855069448414490886435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27478473425931219321181913 20608855069448414490886435)
                  ·
                    refine ⟨30913282604172621736329653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20608855069448414490886435 30913282604172621736329653)
                    ·
                      refine ⟨2898120244141183287780905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30913282604172621736329653 2898120244141183287780905)
                      ·
                        rfl

theorem cell23_5644069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_5644069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644069 prefixEnd_5644069 := by exact prefixLift 5644069
  have htrace : WordTrace (prefixWord ++ tailWord_5644069) baseStart_5644069 baseEnd_5644069 := by
    simpa [prefixWord, tailWord_5644069, baseEnd_5644069] using wordTrace_append hprefix tailTrace_5644069
  have hstable : (prefixWord ++ tailWord_5644069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644069).length < 2 ^ (prefixWord ++ tailWord_5644069).sum := by decide
  have hdescent : baseEnd_5644069 < baseStart_5644069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644112 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_5644112 : Nat := 118140960795 + 5644112 * 2 ^ 59
def prefixEnd_5644112 : Nat := 4983230072969 + 3 ^ 40 * 5644112 * 2
def baseEnd_5644112 : Nat := 2898142323809326619543207

theorem tailTrace_5644112 : CollatzResearch.WordTrace tailWord_5644112 prefixEnd_5644112 2898142323809326619543207 := by
  unfold tailWord_5644112
  simp only [CollatzResearch.WordTrace]
  refine ⟨102928838264176818215859295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137238451018902424287812393 102928838264176818215859295)
  ·
    refine ⟨154393257396265227323788943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102928838264176818215859295 154393257396265227323788943)
    ·
      refine ⟨231589886094397840985683415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154393257396265227323788943 231589886094397840985683415)
      ·
        refine ⟨347384829141596761478525123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231589886094397840985683415 347384829141596761478525123)
        ·
          refine ⟨521077243712395142217787685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347384829141596761478525123 521077243712395142217787685)
          ·
            refine ⟨97701983196074089165835191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 521077243712395142217787685 97701983196074089165835191)
            ·
              refine ⟨146552974794111133748752787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97701983196074089165835191 146552974794111133748752787)
              ·
                refine ⟨219829462191166700623129181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146552974794111133748752787 219829462191166700623129181)
                ·
                  refine ⟨82436048321687512733673443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219829462191166700623129181 82436048321687512733673443)
                  ·
                    refine ⟨123654072482531269100510165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82436048321687512733673443 123654072482531269100510165)
                    ·
                      refine ⟨2898142323809326619543207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123654072482531269100510165 2898142323809326619543207)
                      ·
                        rfl

theorem cell23_5644112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_5644112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644112 prefixEnd_5644112 := by exact prefixLift 5644112
  have htrace : WordTrace (prefixWord ++ tailWord_5644112) baseStart_5644112 baseEnd_5644112 := by
    simpa [prefixWord, tailWord_5644112, baseEnd_5644112] using wordTrace_append hprefix tailTrace_5644112
  have hstable : (prefixWord ++ tailWord_5644112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644112).length < 2 ^ (prefixWord ++ tailWord_5644112).sum := by decide
  have hdescent : baseEnd_5644112 < baseStart_5644112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644159 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_5644159 : Nat := 118140960795 + 5644159 * 2 ^ 59
def prefixEnd_5644159 : Nat := 4983230072969 + 3 ^ 40 * 5644159 * 2
def baseEnd_5644159 : Nat := 2898166457400087935655491

theorem tailTrace_5644159 : CollatzResearch.WordTrace tailWord_5644159 prefixEnd_5644159 2898166457400087935655491 := by
  unfold tailWord_5644159
  simp only [CollatzResearch.WordTrace]
  refine ⟨205859390759183363458679531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137239593839455575639119687 205859390759183363458679531)
  ·
    refine ⟨308789086138775045188019297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205859390759183363458679531 308789086138775045188019297)
    ·
      refine ⟨231591814604081283891014473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308789086138775045188019297 231591814604081283891014473)
      ·
        refine ⟨173693860953060962918260855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231591814604081283891014473 173693860953060962918260855)
        ·
          refine ⟨260540791429591444377391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173693860953060962918260855 260540791429591444377391283)
          ·
            refine ⟨390811187144387166566086925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260540791429591444377391283 390811187144387166566086925)
            ·
              refine ⟨146554195179145187462282597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390811187144387166566086925 146554195179145187462282597)
              ·
                refine ⟨27478911596089722649177987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146554195179145187462282597 27478911596089722649177987)
                ·
                  refine ⟨41218367394134583973766981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27478911596089722649177987 41218367394134583973766981)
                  ·
                    refine ⟨7728443886400234495081309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41218367394134583973766981 7728443886400234495081309)
                    ·
                      refine ⟨2898166457400087935655491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728443886400234495081309 2898166457400087935655491)
                      ·
                        rfl

theorem cell23_5644159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_5644159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644159 prefixEnd_5644159 := by exact prefixLift 5644159
  have htrace : WordTrace (prefixWord ++ tailWord_5644159) baseStart_5644159 baseEnd_5644159 := by
    simpa [prefixWord, tailWord_5644159, baseEnd_5644159] using wordTrace_append hprefix tailTrace_5644159
  have hstable : (prefixWord ++ tailWord_5644159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644159).length < 2 ^ (prefixWord ++ tailWord_5644159).sum := by decide
  have hdescent : baseEnd_5644159 < baseStart_5644159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644170 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_5644170 : Nat := 118140960795 + 5644170 * 2 ^ 59
def prefixEnd_5644170 : Nat := 4983230072969 + 3 ^ 40 * 5644170 * 2
def baseEnd_5644170 : Nat := 966057368562429130872647

theorem tailTrace_5644170 : CollatzResearch.WordTrace tailWord_5644170 prefixEnd_5644170 966057368562429130872647 := by
  unfold tailWord_5644170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51464947990535878084332491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137239861308095674891553309 51464947990535878084332491)
  ·
    refine ⟨77197421985803817126498737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51464947990535878084332491 77197421985803817126498737)
    ·
      refine ⟨57898066489352862844874053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77197421985803817126498737 57898066489352862844874053)
      ·
        refine ⟨10855887466753661783413885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57898066489352862844874053 10855887466753661783413885)
        ·
          refine ⟨4070957800032623168780207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10855887466753661783413885 4070957800032623168780207)
          ·
            refine ⟨6106436700048934753170311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070957800032623168780207 6106436700048934753170311)
            ·
              refine ⟨9159655050073402129755467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106436700048934753170311 9159655050073402129755467)
              ·
                refine ⟨13739482575110103194633201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159655050073402129755467 13739482575110103194633201)
                ·
                  refine ⟨10304611931332577395974901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739482575110103194633201 10304611931332577395974901)
                  ·
                    refine ⟨966057368562429130872647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10304611931332577395974901 966057368562429130872647)
                    ·
                      rfl

theorem cell23_5644170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_5644170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644170 prefixEnd_5644170 := by exact prefixLift 5644170
  have htrace : WordTrace (prefixWord ++ tailWord_5644170) baseStart_5644170 baseEnd_5644170 := by
    simpa [prefixWord, tailWord_5644170, baseEnd_5644170] using wordTrace_append hprefix tailTrace_5644170
  have hstable : (prefixWord ++ tailWord_5644170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644170).length < 2 ^ (prefixWord ++ tailWord_5644170).sum := by decide
  have hdescent : baseEnd_5644170 < baseStart_5644170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644183 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 1, 4]
def baseStart_5644183 : Nat := 118140960795 + 5644183 * 2 ^ 59
def prefixEnd_5644183 : Nat := 4983230072969 + 3 ^ 40 * 5644183 * 2
def baseEnd_5644183 : Nat := 966059593645265280585127

theorem tailTrace_5644183 : CollatzResearch.WordTrace tailWord_5644183 prefixEnd_5644183 966059593645265280585127 := by
  unfold tailWord_5644183
  simp only [CollatzResearch.WordTrace]
  refine ⟨205860266111096415557553203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137240177407397610371702135 205860266111096415557553203)
  ·
    refine ⟨308790399166644623336329805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205860266111096415557553203 308790399166644623336329805)
    ·
      refine ⟨115796399687491733751123677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308790399166644623336329805 115796399687491733751123677)
      ·
        refine ⟨43423649882809400156671379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115796399687491733751123677 43423649882809400156671379)
        ·
          refine ⟨65135474824214100235007069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43423649882809400156671379 65135474824214100235007069)
          ·
            refine ⟨24425803059080287588127651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65135474824214100235007069 24425803059080287588127651)
            ·
              refine ⟨36638704588620431382191477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24425803059080287588127651 36638704588620431382191477)
              ·
                refine ⟨3434878555183165442080451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36638704588620431382191477 3434878555183165442080451)
                ·
                  refine ⟨5152317832774748163120677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434878555183165442080451 5152317832774748163120677)
                  ·
                    refine ⟨966059593645265280585127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152317832774748163120677 966059593645265280585127)
                    ·
                      rfl

theorem cell23_5644183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_5644183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644183 prefixEnd_5644183 := by exact prefixLift 5644183
  have htrace : WordTrace (prefixWord ++ tailWord_5644183) baseStart_5644183 baseEnd_5644183 := by
    simpa [prefixWord, tailWord_5644183, baseEnd_5644183] using wordTrace_append hprefix tailTrace_5644183
  have hstable : (prefixWord ++ tailWord_5644183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644183).length < 2 ^ (prefixWord ++ tailWord_5644183).sum := by decide
  have hdescent : baseEnd_5644183 < baseStart_5644183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644196 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 6]
def baseStart_5644196 : Nat := 118140960795 + 5644196 * 2 ^ 59
def prefixEnd_5644196 : Nat := 4983230072969 + 3 ^ 40 * 5644196 * 2
def baseEnd_5644196 : Nat := 322020606242700476765869

theorem tailTrace_5644196 : CollatzResearch.WordTrace tailWord_5644196 prefixEnd_5644196 322020606242700476765869 := by
  unfold tailWord_5644196
  simp only [CollatzResearch.WordTrace]
  refine ⟨102930370130024659388888221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137240493506699545851850961 102930370130024659388888221)
  ·
    refine ⟨38598888798759247270833083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102930370130024659388888221 38598888798759247270833083)
    ·
      refine ⟨57898333198138870906249625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38598888798759247270833083 57898333198138870906249625)
      ·
        refine ⟨43423749898604153179687219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57898333198138870906249625 43423749898604153179687219)
        ·
          refine ⟨65135624847906229769530829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43423749898604153179687219 65135624847906229769530829)
          ·
            refine ⟨24425859317964836163574061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65135624847906229769530829 24425859317964836163574061)
            ·
              refine ⟨9159697244236813561340273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24425859317964836163574061 9159697244236813561340273)
              ·
                refine ⟨6869772933177610171005205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159697244236813561340273 6869772933177610171005205)
                ·
                  refine ⟨322020606242700476765869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6869772933177610171005205 322020606242700476765869)
                  ·
                    rfl

theorem cell23_5644196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_5644196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644196 prefixEnd_5644196 := by exact prefixLift 5644196
  have htrace : WordTrace (prefixWord ++ tailWord_5644196) baseStart_5644196 baseEnd_5644196 := by
    simpa [prefixWord, tailWord_5644196, baseEnd_5644196] using wordTrace_append hprefix tailTrace_5644196
  have hstable : (prefixWord ++ tailWord_5644196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644196).length < 2 ^ (prefixWord ++ tailWord_5644196).sum := by decide
  have hdescent : baseEnd_5644196 < baseStart_5644196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644213 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 6]
def baseStart_5644213 : Nat := 118140960795 + 5644213 * 2 ^ 59
def prefixEnd_5644213 : Nat := 4983230072969 + 3 ^ 40 * 5644213 * 2
def baseEnd_5644213 : Nat := 322021576150603413820027

theorem tailTrace_5644213 : CollatzResearch.WordTrace tailWord_5644213 prefixEnd_5644213 322021576150603413820027 := by
  unfold tailWord_5644213
  simp only [CollatzResearch.WordTrace]
  refine ⟨205861360300987730681145293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137240906867325153787430195 205861360300987730681145293)
  ·
    refine ⟨77198010112870399005429485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205861360300987730681145293 77198010112870399005429485)
    ·
      refine ⟨28949253792326399627036057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77198010112870399005429485 28949253792326399627036057)
      ·
        refine ⟨21711940344244799720277043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28949253792326399627036057 21711940344244799720277043)
        ·
          refine ⟨32567910516367199580415565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21711940344244799720277043 32567910516367199580415565)
          ·
            refine ⟨12212966443637699842655837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32567910516367199580415565 12212966443637699842655837)
            ·
              refine ⟨4579862416364137440995939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12212966443637699842655837 4579862416364137440995939)
              ·
                refine ⟨6869793624546206161493909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579862416364137440995939 6869793624546206161493909)
                ·
                  refine ⟨322021576150603413820027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6869793624546206161493909 322021576150603413820027)
                  ·
                    rfl

theorem cell23_5644213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_5644213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644213 prefixEnd_5644213 := by exact prefixLift 5644213
  have htrace : WordTrace (prefixWord ++ tailWord_5644213) baseStart_5644213 baseEnd_5644213 := by
    simpa [prefixWord, tailWord_5644213, baseEnd_5644213] using wordTrace_append hprefix tailTrace_5644213
  have hstable : (prefixWord ++ tailWord_5644213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644213).length < 2 ^ (prefixWord ++ tailWord_5644213).sum := by decide
  have hdescent : baseEnd_5644213 < baseStart_5644213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644216 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_5644216 : Nat := 118140960795 + 5644216 * 2 ^ 59
def prefixEnd_5644216 : Nat := 4983230072969 + 3 ^ 40 * 5644216 * 2
def baseEnd_5644216 : Nat := 2898195725797394212642729

theorem tailTrace_5644216 : CollatzResearch.WordTrace tailWord_5644216 prefixEnd_5644216 2898195725797394212642729 := by
  unfold tailWord_5644216
  simp only [CollatzResearch.WordTrace]
  refine ⟨102930734859988431096752251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137240979813317908129003001 102930734859988431096752251)
  ·
    refine ⟨154396102289982646645128377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102930734859988431096752251 154396102289982646645128377)
    ·
      refine ⟨115797076717486984983846283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154396102289982646645128377 115797076717486984983846283)
      ·
        refine ⟨173695615076230477475769425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115797076717486984983846283 173695615076230477475769425)
        ·
          refine ⟨130271711307172858106827069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173695615076230477475769425 130271711307172858106827069)
          ·
            refine ⟨48851891740189821790060151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130271711307172858106827069 48851891740189821790060151)
            ·
              refine ⟨73277837610284732685090227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48851891740189821790060151 73277837610284732685090227)
              ·
                refine ⟨109916756415427099027635341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73277837610284732685090227 109916756415427099027635341)
                ·
                  refine ⟨41218783655785162135363253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109916756415427099027635341 41218783655785162135363253)
                  ·
                    refine ⟨3864260967729858950190305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41218783655785162135363253 3864260967729858950190305)
                    ·
                      refine ⟨2898195725797394212642729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864260967729858950190305 2898195725797394212642729)
                      ·
                        rfl

theorem cell23_5644216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_5644216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644216 prefixEnd_5644216 := by exact prefixLift 5644216
  have htrace : WordTrace (prefixWord ++ tailWord_5644216) baseStart_5644216 baseEnd_5644216 := by
    simpa [prefixWord, tailWord_5644216, baseEnd_5644216] using wordTrace_append hprefix tailTrace_5644216
  have hstable : (prefixWord ++ tailWord_5644216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644216).length < 2 ^ (prefixWord ++ tailWord_5644216).sum := by decide
  have hdescent : baseEnd_5644216 < baseStart_5644216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644239 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 6]
def baseStart_5644239 : Nat := 118140960795 + 5644239 * 2 ^ 59
def prefixEnd_5644239 : Nat := 4983230072969 + 3 ^ 40 * 5644239 * 2
def baseEnd_5644239 : Nat := 966069178617482540885041

theorem tailTrace_5644239 : CollatzResearch.WordTrace tailWord_5644239 prefixEnd_5644239 966069178617482540885041 := by
  unfold tailWord_5644239
  simp only [CollatzResearch.WordTrace]
  refine ⟨205862308598893537121591771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137241539065929024747727847 205862308598893537121591771)
  ·
    refine ⟨308793462898340305682387657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205862308598893537121591771 308793462898340305682387657)
    ·
      refine ⟨231595097173755229261790743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308793462898340305682387657 231595097173755229261790743)
      ·
        refine ⟨347392645760632843892686115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231595097173755229261790743 347392645760632843892686115)
        ·
          refine ⟨521088968640949265839029173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347392645760632843892686115 521088968640949265839029173)
          ·
            refine ⟨48852090810088993672408985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 521088968640949265839029173 48852090810088993672408985)
            ·
              refine ⟨36639068107566745254306739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48852090810088993672408985 36639068107566745254306739)
              ·
                refine ⟨54958602161350117881460109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36639068107566745254306739 54958602161350117881460109)
                ·
                  refine ⟨20609475810506294205547541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54958602161350117881460109 20609475810506294205547541)
                  ·
                    refine ⟨966069178617482540885041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20609475810506294205547541 966069178617482540885041)
                    ·
                      rfl

theorem cell23_5644239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_5644239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644239 prefixEnd_5644239 := by exact prefixLift 5644239
  have htrace : WordTrace (prefixWord ++ tailWord_5644239) baseStart_5644239 baseEnd_5644239 := by
    simpa [prefixWord, tailWord_5644239, baseEnd_5644239] using wordTrace_append hprefix tailTrace_5644239
  have hstable : (prefixWord ++ tailWord_5644239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644239).length < 2 ^ (prefixWord ++ tailWord_5644239).sum := by decide
  have hdescent : baseEnd_5644239 < baseStart_5644239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644240 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 1, 1, 3]
def baseStart_5644240 : Nat := 118140960795 + 5644240 * 2 ^ 59
def prefixEnd_5644240 : Nat := 4983230072969 + 3 ^ 40 * 5644240 * 2
def baseEnd_5644240 : Nat := 2898208049333102118742619

theorem tailTrace_5644240 : CollatzResearch.WordTrace tailWord_5644240 prefixEnd_5644240 2898208049333102118742619 := by
  unfold tailWord_5644240
  simp only [CollatzResearch.WordTrace]
  refine ⟨102931172535944957146189087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137241563381259942861585449 102931172535944957146189087)
  ·
    refine ⟨154396758803917435719283631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102931172535944957146189087 154396758803917435719283631)
    ·
      refine ⟨231595138205876153578925447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154396758803917435719283631 231595138205876153578925447)
      ·
        refine ⟨347392707308814230368388171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231595138205876153578925447 347392707308814230368388171)
        ·
          refine ⟨521089060963221345552582257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347392707308814230368388171 521089060963221345552582257)
          ·
            refine ⟨390816795722416009164436693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521089060963221345552582257 390816795722416009164436693)
            ·
              refine ⟨9159768649744125214791485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 390816795722416009164436693 9159768649744125214791485)
              ·
                refine ⟨3434913243654046955546807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9159768649744125214791485 3434913243654046955546807)
                ·
                  refine ⟨5152369865481070433320211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434913243654046955546807 5152369865481070433320211)
                  ·
                    refine ⟨7728554798221605649980317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5152369865481070433320211 7728554798221605649980317)
                    ·
                      refine ⟨2898208049333102118742619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728554798221605649980317 2898208049333102118742619)
                      ·
                        rfl

theorem cell23_5644240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 1, 3].length) (baseStart_5644240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644240 prefixEnd_5644240 := by exact prefixLift 5644240
  have htrace : WordTrace (prefixWord ++ tailWord_5644240) baseStart_5644240 baseEnd_5644240 := by
    simpa [prefixWord, tailWord_5644240, baseEnd_5644240] using wordTrace_append hprefix tailTrace_5644240
  have hstable : (prefixWord ++ tailWord_5644240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644240).length < 2 ^ (prefixWord ++ tailWord_5644240).sum := by decide
  have hdescent : baseEnd_5644240 < baseStart_5644240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644250 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2]
def baseStart_5644250 : Nat := 118140960795 + 5644250 * 2 ^ 59
def prefixEnd_5644250 : Nat := 4983230072969 + 3 ^ 40 * 5644250 * 2
def baseEnd_5644250 : Nat := 2898213184139647079617573

theorem tailTrace_5644250 : CollatzResearch.WordTrace tailWord_5644250 prefixEnd_5644250 2898213184139647079617573 := by
  unfold tailWord_5644250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51465677450463421500060551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137241806534569124000161469 51465677450463421500060551)
  ·
    refine ⟨77198516175695132250090827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51465677450463421500060551 77198516175695132250090827)
    ·
      refine ⟨115797774263542698375136241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77198516175695132250090827 115797774263542698375136241)
      ·
        refine ⟨86848330697657023781352181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115797774263542698375136241 86848330697657023781352181)
        ·
          refine ⟨8142031002905345979501767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86848330697657023781352181 8142031002905345979501767)
          ·
            refine ⟨12213046504358018969252651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142031002905345979501767 12213046504358018969252651)
            ·
              refine ⟨18319569756537028453878977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213046504358018969252651 18319569756537028453878977)
              ·
                refine ⟨13739677317402771340409233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18319569756537028453878977 13739677317402771340409233)
                ·
                  refine ⟨10304757988052078505306925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739677317402771340409233 10304757988052078505306925)
                  ·
                    refine ⟨3864284245519529439490097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10304757988052078505306925 3864284245519529439490097)
                    ·
                      refine ⟨2898213184139647079617573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864284245519529439490097 2898213184139647079617573)
                      ·
                        rfl

theorem cell23_5644250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_5644250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644250 prefixEnd_5644250 := by exact prefixLift 5644250
  have htrace : WordTrace (prefixWord ++ tailWord_5644250) baseStart_5644250 baseEnd_5644250 := by
    simpa [prefixWord, tailWord_5644250, baseEnd_5644250] using wordTrace_append hprefix tailTrace_5644250
  have hstable : (prefixWord ++ tailWord_5644250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644250).length < 2 ^ (prefixWord ++ tailWord_5644250).sum := by decide
  have hdescent : baseEnd_5644250 < baseStart_5644250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644266 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_5644266 : Nat := 118140960795 + 5644266 * 2 ^ 59
def prefixEnd_5644266 : Nat := 4983230072969 + 3 ^ 40 * 5644266 * 2
def baseEnd_5644266 : Nat := 2898221399830119017017499

theorem tailTrace_5644266 : CollatzResearch.WordTrace tailWord_5644266 prefixEnd_5644266 2898221399830119017017499 := by
  unfold tailWord_5644266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51465823342448930183206163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137242195579863813821883101 51465823342448930183206163)
  ·
    refine ⟨77198735013673395274809245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51465823342448930183206163 77198735013673395274809245)
    ·
      refine ⟨28949525630127523228053467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77198735013673395274809245 28949525630127523228053467)
      ·
        refine ⟨43424288445191284842080201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28949525630127523228053467 43424288445191284842080201)
        ·
          refine ⟨32568216333893463631560151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43424288445191284842080201 32568216333893463631560151)
          ·
            refine ⟨48852324500840195447340227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32568216333893463631560151 48852324500840195447340227)
            ·
              refine ⟨73278486751260293171010341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48852324500840195447340227 73278486751260293171010341)
              ·
                refine ⟨13739716265861304969564439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73278486751260293171010341 13739716265861304969564439)
                ·
                  refine ⟨20609574398791957454346659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13739716265861304969564439 20609574398791957454346659)
                  ·
                    refine ⟨30914361598187936181519989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20609574398791957454346659 30914361598187936181519989)
                    ·
                      refine ⟨2898221399830119017017499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30914361598187936181519989 2898221399830119017017499)
                      ·
                        rfl

theorem cell23_5644266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_5644266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644266 prefixEnd_5644266 := by exact prefixLift 5644266
  have htrace : WordTrace (prefixWord ++ tailWord_5644266) baseStart_5644266 baseEnd_5644266 := by
    simpa [prefixWord, tailWord_5644266, baseEnd_5644266] using wordTrace_append hprefix tailTrace_5644266
  have hstable : (prefixWord ++ tailWord_5644266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644266).length < 2 ^ (prefixWord ++ tailWord_5644266).sum := by decide
  have hdescent : baseEnd_5644266 < baseStart_5644266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644283 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 3]
def baseStart_5644283 : Nat := 118140960795 + 5644283 * 2 ^ 59
def prefixEnd_5644283 : Nat := 4983230072969 + 3 ^ 40 * 5644283 * 2
def baseEnd_5644283 : Nat := 2898230129001245450504921

theorem tailTrace_5644283 : CollatzResearch.WordTrace tailWord_5644283 prefixEnd_5644283 2898230129001245450504921 := by
  unfold tailWord_5644283
  simp only [CollatzResearch.WordTrace]
  refine ⟨205863913410734132636193503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137242608940489421757462335 205863913410734132636193503)
  ·
    refine ⟨308795870116101198954290255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205863913410734132636193503 308795870116101198954290255)
    ·
      refine ⟨463193805174151798431435383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308795870116101198954290255 463193805174151798431435383)
      ·
        refine ⟨694790707761227697647153075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463193805174151798431435383 694790707761227697647153075)
        ·
          refine ⟨1042186061641841546470729613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694790707761227697647153075 1042186061641841546470729613)
          ·
            refine ⟨390819773115690579926523605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042186061641841546470729613 390819773115690579926523605)
            ·
              refine ⟨9159838432398997967027897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 390819773115690579926523605 9159838432398997967027897)
              ·
                refine ⟨6869878824299248475270923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159838432398997967027897 6869878824299248475270923)
                ·
                  refine ⟨10304818236448872712906385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869878824299248475270923 10304818236448872712906385)
                  ·
                    refine ⟨7728613677336654534679789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10304818236448872712906385 7728613677336654534679789)
                    ·
                      refine ⟨2898230129001245450504921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728613677336654534679789 2898230129001245450504921)
                      ·
                        rfl

theorem cell23_5644283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 3].length) (baseStart_5644283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644283 prefixEnd_5644283 := by exact prefixLift 5644283
  have htrace : WordTrace (prefixWord ++ tailWord_5644283) baseStart_5644283 baseEnd_5644283 := by
    simpa [prefixWord, tailWord_5644283, baseEnd_5644283] using wordTrace_append hprefix tailTrace_5644283
  have hstable : (prefixWord ++ tailWord_5644283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644283).length < 2 ^ (prefixWord ++ tailWord_5644283).sum := by decide
  have hdescent : baseEnd_5644283 < baseStart_5644283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644300 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_5644300 : Nat := 118140960795 + 5644300 * 2 ^ 59
def prefixEnd_5644300 : Nat := 4983230072969 + 3 ^ 40 * 5644300 * 2
def baseEnd_5644300 : Nat := 2898238858172371883992343

theorem tailTrace_5644300 : CollatzResearch.WordTrace tailWord_5644300 prefixEnd_5644300 2898238858172371883992343 := by
  unfold tailWord_5644300
  simp only [CollatzResearch.WordTrace]
  refine ⟨102932266725836272269781177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137243022301115029693041569 102932266725836272269781177)
  ·
    refine ⟨77199200044377204202335883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102932266725836272269781177 77199200044377204202335883)
    ·
      refine ⟨115798800066565806303503825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77199200044377204202335883 115798800066565806303503825)
      ·
        refine ⟨86849100049924354727627869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115798800066565806303503825 86849100049924354727627869)
        ·
          refine ⟨32568412518721633022860451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86849100049924354727627869 32568412518721633022860451)
          ·
            refine ⟨48852618778082449534290677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32568412518721633022860451 48852618778082449534290677)
            ·
              refine ⟨4579933010445229643839751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48852618778082449534290677 4579933010445229643839751)
              ·
                refine ⟨6869899515667844465759627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579933010445229643839751 6869899515667844465759627)
                ·
                  refine ⟨10304849273501766698639441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869899515667844465759627 10304849273501766698639441)
                  ·
                    refine ⟨7728636955126325023979581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10304849273501766698639441 7728636955126325023979581)
                    ·
                      refine ⟨2898238858172371883992343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728636955126325023979581 2898238858172371883992343)
                      ·
                        rfl

theorem cell23_5644300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_5644300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644300 prefixEnd_5644300 := by exact prefixLift 5644300
  have htrace : WordTrace (prefixWord ++ tailWord_5644300) baseStart_5644300 baseEnd_5644300 := by
    simpa [prefixWord, tailWord_5644300, baseEnd_5644300] using wordTrace_append hprefix tailTrace_5644300
  have hstable : (prefixWord ++ tailWord_5644300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644300).length < 2 ^ (prefixWord ++ tailWord_5644300).sum := by decide
  have hdescent : baseEnd_5644300 < baseStart_5644300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644308 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_5644308 : Nat := 118140960795 + 5644308 * 2 ^ 59
def prefixEnd_5644308 : Nat := 4983230072969 + 3 ^ 40 * 5644308 * 2
def baseEnd_5644308 : Nat := 2898242966017607852692307

theorem tailTrace_5644308 : CollatzResearch.WordTrace tailWord_5644308 prefixEnd_5644308 2898242966017607852692307 := by
  unfold tailWord_5644308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102932412617821780952926789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137243216823762374603902385 102932412617821780952926789)
  ·
    refine ⟨19299827365841583928673773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102932412617821780952926789 19299827365841583928673773)
    ·
      refine ⟨7237435262190593973252665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19299827365841583928673773 7237435262190593973252665)
      ·
        refine ⟨5428076446642945479939499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7237435262190593973252665 5428076446642945479939499)
        ·
          refine ⟨8142114669964418219909249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428076446642945479939499 8142114669964418219909249)
          ·
            refine ⟨6106586002473313664931937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142114669964418219909249 6106586002473313664931937)
            ·
              refine ⟨4579939501854985248698953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106586002473313664931937 4579939501854985248698953)
              ·
                refine ⟨3434954626391238936524215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579939501854985248698953 3434954626391238936524215)
                ·
                  refine ⟨5152431939586858404786323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434954626391238936524215 5152431939586858404786323)
                  ·
                    refine ⟨7728647909380287607179485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5152431939586858404786323 7728647909380287607179485)
                    ·
                      refine ⟨2898242966017607852692307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728647909380287607179485 2898242966017607852692307)
                      ·
                        rfl

theorem cell23_5644308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_5644308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644308 prefixEnd_5644308 := by exact prefixLift 5644308
  have htrace : WordTrace (prefixWord ++ tailWord_5644308) baseStart_5644308 baseEnd_5644308 := by
    simpa [prefixWord, tailWord_5644308, baseEnd_5644308] using wordTrace_append hprefix tailTrace_5644308
  have hstable : (prefixWord ++ tailWord_5644308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644308).length < 2 ^ (prefixWord ++ tailWord_5644308).sum := by decide
  have hdescent : baseEnd_5644308 < baseStart_5644308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644314 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2]
def baseStart_5644314 : Nat := 118140960795 + 5644314 * 2 ^ 59
def prefixEnd_5644314 : Nat := 4983230072969 + 3 ^ 40 * 5644314 * 2
def baseEnd_5644314 : Nat := 2898246046901534829217279

theorem tailTrace_5644314 : CollatzResearch.WordTrace tailWord_5644314 prefixEnd_5644314 2898246046901534829217279 := by
  unfold tailWord_5644314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51466261018405456232642999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137243362715747883287047997 51466261018405456232642999)
  ·
    refine ⟨77199391527608184348964499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51466261018405456232642999 77199391527608184348964499)
    ·
      refine ⟨115799087291412276523446749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77199391527608184348964499 115799087291412276523446749)
      ·
        refine ⟨43424657734279603696292531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115799087291412276523446749 43424657734279603696292531)
        ·
          refine ⟨65136986601419405544438797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43424657734279603696292531 65136986601419405544438797)
          ·
            refine ⟨24426369975532277079164549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65136986601419405544438797 24426369975532277079164549)
            ·
              refine ⟨4579944370412301952343353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24426369975532277079164549 4579944370412301952343353)
              ·
                refine ⟨3434958277809226464257515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579944370412301952343353 3434958277809226464257515)
                ·
                  refine ⟨5152437416713839696386273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434958277809226464257515 5152437416713839696386273)
                  ·
                    refine ⟨3864328062535379772289705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152437416713839696386273 3864328062535379772289705)
                    ·
                      refine ⟨2898246046901534829217279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864328062535379772289705 2898246046901534829217279)
                      ·
                        rfl

theorem cell23_5644314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_5644314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644314 prefixEnd_5644314 := by exact prefixLift 5644314
  have htrace : WordTrace (prefixWord ++ tailWord_5644314) baseStart_5644314 baseEnd_5644314 := by
    simpa [prefixWord, tailWord_5644314, baseEnd_5644314] using wordTrace_append hprefix tailTrace_5644314
  have hstable : (prefixWord ++ tailWord_5644314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644314).length < 2 ^ (prefixWord ++ tailWord_5644314).sum := by decide
  have hdescent : baseEnd_5644314 < baseStart_5644314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644316 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5644316 : Nat := 118140960795 + 5644316 * 2 ^ 59
def prefixEnd_5644316 : Nat := 4983230072969 + 3 ^ 40 * 5644316 * 2
def baseEnd_5644316 : Nat := 966082357954281273797423

theorem tailTrace_5644316 : CollatzResearch.WordTrace tailWord_5644316 prefixEnd_5644316 966082357954281273797423 := by
  unfold tailWord_5644316
  simp only [CollatzResearch.WordTrace]
  refine ⟨102932558509807289636072401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137243411346409719514763201 102932558509807289636072401)
  ·
    refine ⟨77199418882355467227054301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102932558509807289636072401 77199418882355467227054301)
    ·
      refine ⟨28949782080883300210145363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77199418882355467227054301 28949782080883300210145363)
      ·
        refine ⟨43424673121324950315218045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28949782080883300210145363 43424673121324950315218045)
        ·
          refine ⟨16284252420496856368206767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43424673121324950315218045 16284252420496856368206767)
          ·
            refine ⟨24426378630745284552310151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16284252420496856368206767 24426378630745284552310151)
            ·
              refine ⟨36639567946117926828465227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24426378630745284552310151 36639567946117926828465227)
              ·
                refine ⟨54959351919176890242697841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36639567946117926828465227 54959351919176890242697841)
                ·
                  refine ⟨41219513939382667682023381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54959351919176890242697841 41219513939382667682023381)
                  ·
                    refine ⟨966082357954281273797423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41219513939382667682023381 966082357954281273797423)
                    ·
                      rfl

theorem cell23_5644316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5644316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644316 prefixEnd_5644316 := by exact prefixLift 5644316
  have htrace : WordTrace (prefixWord ++ tailWord_5644316) baseStart_5644316 baseEnd_5644316 := by
    simpa [prefixWord, tailWord_5644316, baseEnd_5644316] using wordTrace_append hprefix tailTrace_5644316
  have hstable : (prefixWord ++ tailWord_5644316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644316).length < 2 ^ (prefixWord ++ tailWord_5644316).sum := by decide
  have hdescent : baseEnd_5644316 < baseStart_5644316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644323 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 5, 3, 2]
def baseStart_5644323 : Nat := 118140960795 + 5644323 * 2 ^ 59
def prefixEnd_5644323 : Nat := 4983230072969 + 3 ^ 40 * 5644323 * 2
def baseEnd_5644323 : Nat := 2898250668227425294004737

theorem tailTrace_5644323 : CollatzResearch.WordTrace tailWord_5644323 prefixEnd_5644323 2898250668227425294004737 := by
  unfold tailWord_5644323
  simp only [CollatzResearch.WordTrace]
  refine ⟨205865372330589219467649623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137243581553726146311766415 205865372330589219467649623)
  ·
    refine ⟨308798058495883829201474435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205865372330589219467649623 308798058495883829201474435)
    ·
      refine ⟨463197087743825743802211653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308798058495883829201474435 463197087743825743802211653)
      ·
        refine ⟨86849453951967326962914685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463197087743825743802211653 86849453951967326962914685)
        ·
          refine ⟨32568545231987747611093007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86849453951967326962914685 32568545231987747611093007)
          ·
            refine ⟨48852817847981621416639511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32568545231987747611093007 48852817847981621416639511)
            ·
              refine ⟨73279226771972432124959267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48852817847981621416639511 73279226771972432124959267)
              ·
                refine ⟨109918840157958648187438901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73279226771972432124959267 109918840157958648187438901)
                ·
                  refine ⟨10304891264808623267572397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109918840157958648187438901 10304891264808623267572397)
                  ·
                    refine ⟨3864334224303233725339649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10304891264808623267572397 3864334224303233725339649)
                    ·
                      refine ⟨2898250668227425294004737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864334224303233725339649 2898250668227425294004737)
                      ·
                        rfl

theorem cell23_5644323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_5644323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644323 prefixEnd_5644323 := by exact prefixLift 5644323
  have htrace : WordTrace (prefixWord ++ tailWord_5644323) baseStart_5644323 baseEnd_5644323 := by
    simpa [prefixWord, tailWord_5644323, baseEnd_5644323] using wordTrace_append hprefix tailTrace_5644323
  have hstable : (prefixWord ++ tailWord_5644323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644323).length < 2 ^ (prefixWord ++ tailWord_5644323).sum := by decide
  have hdescent : baseEnd_5644323 < baseStart_5644323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644330 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5644330 : Nat := 118140960795 + 5644330 * 2 ^ 59
def prefixEnd_5644330 : Nat := 4983230072969 + 3 ^ 40 * 5644330 * 2
def baseEnd_5644330 : Nat := 2898254262592006766617205

theorem tailTrace_5644330 : CollatzResearch.WordTrace tailWord_5644330 prefixEnd_5644330 2898254262592006766617205 := by
  unfold tailWord_5644330
  simp only [CollatzResearch.WordTrace]
  refine ⟨51466406910390964915788611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137243751761042573108769629 51466406910390964915788611)
  ·
    refine ⟨77199610365586447373682917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51466406910390964915788611 77199610365586447373682917)
    ·
      refine ⟨14474926943547458882565547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77199610365586447373682917 14474926943547458882565547)
      ·
        refine ⟨21712390415321188323848321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14474926943547458882565547 21712390415321188323848321)
        ·
          refine ⟨16284292811490891242886241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21712390415321188323848321 16284292811490891242886241)
          ·
            refine ⟨12213219608618168432164681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16284292811490891242886241 12213219608618168432164681)
            ·
              refine ⟨9159914706463626324123511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12213219608618168432164681 9159914706463626324123511)
              ·
                refine ⟨13739872059695439486185267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159914706463626324123511 13739872059695439486185267)
                ·
                  refine ⟨20609808089543159229277901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13739872059695439486185267 20609808089543159229277901)
                  ·
                    refine ⟨7728678033578684710979213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20609808089543159229277901 7728678033578684710979213)
                    ·
                      refine ⟨2898254262592006766617205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728678033578684710979213 2898254262592006766617205)
                      ·
                        rfl

theorem cell23_5644330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5644330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644330 prefixEnd_5644330 := by exact prefixLift 5644330
  have htrace : WordTrace (prefixWord ++ tailWord_5644330) baseStart_5644330 baseEnd_5644330 := by
    simpa [prefixWord, tailWord_5644330, baseEnd_5644330] using wordTrace_append hprefix tailTrace_5644330
  have hstable : (prefixWord ++ tailWord_5644330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644330).length < 2 ^ (prefixWord ++ tailWord_5644330).sum := by decide
  have hdescent : baseEnd_5644330 < baseStart_5644330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644376 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 7]
def baseStart_5644376 : Nat := 118140960795 + 5644376 * 2 ^ 59
def prefixEnd_5644376 : Nat := 4983230072969 + 3 ^ 40 * 5644376 * 2
def baseEnd_5644376 : Nat := 322030875855790398515777

theorem tailTrace_5644376 : CollatzResearch.WordTrace tailWord_5644376 prefixEnd_5644376 322030875855790398515777 := by
  unfold tailWord_5644376
  simp only [CollatzResearch.WordTrace]
  refine ⟨102933652699698604759664491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137244870266264806346219321 102933652699698604759664491)
  ·
    refine ⟨154400479049547907139496737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102933652699698604759664491 154400479049547907139496737)
    ·
      refine ⟨115800359287160930354622553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154400479049547907139496737 115800359287160930354622553)
      ·
        refine ⟨86850269465370697765966915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115800359287160930354622553 86850269465370697765966915)
        ·
          refine ⟨130275404198056046648950373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86850269465370697765966915 130275404198056046648950373)
          ·
            refine ⟨24426638287135508746678195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130275404198056046648950373 24426638287135508746678195)
            ·
              refine ⟨36639957430703263120017293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24426638287135508746678195 36639957430703263120017293)
              ·
                refine ⟨13739984036513723670006485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36639957430703263120017293 13739984036513723670006485)
                ·
                  refine ⟨322030875855790398515777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13739984036513723670006485 322030875855790398515777)
                  ·
                    rfl

theorem cell23_5644376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 7].length) (baseStart_5644376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644376 prefixEnd_5644376 := by exact prefixLift 5644376
  have htrace : WordTrace (prefixWord ++ tailWord_5644376) baseStart_5644376 baseEnd_5644376 := by
    simpa [prefixWord, tailWord_5644376, baseEnd_5644376] using wordTrace_append hprefix tailTrace_5644376
  have hstable : (prefixWord ++ tailWord_5644376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644376).length < 2 ^ (prefixWord ++ tailWord_5644376).sum := by decide
  have hdescent : baseEnd_5644376 < baseStart_5644376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644416 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5]
def baseStart_5644416 : Nat := 118140960795 + 5644416 * 2 ^ 59
def prefixEnd_5644416 : Nat := 4983230072969 + 3 ^ 40 * 5644416 * 2
def baseEnd_5644416 : Nat := 2898298421928293430141809

theorem tailTrace_5644416 : CollatzResearch.WordTrace tailWord_5644416 prefixEnd_5644416 2898298421928293430141809 := by
  unfold tailWord_5644416
  simp only [CollatzResearch.WordTrace]
  refine ⟨102934382159626148175392551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137245842879501530900523401 102934382159626148175392551)
  ·
    refine ⟨154401573239439222263088827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102934382159626148175392551 154401573239439222263088827)
    ·
      refine ⟨231602359859158833394633241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154401573239439222263088827 231602359859158833394633241)
      ·
        refine ⟨173701769894369125045974931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231602359859158833394633241 173701769894369125045974931)
        ·
          refine ⟨260552654841553687568962397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173701769894369125045974931 260552654841553687568962397)
          ·
            refine ⟨97707245565582632838360899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260552654841553687568962397 97707245565582632838360899)
            ·
              refine ⟨146560868348373949257541349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97707245565582632838360899 146560868348373949257541349)
              ·
                refine ⟨27480162815320115485789003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146560868348373949257541349 27480162815320115485789003)
                ·
                  refine ⟨41220244222980173228683505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27480162815320115485789003 41220244222980173228683505)
                  ·
                    refine ⟨30915183167235129921512629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41220244222980173228683505 30915183167235129921512629)
                    ·
                      refine ⟨2898298421928293430141809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30915183167235129921512629 2898298421928293430141809)
                      ·
                        rfl

theorem cell23_5644416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_5644416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644416 prefixEnd_5644416 := by exact prefixLift 5644416
  have htrace : WordTrace (prefixWord ++ tailWord_5644416) baseStart_5644416 baseEnd_5644416 := by
    simpa [prefixWord, tailWord_5644416, baseEnd_5644416] using wordTrace_append hprefix tailTrace_5644416
  have hstable : (prefixWord ++ tailWord_5644416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644416).length < 2 ^ (prefixWord ++ tailWord_5644416).sum := by decide
  have hdescent : baseEnd_5644416 < baseStart_5644416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644453 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_5644453 : Nat := 118140960795 + 5644453 * 2 ^ 59
def prefixEnd_5644453 : Nat := 4983230072969 + 3 ^ 40 * 5644453 * 2
def baseEnd_5644453 : Nat := 966105806904169928459713

theorem tailTrace_5644453 : CollatzResearch.WordTrace tailWord_5644453 prefixEnd_5644453 966105806904169928459713 := by
  unfold tailWord_5644453
  simp only [CollatzResearch.WordTrace]
  refine ⟨205870113820118251669882013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137246742546745501113254675 205870113820118251669882013)
  ·
    refine ⟨77201292682544344376205755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205870113820118251669882013 77201292682544344376205755)
    ·
      refine ⟨115801939023816516564308633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77201292682544344376205755 115801939023816516564308633)
      ·
        refine ⟨86851454267862387423231475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115801939023816516564308633 86851454267862387423231475)
        ·
          refine ⟨130277181401793581134847213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86851454267862387423231475 130277181401793581134847213)
          ·
            refine ⟨48853943025672592925567705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130277181401793581134847213 48853943025672592925567705)
            ·
              refine ⟨36640457269254444694175779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48853943025672592925567705 36640457269254444694175779)
              ·
                refine ⟨54960685903881667041263669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36640457269254444694175779 54960685903881667041263669)
                ·
                  refine ⟨5152564303488906285118469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54960685903881667041263669 5152564303488906285118469)
                  ·
                    refine ⟨966105806904169928459713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152564303488906285118469 966105806904169928459713)
                    ·
                      rfl

theorem cell23_5644453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_5644453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644453 prefixEnd_5644453 := by exact prefixLift 5644453
  have htrace : WordTrace (prefixWord ++ tailWord_5644453) baseStart_5644453 baseEnd_5644453 := by
    simpa [prefixWord, tailWord_5644453, baseEnd_5644453] using wordTrace_append hprefix tailTrace_5644453
  have hstable : (prefixWord ++ tailWord_5644453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644453).length < 2 ^ (prefixWord ++ tailWord_5644453).sum := by decide
  have hdescent : baseEnd_5644453 < baseStart_5644453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644480 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3]
def baseStart_5644480 : Nat := 118140960795 + 5644480 * 2 ^ 59
def prefixEnd_5644480 : Nat := 4983230072969 + 3 ^ 40 * 5644480 * 2
def baseEnd_5644480 : Nat := 2898331284690181179741515

theorem tailTrace_5644480 : CollatzResearch.WordTrace tailWord_5644480 prefixEnd_5644480 2898331284690181179741515 := by
  unfold tailWord_5644480
  simp only [CollatzResearch.WordTrace]
  refine ⟨102935549295510217640557447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137247399060680290187409929 102935549295510217640557447)
  ·
    refine ⟨154403323943265326460836171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102935549295510217640557447 154403323943265326460836171)
    ·
      refine ⟨231604985914897989691254257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154403323943265326460836171 231604985914897989691254257)
      ·
        refine ⟨173703739436173492268440693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231604985914897989691254257 173703739436173492268440693)
        ·
          refine ⟨16284725572141264900166315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173703739436173492268440693 16284725572141264900166315)
          ·
            refine ⟨24427088358211897350249473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16284725572141264900166315 24427088358211897350249473)
            ·
              refine ⟨18320316268658923012687105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24427088358211897350249473 18320316268658923012687105)
              ·
                refine ⟨13740237201494192259515329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18320316268658923012687105 13740237201494192259515329)
                ·
                  refine ⟨10305177901120644194636497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13740237201494192259515329 10305177901120644194636497)
                  ·
                    refine ⟨7728883425840483145977373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10305177901120644194636497 7728883425840483145977373)
                    ·
                      refine ⟨2898331284690181179741515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7728883425840483145977373 2898331284690181179741515)
                      ·
                        rfl

theorem cell23_5644480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_5644480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644480 prefixEnd_5644480 := by exact prefixLift 5644480
  have htrace : WordTrace (prefixWord ++ tailWord_5644480) baseStart_5644480 baseEnd_5644480 := by
    simpa [prefixWord, tailWord_5644480, baseEnd_5644480] using wordTrace_append hprefix tailTrace_5644480
  have hstable : (prefixWord ++ tailWord_5644480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644480).length < 2 ^ (prefixWord ++ tailWord_5644480).sum := by decide
  have hdescent : baseEnd_5644480 < baseStart_5644480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644513 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 3, 5]
def baseStart_5644513 : Nat := 118140960795 + 5644513 * 2 ^ 59
def prefixEnd_5644513 : Nat := 4983230072969 + 3 ^ 40 * 5644513 * 2
def baseEnd_5644513 : Nat := 966116076517259850209621

theorem tailTrace_5644513 : CollatzResearch.WordTrace tailWord_5644513 prefixEnd_5644513 966116076517259850209621 := by
  unfold tailWord_5644513
  simp only [CollatzResearch.WordTrace]
  refine ⟨205872302199900881917066193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137248201466600587944710795 205872302199900881917066193)
  ·
    refine ⟨154404226649925661437799645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205872302199900881917066193 154404226649925661437799645)
    ·
      refine ⟨57901584993722123039174867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154404226649925661437799645 57901584993722123039174867)
      ·
        refine ⟨86852377490583184558762301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57901584993722123039174867 86852377490583184558762301)
        ·
          refine ⟨32569641558968694209535863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86852377490583184558762301 32569641558968694209535863)
          ·
            refine ⟨48854462338453041314303795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32569641558968694209535863 48854462338453041314303795)
            ·
              refine ⟨73281693507679561971455693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48854462338453041314303795 73281693507679561971455693)
              ·
                refine ⟨27480635065379835739295885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73281693507679561971455693 27480635065379835739295885)
                ·
                  refine ⟨10305238149517438402235957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27480635065379835739295885 10305238149517438402235957)
                  ·
                    refine ⟨966116076517259850209621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10305238149517438402235957 966116076517259850209621)
                    ·
                      rfl

theorem cell23_5644513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_5644513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644513 prefixEnd_5644513 := by exact prefixLift 5644513
  have htrace : WordTrace (prefixWord ++ tailWord_5644513) baseStart_5644513 baseEnd_5644513 := by
    simpa [prefixWord, tailWord_5644513, baseEnd_5644513] using wordTrace_append hprefix tailTrace_5644513
  have hstable : (prefixWord ++ tailWord_5644513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644513).length < 2 ^ (prefixWord ++ tailWord_5644513).sum := by decide
  have hdescent : baseEnd_5644513 < baseStart_5644513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644553 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_5644553 : Nat := 118140960795 + 5644553 * 2 ^ 59
def prefixEnd_5644553 : Nat := 4983230072969 + 3 ^ 40 * 5644553 * 2
def baseEnd_5644553 : Nat := 2898368768777959394128679

theorem tailTrace_5644553 : CollatzResearch.WordTrace tailWord_5644553 prefixEnd_5644553 2898368768777959394128679 := by
  unfold tailWord_5644553
  simp only [CollatzResearch.WordTrace]
  refine ⟨205873761119755968748522313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137249174079837312499014875 205873761119755968748522313)
  ·
    refine ⟨154405320839816976561391735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205873761119755968748522313 154405320839816976561391735)
    ·
      refine ⟨231607981259725464842087603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154405320839816976561391735 231607981259725464842087603)
      ·
        refine ⟨347411971889588197263131405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231607981259725464842087603 347411971889588197263131405)
        ·
          refine ⟨130279489458595573973674277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347411971889588197263131405 130279489458595573973674277)
          ·
            refine ⟨24427404273486670120063927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130279489458595573973674277 24427404273486670120063927)
            ·
              refine ⟨36641106410230005180095891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24427404273486670120063927 36641106410230005180095891)
              ·
                refine ⟨54961659615345007770143837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36641106410230005180095891 54961659615345007770143837)
                ·
                  refine ⟨20610622355754377913803939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54961659615345007770143837 20610622355754377913803939)
                  ·
                    refine ⟨30915933533631566870705909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20610622355754377913803939 30915933533631566870705909)
                    ·
                      refine ⟨2898368768777959394128679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30915933533631566870705909 2898368768777959394128679)
                      ·
                        rfl

theorem cell23_5644553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_5644553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644553 prefixEnd_5644553 := by exact prefixLift 5644553
  have htrace : WordTrace (prefixWord ++ tailWord_5644553) baseStart_5644553 baseEnd_5644553 := by
    simpa [prefixWord, tailWord_5644553, baseEnd_5644553] using wordTrace_append hprefix tailTrace_5644553
  have hstable : (prefixWord ++ tailWord_5644553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644553).length < 2 ^ (prefixWord ++ tailWord_5644553).sum := by decide
  have hdescent : baseEnd_5644553 < baseStart_5644553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644567 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_5644567 : Nat := 118140960795 + 5644567 * 2 ^ 59
def prefixEnd_5644567 : Nat := 4983230072969 + 3 ^ 40 * 5644567 * 2
def baseEnd_5644567 : Nat := 2898375957507122339353615

theorem tailTrace_5644567 : CollatzResearch.WordTrace tailWord_5644567 prefixEnd_5644567 2898375957507122339353615 := by
  unfold tailWord_5644567
  simp only [CollatzResearch.WordTrace]
  refine ⟨205874271741705249139531955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137249514494470166093021303 205874271741705249139531955)
  ·
    refine ⟨308811407612557873709297933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205874271741705249139531955 308811407612557873709297933)
    ·
      refine ⟨115804277854709202640986725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308811407612557873709297933 115804277854709202640986725)
      ·
        refine ⟨21713302097757975495185011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115804277854709202640986725 21713302097757975495185011)
        ·
          refine ⟨32569953146636963242777517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713302097757975495185011 32569953146636963242777517)
          ·
            refine ⟨12213732429988861216041569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32569953146636963242777517 12213732429988861216041569)
            ·
              refine ⟨9160299322491645912031177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12213732429988861216041569 9160299322491645912031177)
              ·
                refine ⟨6870224491868734434023383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9160299322491645912031177 6870224491868734434023383)
                ·
                  refine ⟨10305336737803101651035075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870224491868734434023383 10305336737803101651035075)
                  ·
                    refine ⟨15458005106704652476552613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10305336737803101651035075 15458005106704652476552613)
                    ·
                      refine ⟨2898375957507122339353615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15458005106704652476552613 2898375957507122339353615)
                      ·
                        rfl

theorem cell23_5644567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_5644567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644567 prefixEnd_5644567 := by exact prefixLift 5644567
  have htrace : WordTrace (prefixWord ++ tailWord_5644567) baseStart_5644567 baseEnd_5644567 := by
    simpa [prefixWord, tailWord_5644567, baseEnd_5644567] using wordTrace_append hprefix tailTrace_5644567
  have hstable : (prefixWord ++ tailWord_5644567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644567).length < 2 ^ (prefixWord ++ tailWord_5644567).sum := by decide
  have hdescent : baseEnd_5644567 < baseStart_5644567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644601 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5644601 : Nat := 118140960795 + 5644601 * 2 ^ 59
def prefixEnd_5644601 : Nat := 4983230072969 + 3 ^ 40 * 5644601 * 2
def baseEnd_5644601 : Nat := 2898393415849375206328459

theorem tailTrace_5644601 : CollatzResearch.WordTrace tailWord_5644601 prefixEnd_5644601 2898393415849375206328459 := by
  unfold tailWord_5644601
  simp only [CollatzResearch.WordTrace]
  refine ⟨205875511823582072946269657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137250341215721381964179771 205875511823582072946269657)
  ·
    refine ⟨154406633867686554709702243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205875511823582072946269657 154406633867686554709702243)
    ·
      refine ⟨231609950801529832064553365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154406633867686554709702243 231609950801529832064553365)
      ·
        refine ⟨10856716443821710878025939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 231609950801529832064553365 10856716443821710878025939)
        ·
          refine ⟨16285074665732566317038909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856716443821710878025939 16285074665732566317038909)
          ·
            refine ⟨6106902999649712368889591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16285074665732566317038909 6106902999649712368889591)
            ·
              refine ⟨9160354499474568553334387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106902999649712368889591 9160354499474568553334387)
              ·
                refine ⟨13740531749211852830001581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160354499474568553334387 13740531749211852830001581)
                ·
                  refine ⟨5152699405954444811250593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13740531749211852830001581 5152699405954444811250593)
                  ·
                    refine ⟨3864524554465833608437945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152699405954444811250593 3864524554465833608437945)
                    ·
                      refine ⟨2898393415849375206328459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864524554465833608437945 2898393415849375206328459)
                      ·
                        rfl

theorem cell23_5644601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5644601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644601 prefixEnd_5644601 := by exact prefixLift 5644601
  have htrace : WordTrace (prefixWord ++ tailWord_5644601) baseStart_5644601 baseEnd_5644601 := by
    simpa [prefixWord, tailWord_5644601, baseEnd_5644601] using wordTrace_append hprefix tailTrace_5644601
  have hstable : (prefixWord ++ tailWord_5644601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644601).length < 2 ^ (prefixWord ++ tailWord_5644601).sum := by decide
  have hdescent : baseEnd_5644601 < baseStart_5644601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644623 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_5644623 : Nat := 118140960795 + 5644623 * 2 ^ 59
def prefixEnd_5644623 : Nat := 4983230072969 + 3 ^ 40 * 5644623 * 2
def baseEnd_5644623 : Nat := 2898404712423774120253357

theorem tailTrace_5644623 : CollatzResearch.WordTrace tailWord_5644623 prefixEnd_5644623 2898404712423774120253357 := by
  unfold tailWord_5644623
  simp only [CollatzResearch.WordTrace]
  refine ⟨205876314229502370703570523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137250876153001580469047015 205876314229502370703570523)
  ·
    refine ⟨308814471344253556055355785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205876314229502370703570523 308814471344253556055355785)
    ·
      refine ⟨231610853508190167041516839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308814471344253556055355785 231610853508190167041516839)
      ·
        refine ⟨347416280262285250562275259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231610853508190167041516839 347416280262285250562275259)
        ·
          refine ⟨521124420393427875843412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347416280262285250562275259 521124420393427875843412889)
          ·
            refine ⟨390843315295070906882559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521124420393427875843412889 390843315295070906882559667)
            ·
              refine ⟨586264972942606360323839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390843315295070906882559667 586264972942606360323839501)
              ·
                refine ⟨219849364853477385121439813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586264972942606360323839501 219849364853477385121439813)
                ·
                  refine ⟨41221755910027009710269965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219849364853477385121439813 41221755910027009710269965)
                  ·
                    refine ⟨15458158466260128641351237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41221755910027009710269965 15458158466260128641351237)
                    ·
                      refine ⟨2898404712423774120253357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15458158466260128641351237 2898404712423774120253357)
                      ·
                        rfl

theorem cell23_5644623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_5644623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644623 prefixEnd_5644623 := by exact prefixLift 5644623
  have htrace : WordTrace (prefixWord ++ tailWord_5644623) baseStart_5644623 baseEnd_5644623 := by
    simpa [prefixWord, tailWord_5644623, baseEnd_5644623] using wordTrace_append hprefix tailTrace_5644623
  have hstable : (prefixWord ++ tailWord_5644623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644623).length < 2 ^ (prefixWord ++ tailWord_5644623).sum := by decide
  have hdescent : baseEnd_5644623 < baseStart_5644623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644627 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 1, 3, 2]
def baseStart_5644627 : Nat := 118140960795 + 5644627 * 2 ^ 59
def prefixEnd_5644627 : Nat := 4983230072969 + 3 ^ 40 * 5644627 * 2
def baseEnd_5644627 : Nat := 2898406766346392104603339

theorem tailTrace_5644627 : CollatzResearch.WordTrace tailWord_5644627 prefixEnd_5644627 2898406766346392104603339 := by
  unfold tailWord_5644627
  simp only [CollatzResearch.WordTrace]
  refine ⟨205876460121487879386716135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137250973414325252924477423 205876460121487879386716135)
  ·
    refine ⟨308814690182231819080074203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205876460121487879386716135 308814690182231819080074203)
    ·
      refine ⟨463222035273347728620111305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308814690182231819080074203 463222035273347728620111305)
      ·
        refine ⟨347416526455010796465083479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463222035273347728620111305 347416526455010796465083479)
        ·
          refine ⟨521124789682516194697625219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347416526455010796465083479 521124789682516194697625219)
          ·
            refine ⟨781687184523774292046437829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521124789682516194697625219 781687184523774292046437829)
            ·
              refine ⟨146566347098207679758707093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 781687184523774292046437829 146566347098207679758707093)
              ·
                refine ⟨6870297520228484988689395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146566347098207679758707093 6870297520228484988689395)
                ·
                  refine ⟨10305446280342727483034093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870297520228484988689395 10305446280342727483034093)
                  ·
                    refine ⟨3864542355128522806137785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10305446280342727483034093 3864542355128522806137785)
                    ·
                      refine ⟨2898406766346392104603339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864542355128522806137785 2898406766346392104603339)
                      ·
                        rfl

theorem cell23_5644627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3, 2].length) (baseStart_5644627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644627 prefixEnd_5644627 := by exact prefixLift 5644627
  have htrace : WordTrace (prefixWord ++ tailWord_5644627) baseStart_5644627 baseEnd_5644627 := by
    simpa [prefixWord, tailWord_5644627, baseEnd_5644627] using wordTrace_append hprefix tailTrace_5644627
  have hstable : (prefixWord ++ tailWord_5644627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644627).length < 2 ^ (prefixWord ++ tailWord_5644627).sum := by decide
  have hdescent : baseEnd_5644627 < baseStart_5644627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644633 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 6]
def baseStart_5644633 : Nat := 118140960795 + 5644633 * 2 ^ 59
def prefixEnd_5644633 : Nat := 4983230072969 + 3 ^ 40 * 5644633 * 2
def baseEnd_5644633 : Nat := 966136615743439693709437

theorem tailTrace_5644633 : CollatzResearch.WordTrace tailWord_5644633 prefixEnd_5644633 966136615743439693709437 := by
  unfold tailWord_5644633
  simp only [CollatzResearch.WordTrace]
  refine ⟨205876678959466142411434553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137251119306310761607623035 205876678959466142411434553)
  ·
    refine ⟨154407509219599606808575915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205876678959466142411434553 154407509219599606808575915)
    ·
      refine ⟨231611263829399410212863873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154407509219599606808575915 231611263829399410212863873)
      ·
        refine ⟨173708447872049557659647905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231611263829399410212863873 173708447872049557659647905)
        ·
          refine ⟨130281335904037168244735929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173708447872049557659647905 130281335904037168244735929)
          ·
            refine ⟨97711001928027876183551947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130281335904037168244735929 97711001928027876183551947)
            ·
              refine ⟨146566502892041814275327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97711001928027876183551947 146566502892041814275327921)
              ·
                refine ⟨109924877169031360706495941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146566502892041814275327921 109924877169031360706495941)
                ·
                  refine ⟨20610914469193380132467989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109924877169031360706495941 20610914469193380132467989)
                  ·
                    refine ⟨966136615743439693709437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20610914469193380132467989 966136615743439693709437)
                    ·
                      rfl

theorem cell23_5644633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_5644633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644633 prefixEnd_5644633 := by exact prefixLift 5644633
  have htrace : WordTrace (prefixWord ++ tailWord_5644633) baseStart_5644633 baseEnd_5644633 := by
    simpa [prefixWord, tailWord_5644633, baseEnd_5644633] using wordTrace_append hprefix tailTrace_5644633
  have hstable : (prefixWord ++ tailWord_5644633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644633).length < 2 ^ (prefixWord ++ tailWord_5644633).sum := by decide
  have hdescent : baseEnd_5644633 < baseStart_5644633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644680 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 7]
def baseStart_5644680 : Nat := 118140960795 + 5644680 * 2 ^ 59
def prefixEnd_5644680 : Nat := 4983230072969 + 3 ^ 40 * 5644680 * 2
def baseEnd_5644680 : Nat := 322048220091231155248955

theorem tailTrace_5644680 : CollatzResearch.WordTrace tailWord_5644680 prefixEnd_5644680 322048220091231155248955 := by
  unfold tailWord_5644680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102939196595147934719197747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137252262126863912958930329 102939196595147934719197747)
  ·
    refine ⟨154408794892721902078796621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102939196595147934719197747 154408794892721902078796621)
    ·
      refine ⟨57903298084770713279548733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154408794892721902078796621 57903298084770713279548733)
      ·
        refine ⟨21713736781789017479830775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57903298084770713279548733 21713736781789017479830775)
        ·
          refine ⟨32570605172683526219746163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713736781789017479830775 32570605172683526219746163)
          ·
            refine ⟨48855907759025289329619245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32570605172683526219746163 48855907759025289329619245)
            ·
              refine ⟨18320965409634483498607217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48855907759025289329619245 18320965409634483498607217)
              ·
                refine ⟨13740724057225862623955413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18320965409634483498607217 13740724057225862623955413)
                ·
                  refine ⟨322048220091231155248955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13740724057225862623955413 322048220091231155248955)
                  ·
                    rfl

theorem cell23_5644680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 7].length) (baseStart_5644680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644680 prefixEnd_5644680 := by exact prefixLift 5644680
  have htrace : WordTrace (prefixWord ++ tailWord_5644680) baseStart_5644680 baseEnd_5644680 := by
    simpa [prefixWord, tailWord_5644680, baseEnd_5644680] using wordTrace_append hprefix tailTrace_5644680
  have hstable : (prefixWord ++ tailWord_5644680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644680).length < 2 ^ (prefixWord ++ tailWord_5644680).sum := by decide
  have hdescent : baseEnd_5644680 < baseStart_5644680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644697 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 5]
def baseStart_5644697 : Nat := 118140960795 + 5644697 * 2 ^ 59
def prefixEnd_5644697 : Nat := 4983230072969 + 3 ^ 40 * 5644697 * 2
def baseEnd_5644697 : Nat := 322049189999134092303113

theorem tailTrace_5644697 : CollatzResearch.WordTrace tailWord_5644697 prefixEnd_5644697 322049189999134092303113 := by
  unfold tailWord_5644697
  simp only [CollatzResearch.WordTrace]
  refine ⟨205879013231234281341764345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137252675487489520894509563 205879013231234281341764345)
  ·
    refine ⟨154409259923425711006323259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205879013231234281341764345 154409259923425711006323259)
    ·
      refine ⟨231613889885138566509484889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154409259923425711006323259 231613889885138566509484889)
      ·
        refine ⟨173710417413853924882113667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231613889885138566509484889 173710417413853924882113667)
        ·
          refine ⟨260565626120780887323170501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173710417413853924882113667 260565626120780887323170501)
          ·
            refine ⟨48856054897646416373094469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260565626120780887323170501 48856054897646416373094469)
            ·
              refine ⟨9160510293308703069955213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48856054897646416373094469 9160510293308703069955213)
              ·
                refine ⟨3435191359990763651233205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9160510293308703069955213 3435191359990763651233205)
                ·
                  refine ⟨322049189999134092303113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3435191359990763651233205 322049189999134092303113)
                  ·
                    rfl

theorem cell23_5644697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 5].length) (baseStart_5644697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644697 prefixEnd_5644697 := by exact prefixLift 5644697
  have htrace : WordTrace (prefixWord ++ tailWord_5644697) baseStart_5644697 baseEnd_5644697 := by
    simpa [prefixWord, tailWord_5644697, baseEnd_5644697] using wordTrace_append hprefix tailTrace_5644697
  have hstable : (prefixWord ++ tailWord_5644697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644697).length < 2 ^ (prefixWord ++ tailWord_5644697).sum := by decide
  have hdescent : baseEnd_5644697 < baseStart_5644697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644750 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_5644750 : Nat := 118140960795 + 5644750 * 2 ^ 59
def prefixEnd_5644750 : Nat := 4983230072969 + 3 ^ 40 * 5644750 * 2
def baseEnd_5644750 : Nat := 2898469924466895123365273

theorem tailTrace_5644750 : CollatzResearch.WordTrace tailWord_5644750 prefixEnd_5644750 2898469924466895123365273 := by
  unfold tailWord_5644750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735118287505283924180463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137253964200028180928962469 25735118287505283924180463)
  ·
    refine ⟨38602677431257925886270695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25735118287505283924180463 38602677431257925886270695)
    ·
      refine ⟨57904016146886888829406043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38602677431257925886270695 57904016146886888829406043)
      ·
        refine ⟨86856024220330333244109065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57904016146886888829406043 86856024220330333244109065)
        ·
          refine ⟨65142018165247749933081799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86856024220330333244109065 65142018165247749933081799)
          ·
            refine ⟨97713027247871624899622699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65142018165247749933081799 97713027247871624899622699)
            ·
              refine ⟨146569540871807437349434049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97713027247871624899622699 146569540871807437349434049)
              ·
                refine ⟨109927155653855578012075537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146569540871807437349434049 109927155653855578012075537)
                ·
                  refine ⟨82445366740391683509056653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109927155653855578012075537 82445366740391683509056653)
                  ·
                    refine ⟨30917012527646881315896245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82445366740391683509056653 30917012527646881315896245)
                    ·
                      refine ⟨2898469924466895123365273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30917012527646881315896245 2898469924466895123365273)
                      ·
                        rfl

theorem cell23_5644750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_5644750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644750 prefixEnd_5644750 := by exact prefixLift 5644750
  have htrace : WordTrace (prefixWord ++ tailWord_5644750) baseStart_5644750 baseEnd_5644750 := by
    simpa [prefixWord, tailWord_5644750, baseEnd_5644750] using wordTrace_append hprefix tailTrace_5644750
  have hstable : (prefixWord ++ tailWord_5644750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644750).length < 2 ^ (prefixWord ++ tailWord_5644750).sum := by decide
  have hdescent : baseEnd_5644750 < baseStart_5644750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644767 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_5644767 : Nat := 118140960795 + 5644767 * 2 ^ 59
def prefixEnd_5644767 : Nat := 4983230072969 + 3 ^ 40 * 5644767 * 2
def baseEnd_5644767 : Nat := 2898478653638021556852695

theorem tailTrace_5644767 : CollatzResearch.WordTrace tailWord_5644767 prefixEnd_5644767 2898478653638021556852695 := by
  unfold tailWord_5644767
  simp only [CollatzResearch.WordTrace]
  refine ⟨205881566340980683296812555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137254377560653788864541703 205881566340980683296812555)
  ·
    refine ⟨308822349511471024945218833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205881566340980683296812555 308822349511471024945218833)
    ·
      refine ⟨231616762133603268708914125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308822349511471024945218833 231616762133603268708914125)
      ·
        refine ⟨86856285800101225765842797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231616762133603268708914125 86856285800101225765842797)
        ·
          refine ⟨32571107175037959662191049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86856285800101225765842797 32571107175037959662191049)
          ·
            refine ⟨24428330381278469746643287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32571107175037959662191049 24428330381278469746643287)
            ·
              refine ⟨36642495571917704619964931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24428330381278469746643287 36642495571917704619964931)
              ·
                refine ⟨54963743357876556929947397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36642495571917704619964931 54963743357876556929947397)
                ·
                  refine ⟨10305701879601854424365137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54963743357876556929947397 10305701879601854424365137)
                  ·
                    refine ⟨7729276409701390818273853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10305701879601854424365137 7729276409701390818273853)
                    ·
                      refine ⟨2898478653638021556852695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7729276409701390818273853 2898478653638021556852695)
                      ·
                        rfl

theorem cell23_5644767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_5644767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644767 prefixEnd_5644767 := by exact prefixLift 5644767
  have htrace : WordTrace (prefixWord ++ tailWord_5644767) baseStart_5644767 baseEnd_5644767 := by
    simpa [prefixWord, tailWord_5644767, baseEnd_5644767] using wordTrace_append hprefix tailTrace_5644767
  have hstable : (prefixWord ++ tailWord_5644767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644767).length < 2 ^ (prefixWord ++ tailWord_5644767).sum := by decide
  have hdescent : baseEnd_5644767 < baseStart_5644767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644837 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_5644837 : Nat := 118140960795 + 5644837 * 2 ^ 59
def prefixEnd_5644837 : Nat := 4983230072969 + 3 ^ 40 * 5644837 * 2
def baseEnd_5644837 : Nat := 2898514597283836282977373

theorem tailTrace_5644837 : CollatzResearch.WordTrace tailWord_5644837 prefixEnd_5644837 2898514597283836282977373 := by
  unfold tailWord_5644837
  simp only [CollatzResearch.WordTrace]
  refine ⟨205884119450727085251860765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137256079633818056834573843 205884119450727085251860765)
  ·
    refine ⟨77206544794022656969447787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205884119450727085251860765 77206544794022656969447787)
    ·
      refine ⟨115809817191033985454171681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77206544794022656969447787 115809817191033985454171681)
      ·
        refine ⟨86857362893275489090628761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115809817191033985454171681 86857362893275489090628761)
        ·
          refine ⟨65143022169956616817971571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86857362893275489090628761 65143022169956616817971571)
          ·
            refine ⟨97714533254934925226957357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65143022169956616817971571 97714533254934925226957357)
            ·
              refine ⟨36642949970600596960109009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97714533254934925226957357 36642949970600596960109009)
              ·
                refine ⟨27482212477950447720081757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36642949970600596960109009 27482212477950447720081757)
                ·
                  refine ⟨10305829679231417895030659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27482212477950447720081757 10305829679231417895030659)
                  ·
                    refine ⟨15458744518847126842545989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10305829679231417895030659 15458744518847126842545989)
                    ·
                      refine ⟨2898514597283836282977373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15458744518847126842545989 2898514597283836282977373)
                      ·
                        rfl

theorem cell23_5644837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_5644837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644837 prefixEnd_5644837 := by exact prefixLift 5644837
  have htrace : WordTrace (prefixWord ++ tailWord_5644837) baseStart_5644837 baseEnd_5644837 := by
    simpa [prefixWord, tailWord_5644837, baseEnd_5644837] using wordTrace_append hprefix tailTrace_5644837
  have hstable : (prefixWord ++ tailWord_5644837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644837).length < 2 ^ (prefixWord ++ tailWord_5644837).sum := by decide
  have hdescent : baseEnd_5644837 < baseStart_5644837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644871 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_5644871 : Nat := 118140960795 + 5644871 * 2 ^ 59
def prefixEnd_5644871 : Nat := 4983230072969 + 3 ^ 40 * 5644871 * 2
def baseEnd_5644871 : Nat := 2898532055626089149952217

theorem tailTrace_5644871 : CollatzResearch.WordTrace tailWord_5644871 prefixEnd_5644871 2898532055626089149952217 := by
  unfold tailWord_5644871
  simp only [CollatzResearch.WordTrace]
  refine ⟨205885359532603909058598467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137256906355069272705732311 205885359532603909058598467)
  ·
    refine ⟨308828039298905863587897701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205885359532603909058598467 308828039298905863587897701)
    ·
      refine ⟨57905257368544849422730819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308828039298905863587897701 57905257368544849422730819)
      ·
        refine ⟨86857886052817274134096229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57905257368544849422730819 86857886052817274134096229)
        ·
          refine ⟨16285853634903238900143043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86857886052817274134096229 16285853634903238900143043)
          ·
            refine ⟨24428780452354858350214565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16285853634903238900143043 24428780452354858350214565)
            ·
              refine ⟨4580396334816535940665231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24428780452354858350214565 4580396334816535940665231)
              ·
                refine ⟨6870594502224803910997847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580396334816535940665231 6870594502224803910997847)
                ·
                  refine ⟨10305891753337205866496771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870594502224803910997847 10305891753337205866496771)
                  ·
                    refine ⟨15458837630005808799745157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10305891753337205866496771 15458837630005808799745157)
                    ·
                      refine ⟨2898532055626089149952217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15458837630005808799745157 2898532055626089149952217)
                      ·
                        rfl

theorem cell23_5644871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_5644871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644871 prefixEnd_5644871 := by exact prefixLift 5644871
  have htrace : WordTrace (prefixWord ++ tailWord_5644871) baseStart_5644871 baseEnd_5644871 := by
    simpa [prefixWord, tailWord_5644871, baseEnd_5644871] using wordTrace_append hprefix tailTrace_5644871
  have hstable : (prefixWord ++ tailWord_5644871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644871).length < 2 ^ (prefixWord ++ tailWord_5644871).sum := by decide
  have hdescent : baseEnd_5644871 < baseStart_5644871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644881 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 2, 4]
def baseStart_5644881 : Nat := 118140960795 + 5644881 * 2 ^ 59
def prefixEnd_5644881 : Nat := 4983230072969 + 3 ^ 40 * 5644881 * 2
def baseEnd_5644881 : Nat := 966179063477544703609057

theorem tailTrace_5644881 : CollatzResearch.WordTrace tailWord_5644881 prefixEnd_5644881 966179063477544703609057 := by
  unfold tailWord_5644881
  simp only [CollatzResearch.WordTrace]
  refine ⟨205885724262567680766462497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137257149508378453844308331 205885724262567680766462497)
  ·
    refine ⟨154414293196925760574846873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205885724262567680766462497 154414293196925760574846873)
    ·
      refine ⟨115810719897694320431135155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154414293196925760574846873 115810719897694320431135155)
      ·
        refine ⟨173716079846541480646702733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115810719897694320431135155 173716079846541480646702733)
        ·
          refine ⟨65143529942453055242513525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173716079846541480646702733 65143529942453055242513525)
          ·
            refine ⟨6107205932104973928985643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65143529942453055242513525 6107205932104973928985643)
            ·
              refine ⟨9160808898157460893478465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107205932104973928985643 9160808898157460893478465)
              ·
                refine ⟨6870606673618095670108849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9160808898157460893478465 6870606673618095670108849)
                ·
                  refine ⟨5152955005213571752581637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6870606673618095670108849 5152955005213571752581637)
                  ·
                    refine ⟨966179063477544703609057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152955005213571752581637 966179063477544703609057)
                    ·
                      rfl

theorem cell23_5644881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_5644881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644881 prefixEnd_5644881 := by exact prefixLift 5644881
  have htrace : WordTrace (prefixWord ++ tailWord_5644881) baseStart_5644881 baseEnd_5644881 := by
    simpa [prefixWord, tailWord_5644881, baseEnd_5644881] using wordTrace_append hprefix tailTrace_5644881
  have hstable : (prefixWord ++ tailWord_5644881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644881).length < 2 ^ (prefixWord ++ tailWord_5644881).sum := by decide
  have hdescent : baseEnd_5644881 < baseStart_5644881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644888 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_5644888 : Nat := 118140960795 + 5644888 * 2 ^ 59
def prefixEnd_5644888 : Nat := 4983230072969 + 3 ^ 40 * 5644888 * 2
def baseEnd_5644888 : Nat := 2898540784797215583439639

theorem tailTrace_5644888 : CollatzResearch.WordTrace tailWord_5644888 prefixEnd_5644888 2898540784797215583439639 := by
  unfold tailWord_5644888
  simp only [CollatzResearch.WordTrace]
  refine ⟨102942989786771160480983659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137257319715694880641311545 102942989786771160480983659)
  ·
    refine ⟨154414484680156740721475489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102942989786771160480983659 154414484680156740721475489)
    ·
      refine ⟨115810863510117555541106617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154414484680156740721475489 115810863510117555541106617)
      ·
        refine ⟨86858147632588166655829963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115810863510117555541106617 86858147632588166655829963)
        ·
          refine ⟨130287221448882249983744945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86858147632588166655829963 130287221448882249983744945)
          ·
            refine ⟨97715416086661687487808709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130287221448882249983744945 97715416086661687487808709)
            ·
              refine ⟨18321640516249066403964133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97715416086661687487808709 18321640516249066403964133)
              ·
                refine ⟨3435307596796699950743275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18321640516249066403964133 3435307596796699950743275)
                ·
                  refine ⟨5152961395195049926114913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435307596796699950743275 5152961395195049926114913)
                  ·
                    refine ⟨3864721046396287444586185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152961395195049926114913 3864721046396287444586185)
                    ·
                      refine ⟨2898540784797215583439639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864721046396287444586185 2898540784797215583439639)
                      ·
                        rfl

theorem cell23_5644888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_5644888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644888 prefixEnd_5644888 := by exact prefixLift 5644888
  have htrace : WordTrace (prefixWord ++ tailWord_5644888) baseStart_5644888 baseEnd_5644888 := by
    simpa [prefixWord, tailWord_5644888, baseEnd_5644888] using wordTrace_append hprefix tailTrace_5644888
  have hstable : (prefixWord ++ tailWord_5644888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644888).length < 2 ^ (prefixWord ++ tailWord_5644888).sum := by decide
  have hdescent : baseEnd_5644888 < baseStart_5644888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644898 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5644898 : Nat := 118140960795 + 5644898 * 2 ^ 59
def prefixEnd_5644898 : Nat := 4983230072969 + 3 ^ 40 * 5644898 * 2
def baseEnd_5644898 : Nat := 966181973201253514771531

theorem tailTrace_5644898 : CollatzResearch.WordTrace tailWord_5644898 prefixEnd_5644898 966181973201253514771531 := by
  unfold tailWord_5644898
  simp only [CollatzResearch.WordTrace]
  refine ⟨51471586075876523167457837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137257562869004061779887565 51471586075876523167457837)
  ·
    refine ⟨19301844778453696187796689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51471586075876523167457837 19301844778453696187796689)
    ·
      refine ⟨14476383583840272140847517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19301844778453696187796689 14476383583840272140847517)
      ·
        refine ⟨5428643843940102052817819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14476383583840272140847517 5428643843940102052817819)
        ·
          refine ⟨8142965765910153079226729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428643843940102052817819 8142965765910153079226729)
          ·
            refine ⟨6107224324432614809420047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142965765910153079226729 6107224324432614809420047)
            ·
              refine ⟨9160836486648922214130071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107224324432614809420047 9160836486648922214130071)
              ·
                refine ⟨13741254729973383321195107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160836486648922214130071 13741254729973383321195107)
                ·
                  refine ⟨20611882094960074981792661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13741254729973383321195107 20611882094960074981792661)
                  ·
                    refine ⟨966181973201253514771531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20611882094960074981792661 966181973201253514771531)
                    ·
                      rfl

theorem cell23_5644898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5644898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644898 prefixEnd_5644898 := by exact prefixLift 5644898
  have htrace : WordTrace (prefixWord ++ tailWord_5644898) baseStart_5644898 baseEnd_5644898 := by
    simpa [prefixWord, tailWord_5644898, baseEnd_5644898] using wordTrace_append hprefix tailTrace_5644898
  have hstable : (prefixWord ++ tailWord_5644898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644898).length < 2 ^ (prefixWord ++ tailWord_5644898).sum := by decide
  have hdescent : baseEnd_5644898 < baseStart_5644898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644901 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_5644901 : Nat := 118140960795 + 5644901 * 2 ^ 59
def prefixEnd_5644901 : Nat := 4983230072969 + 3 ^ 40 * 5644901 * 2
def baseEnd_5644901 : Nat := 2898547460045724032577079

theorem tailTrace_5644901 : CollatzResearch.WordTrace tailWord_5644901 prefixEnd_5644901 2898547460045724032577079 := by
  unfold tailWord_5644901
  simp only [CollatzResearch.WordTrace]
  refine ⟨205886453722495224182190557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137257635814996816121460371 205886453722495224182190557)
  ·
    refine ⟨77207420145935709068321459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205886453722495224182190557 77207420145935709068321459)
    ·
      refine ⟨115811130218903563602482189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77207420145935709068321459 115811130218903563602482189)
      ·
        refine ⟨43429173832088836350930821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115811130218903563602482189 43429173832088836350930821)
        ·
          refine ⟨8142970093516656815799529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43429173832088836350930821 8142970093516656815799529)
          ·
            refine ⟨6107227570137492611849647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142970093516656815799529 6107227570137492611849647)
            ·
              refine ⟨9160841355206238917774471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107227570137492611849647 9160841355206238917774471)
              ·
                refine ⟨13741262032809358376661707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160841355206238917774471 13741262032809358376661707)
                ·
                  refine ⟨20611893049214037564992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13741262032809358376661707 20611893049214037564992561)
                  ·
                    refine ⟨15458919786910528173744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20611893049214037564992561 15458919786910528173744421)
                    ·
                      refine ⟨2898547460045724032577079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15458919786910528173744421 2898547460045724032577079)
                      ·
                        rfl

theorem cell23_5644901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_5644901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644901 prefixEnd_5644901 := by exact prefixLift 5644901
  have htrace : WordTrace (prefixWord ++ tailWord_5644901) baseStart_5644901 baseEnd_5644901 := by
    simpa [prefixWord, tailWord_5644901, baseEnd_5644901] using wordTrace_append hprefix tailTrace_5644901
  have hstable : (prefixWord ++ tailWord_5644901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644901).length < 2 ^ (prefixWord ++ tailWord_5644901).sum := by decide
  have hdescent : baseEnd_5644901 < baseStart_5644901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644931 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 1, 3, 2]
def baseStart_5644931 : Nat := 118140960795 + 5644931 * 2 ^ 59
def prefixEnd_5644931 : Nat := 4983230072969 + 3 ^ 40 * 5644931 * 2
def baseEnd_5644931 : Nat := 2898562864465358915201941

theorem tailTrace_5644931 : CollatzResearch.WordTrace tailWord_5644931 prefixEnd_5644931 2898562864465358915201941 := by
  unfold tailWord_5644931
  simp only [CollatzResearch.WordTrace]
  refine ⟨205887547912386539305782647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137258365274924359537188431 205887547912386539305782647)
  ·
    refine ⟨308831321868579808958673971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205887547912386539305782647 308831321868579808958673971)
    ·
      refine ⟨463246982802869713438010957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308831321868579808958673971 463246982802869713438010957)
      ·
        refine ⟨173717618551076142539254109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463246982802869713438010957 173717618551076142539254109)
        ·
          refine ⟨65144106956653553452220291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173717618551076142539254109 65144106956653553452220291)
          ·
            refine ⟨97716160434980330178330437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65144106956653553452220291 97716160434980330178330437)
            ·
              refine ⟨18321780081558811908436957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97716160434980330178330437 18321780081558811908436957)
              ·
                refine ⟨6870667530584554465663859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18321780081558811908436957 6870667530584554465663859)
                ·
                  refine ⟨10306001295876831698495789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870667530584554465663859 10306001295876831698495789)
                  ·
                    refine ⟨3864750485953811886935921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10306001295876831698495789 3864750485953811886935921)
                    ·
                      refine ⟨2898562864465358915201941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3864750485953811886935921 2898562864465358915201941)
                      ·
                        rfl

theorem cell23_5644931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_5644931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644931 prefixEnd_5644931 := by exact prefixLift 5644931
  have htrace : WordTrace (prefixWord ++ tailWord_5644931) baseStart_5644931 baseEnd_5644931 := by
    simpa [prefixWord, tailWord_5644931, baseEnd_5644931] using wordTrace_append hprefix tailTrace_5644931
  have hstable : (prefixWord ++ tailWord_5644931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644931).length < 2 ^ (prefixWord ++ tailWord_5644931).sum := by decide
  have hdescent : baseEnd_5644931 < baseStart_5644931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5644947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3]
def baseStart_5644947 : Nat := 118140960795 + 5644947 * 2 ^ 59
def prefixEnd_5644947 : Nat := 4983230072969 + 3 ^ 40 * 5644947 * 2
def baseEnd_5644947 : Nat := 2898571080155830852601867

theorem tailTrace_5644947 : CollatzResearch.WordTrace tailWord_5644947 prefixEnd_5644947 2898571080155830852601867 := by
  unfold tailWord_5644947
  simp only [CollatzResearch.WordTrace]
  refine ⟨205888131480328574038365095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137258754320219049358910063 205888131480328574038365095)
  ·
    refine ⟨308832197220492861057547643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205888131480328574038365095 308832197220492861057547643)
    ·
      refine ⟨463248295830739291586321465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308832197220492861057547643 463248295830739291586321465)
      ·
        refine ⟨347436221873054468689741099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463248295830739291586321465 347436221873054468689741099)
        ·
          refine ⟨521154332809581703034611649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347436221873054468689741099 521154332809581703034611649)
          ·
            refine ⟨390865749607186277275958737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521154332809581703034611649 390865749607186277275958737)
            ·
              refine ⟨293149312205389707956969053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390865749607186277275958737 293149312205389707956969053)
              ·
                refine ⟨109930992077021140483863395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293149312205389707956969053 109930992077021140483863395)
                ·
                  refine ⟨164896488115531710725795093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109930992077021140483863395 164896488115531710725795093)
                  ·
                    refine ⟨7729522880415548940271645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164896488115531710725795093 7729522880415548940271645)
                    ·
                      refine ⟨2898571080155830852601867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7729522880415548940271645 2898571080155830852601867)
                      ·
                        rfl

theorem cell23_5644947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_5644947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5644947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5644947 prefixEnd_5644947 := by exact prefixLift 5644947
  have htrace : WordTrace (prefixWord ++ tailWord_5644947) baseStart_5644947 baseEnd_5644947 := by
    simpa [prefixWord, tailWord_5644947, baseEnd_5644947] using wordTrace_append hprefix tailTrace_5644947
  have hstable : (prefixWord ++ tailWord_5644947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5644947).length < 2 ^ (prefixWord ++ tailWord_5644947).sum := by decide
  have hdescent : baseEnd_5644947 < baseStart_5644947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5644947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645134 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_5645134 : Nat := 118140960795 + 5645134 * 2 ^ 59
def prefixEnd_5645134 : Nat := 4983230072969 + 3 ^ 40 * 5645134 * 2
def baseEnd_5645134 : Nat := 966222367012740540321169

theorem tailTrace_5645134 : CollatzResearch.WordTrace tailWord_5645134 prefixEnd_5645134 966222367012740540321169 := by
  unfold tailWord_5645134
  simp only [CollatzResearch.WordTrace]
  refine ⟨25736868991331388121927807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137263301287100736650281637 25736868991331388121927807)
  ·
    refine ⟨38605303486997082182891711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25736868991331388121927807 38605303486997082182891711)
    ·
      refine ⟨57907955230495623274337567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38605303486997082182891711 57907955230495623274337567)
      ·
        refine ⟨86861932845743434911506351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57907955230495623274337567 86861932845743434911506351)
        ·
          refine ⟨130292899268615152367259527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86861932845743434911506351 130292899268615152367259527)
          ·
            refine ⟨195439348902922728550889291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130292899268615152367259527 195439348902922728550889291)
            ·
              refine ⟨293159023354384092826333937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195439348902922728550889291 293159023354384092826333937)
              ·
                refine ⟨219869267515788069619750453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293159023354384092826333937 219869267515788069619750453)
                ·
                  refine ⟨20612743829605131526851605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219869267515788069619750453 20612743829605131526851605)
                  ·
                    refine ⟨966222367012740540321169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20612743829605131526851605 966222367012740540321169)
                    ·
                      rfl

theorem cell23_5645134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_5645134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645134 prefixEnd_5645134 := by exact prefixLift 5645134
  have htrace : WordTrace (prefixWord ++ tailWord_5645134) baseStart_5645134 baseEnd_5645134 := by
    simpa [prefixWord, tailWord_5645134, baseEnd_5645134] using wordTrace_append hprefix tailTrace_5645134
  have hstable : (prefixWord ++ tailWord_5645134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645134).length < 2 ^ (prefixWord ++ tailWord_5645134).sum := by decide
  have hdescent : baseEnd_5645134 < baseStart_5645134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645141 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5645141 : Nat := 118140960795 + 5645141 * 2 ^ 59
def prefixEnd_5645141 : Nat := 4983230072969 + 3 ^ 40 * 5645141 * 2
def baseEnd_5645141 : Nat := 2898670695402803093575975

theorem tailTrace_5645141 : CollatzResearch.WordTrace tailWord_5645141 prefixEnd_5645141 2898670695402803093575975 := by
  unfold tailWord_5645141
  simp only [CollatzResearch.WordTrace]
  refine ⟨205895207241625745170927277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137263471494417163447284851 205895207241625745170927277)
  ·
    refine ⟨77210702715609654439097729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205895207241625745170927277 77210702715609654439097729)
    ·
      refine ⟨57908027036707240829323297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77210702715609654439097729 57908027036707240829323297)
      ·
        refine ⟨43431020277530430621992473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57908027036707240829323297 43431020277530430621992473)
        ·
          refine ⟨32573265208147822966494355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43431020277530430621992473 32573265208147822966494355)
          ·
            refine ⟨48859897812221734449741533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32573265208147822966494355 48859897812221734449741533)
            ·
              refine ⟨18322461679583150418653075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48859897812221734449741533 18322461679583150418653075)
              ·
                refine ⟨27483692519374725627979613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18322461679583150418653075 27483692519374725627979613)
                ·
                  refine ⟨10306384694765522110492355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27483692519374725627979613 10306384694765522110492355)
                  ·
                    refine ⟨15459577042148283165738533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10306384694765522110492355 15459577042148283165738533)
                    ·
                      refine ⟨2898670695402803093575975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15459577042148283165738533 2898670695402803093575975)
                      ·
                        rfl

theorem cell23_5645141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5645141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645141 prefixEnd_5645141 := by exact prefixLift 5645141
  have htrace : WordTrace (prefixWord ++ tailWord_5645141) baseStart_5645141 baseEnd_5645141 := by
    simpa [prefixWord, tailWord_5645141, baseEnd_5645141] using wordTrace_append hprefix tailTrace_5645141
  have hstable : (prefixWord ++ tailWord_5645141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645141).length < 2 ^ (prefixWord ++ tailWord_5645141).sum := by decide
  have hdescent : baseEnd_5645141 < baseStart_5645141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645144 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5645144 : Nat := 118140960795 + 5645144 * 2 ^ 59
def prefixEnd_5645144 : Nat := 4983230072969 + 3 ^ 40 * 5645144 * 2
def baseEnd_5645144 : Nat := 2898672235844766581838461

theorem tailTrace_5645144 : CollatzResearch.WordTrace tailWord_5645144 prefixEnd_5645144 2898672235844766581838461 := by
  unfold tailWord_5645144
  simp only [CollatzResearch.WordTrace]
  refine ⟨102947658330307438341643243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137263544440409917788857657 102947658330307438341643243)
  ·
    refine ⟨154421487495461157512464865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102947658330307438341643243 154421487495461157512464865)
    ·
      refine ⟨115816115621595868134348649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154421487495461157512464865 115816115621595868134348649)
      ·
        refine ⟨86862086716196901100761487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115816115621595868134348649 86862086716196901100761487)
        ·
          refine ⟨130293130074295351651142231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86862086716196901100761487 130293130074295351651142231)
          ·
            refine ⟨195439695111443027476713347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130293130074295351651142231 195439695111443027476713347)
            ·
              refine ⟨293159542667164541215070021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195439695111443027476713347 293159542667164541215070021)
              ·
                refine ⟨54967414250093351477825629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293159542667164541215070021 54967414250093351477825629)
                ·
                  refine ⟨20612780343785006804184611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54967414250093351477825629 20612780343785006804184611)
                  ·
                    refine ⟨30919170515677510206276917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20612780343785006804184611 30919170515677510206276917)
                    ·
                      refine ⟨2898672235844766581838461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30919170515677510206276917 2898672235844766581838461)
                      ·
                        rfl

theorem cell23_5645144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5645144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645144 prefixEnd_5645144 := by exact prefixLift 5645144
  have htrace : WordTrace (prefixWord ++ tailWord_5645144) baseStart_5645144 baseEnd_5645144 := by
    simpa [prefixWord, tailWord_5645144, baseEnd_5645144] using wordTrace_append hprefix tailTrace_5645144
  have hstable : (prefixWord ++ tailWord_5645144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645144).length < 2 ^ (prefixWord ++ tailWord_5645144).sum := by decide
  have hdescent : baseEnd_5645144 < baseStart_5645144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645241 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 6]
def baseStart_5645241 : Nat := 118140960795 + 5645241 * 2 ^ 59
def prefixEnd_5645241 : Nat := 4983230072969 + 3 ^ 40 * 5645241 * 2
def baseEnd_5645241 : Nat := 966240681156084234108505

theorem tailTrace_5645241 : CollatzResearch.WordTrace tailWord_5645241 prefixEnd_5645241 966240681156084234108505 := by
  unfold tailWord_5645241
  simp only [CollatzResearch.WordTrace]
  refine ⟨205898854541263462249567577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137265903027508974833045051 205898854541263462249567577)
  ·
    refine ⟨154424140905947596687175683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205898854541263462249567577 154424140905947596687175683)
    ·
      refine ⟨231636211358921395030763525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154424140905947596687175683 231636211358921395030763525)
      ·
        refine ⟨43431789629797761568268161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231636211358921395030763525 43431789629797761568268161)
        ·
          refine ⟨32573842222348321176201121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43431789629797761568268161 32573842222348321176201121)
          ·
            refine ⟨24430381666761240882150841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32573842222348321176201121 24430381666761240882150841)
            ·
              refine ⟨18322786250070930661613131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24430381666761240882150841 18322786250070930661613131)
              ·
                refine ⟨27484179375106395992419697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18322786250070930661613131 27484179375106395992419697)
                ·
                  refine ⟨20613134531329796994314773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27484179375106395992419697 20613134531329796994314773)
                  ·
                    refine ⟨966240681156084234108505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20613134531329796994314773 966240681156084234108505)
                    ·
                      rfl

theorem cell23_5645241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_5645241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645241 prefixEnd_5645241 := by exact prefixLift 5645241
  have htrace : WordTrace (prefixWord ++ tailWord_5645241) baseStart_5645241 baseEnd_5645241 := by
    simpa [prefixWord, tailWord_5645241, baseEnd_5645241] using wordTrace_append hprefix tailTrace_5645241
  have hstable : (prefixWord ++ tailWord_5645241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645241).length < 2 ^ (prefixWord ++ tailWord_5645241).sum := by decide
  have hdescent : baseEnd_5645241 < baseStart_5645241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645268 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5645268 : Nat := 118140960795 + 5645268 * 2 ^ 59
def prefixEnd_5645268 : Nat := 4983230072969 + 3 ^ 40 * 5645268 * 2
def baseEnd_5645268 : Nat := 2898735907445924096687891

theorem tailTrace_5645268 : CollatzResearch.WordTrace tailWord_5645268 prefixEnd_5645268 2898735907445924096687891 := by
  unfold tailWord_5645268
  simp only [CollatzResearch.WordTrace]
  refine ⟨102949919656082822930400229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137266559541443763907200305 102949919656082822930400229)
  ·
    refine ⟨19303109935515529299450043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102949919656082822930400229 19303109935515529299450043)
    ·
      refine ⟨28954664903273293949175065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19303109935515529299450043 28954664903273293949175065)
      ·
        refine ⟨21715998677454970461881299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28954664903273293949175065 21715998677454970461881299)
        ·
          refine ⟨32573998016182455692821949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21715998677454970461881299 32573998016182455692821949)
          ·
            refine ⟨12215249256068420884808231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32573998016182455692821949 12215249256068420884808231)
            ·
              refine ⟨18322873884102631327212347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12215249256068420884808231 18322873884102631327212347)
              ·
                refine ⟨27484310826153946990818521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18322873884102631327212347 27484310826153946990818521)
                ·
                  refine ⟨20613233119615460243113891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27484310826153946990818521 20613233119615460243113891)
                  ·
                    refine ⟨30919849679423190364670837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20613233119615460243113891 30919849679423190364670837)
                    ·
                      refine ⟨2898735907445924096687891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30919849679423190364670837 2898735907445924096687891)
                      ·
                        rfl

theorem cell23_5645268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5645268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645268 prefixEnd_5645268 := by exact prefixLift 5645268
  have htrace : WordTrace (prefixWord ++ tailWord_5645268) baseStart_5645268 baseEnd_5645268 := by
    simpa [prefixWord, tailWord_5645268, baseEnd_5645268] using wordTrace_append hprefix tailTrace_5645268
  have hstable : (prefixWord ++ tailWord_5645268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645268).length < 2 ^ (prefixWord ++ tailWord_5645268).sum := by decide
  have hdescent : baseEnd_5645268 < baseStart_5645268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645288 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 5]
def baseStart_5645288 : Nat := 118140960795 + 5645288 * 2 ^ 59
def prefixEnd_5645288 : Nat := 4983230072969 + 3 ^ 40 * 5645288 * 2
def baseEnd_5645288 : Nat := 322082908562112668715311

theorem tailTrace_5645288 : CollatzResearch.WordTrace tailWord_5645288 prefixEnd_5645288 322082908562112668715311 := by
  unfold tailWord_5645288
  simp only [CollatzResearch.WordTrace]
  refine ⟨102950284386046594638264259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137267045848062126184352345 102950284386046594638264259)
  ·
    refine ⟨154425426579069891957396389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102950284386046594638264259 154425426579069891957396389)
    ·
      refine ⟨28954767483575604742011823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154425426579069891957396389 28954767483575604742011823)
      ·
        refine ⟨43432151225363407113017735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28954767483575604742011823 43432151225363407113017735)
        ·
          refine ⟨65148226838045110669526603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43432151225363407113017735 65148226838045110669526603)
          ·
            refine ⟨97722340257067666004289905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65148226838045110669526603 97722340257067666004289905)
            ·
              refine ⟨73291755192800749503217429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97722340257067666004289905 73291755192800749503217429)
              ·
                refine ⟨3435551024662535132963317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73291755192800749503217429 3435551024662535132963317)
                ·
                  refine ⟨322082908562112668715311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3435551024662535132963317 322082908562112668715311)
                  ·
                    rfl

theorem cell23_5645288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 5].length) (baseStart_5645288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645288 prefixEnd_5645288 := by exact prefixLift 5645288
  have htrace : WordTrace (prefixWord ++ tailWord_5645288) baseStart_5645288 baseEnd_5645288 := by
    simpa [prefixWord, tailWord_5645288, baseEnd_5645288] using wordTrace_append hprefix tailTrace_5645288
  have hstable : (prefixWord ++ tailWord_5645288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645288).length < 2 ^ (prefixWord ++ tailWord_5645288).sum := by decide
  have hdescent : baseEnd_5645288 < baseStart_5645288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645321 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_5645321 : Nat := 118140960795 + 5645321 * 2 ^ 59
def prefixEnd_5645321 : Nat := 4983230072969 + 3 ^ 40 * 5645321 * 2
def baseEnd_5645321 : Nat := 2898763121920612389325147

theorem tailTrace_5645321 : CollatzResearch.WordTrace tailWord_5645321 prefixEnd_5645321 2898763121920612389325147 := by
  unfold tailWord_5645321
  simp only [CollatzResearch.WordTrace]
  refine ⟨205901772380973635912479817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137267848253982423941653211 205901772380973635912479817)
  ·
    refine ⟨154426329285730226934359863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205901772380973635912479817 154426329285730226934359863)
    ·
      refine ⟨231639493928595340401539795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154426329285730226934359863 231639493928595340401539795)
      ·
        refine ⟨347459240892893010602309693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231639493928595340401539795 347459240892893010602309693)
        ·
          refine ⟨130297215334834878975866135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347459240892893010602309693 130297215334834878975866135)
          ·
            refine ⟨195445823002252318463799203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130297215334834878975866135 195445823002252318463799203)
            ·
              refine ⟨293168734503378477695698805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195445823002252318463799203 293168734503378477695698805)
              ·
                refine ⟨27484568859691732283971763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293168734503378477695698805 27484568859691732283971763)
                ·
                  refine ⟨41226853289537598425957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27484568859691732283971763 41226853289537598425957645)
                  ·
                    refine ⟨15460069983576599409734117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41226853289537598425957645 15460069983576599409734117)
                    ·
                      refine ⟨2898763121920612389325147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15460069983576599409734117 2898763121920612389325147)
                      ·
                        rfl

theorem cell23_5645321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_5645321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645321 prefixEnd_5645321 := by exact prefixLift 5645321
  have htrace : WordTrace (prefixWord ++ tailWord_5645321) baseStart_5645321 baseEnd_5645321 := by
    simpa [prefixWord, tailWord_5645321, baseEnd_5645321] using wordTrace_append hprefix tailTrace_5645321
  have hstable : (prefixWord ++ tailWord_5645321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645321).length < 2 ^ (prefixWord ++ tailWord_5645321).sum := by decide
  have hdescent : baseEnd_5645321 < baseStart_5645321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645338 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_5645338 : Nat := 118140960795 + 5645338 * 2 ^ 59
def prefixEnd_5645338 : Nat := 4983230072969 + 3 ^ 40 * 5645338 * 2
def baseEnd_5645338 : Nat := 2898771851091738822812569

theorem tailTrace_5645338 : CollatzResearch.WordTrace tailWord_5645338 prefixEnd_5645338 2898771851091738822812569 := by
  unfold tailWord_5645338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51475598105478011953962167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137268261614608031877232445 51475598105478011953962167)
  ·
    refine ⟨77213397158217017930943251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51475598105478011953962167 77213397158217017930943251)
    ·
      refine ⟨115820095737325526896414877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77213397158217017930943251 115820095737325526896414877)
      ·
        refine ⟨43432535901497072586155579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115820095737325526896414877 43432535901497072586155579)
        ·
          refine ⟨65148803852245608879233369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43432535901497072586155579 65148803852245608879233369)
          ·
            refine ⟨48861602889184206659425027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65148803852245608879233369 48861602889184206659425027)
            ·
              refine ⟨73292404333776309989137541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48861602889184206659425027 73292404333776309989137541)
              ·
                refine ⟨13742325812583058122963289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73292404333776309989137541 13742325812583058122963289)
                ·
                  refine ⟨10306744359437293592222467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13742325812583058122963289 10306744359437293592222467)
                  ·
                    refine ⟨15460116539155940388333701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10306744359437293592222467 15460116539155940388333701)
                    ·
                      refine ⟨2898771851091738822812569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15460116539155940388333701 2898771851091738822812569)
                      ·
                        rfl

theorem cell23_5645338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_5645338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645338 prefixEnd_5645338 := by exact prefixLift 5645338
  have htrace : WordTrace (prefixWord ++ tailWord_5645338) baseStart_5645338 baseEnd_5645338 := by
    simpa [prefixWord, tailWord_5645338, baseEnd_5645338] using wordTrace_append hprefix tailTrace_5645338
  have hstable : (prefixWord ++ tailWord_5645338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645338).length < 2 ^ (prefixWord ++ tailWord_5645338).sum := by decide
  have hdescent : baseEnd_5645338 < baseStart_5645338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645401 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_5645401 : Nat := 118140960795 + 5645401 * 2 ^ 59
def prefixEnd_5645401 : Nat := 4983230072969 + 3 ^ 40 * 5645401 * 2
def baseEnd_5645401 : Nat := 2898804200372972076324779

theorem tailTrace_5645401 : CollatzResearch.WordTrace tailWord_5645401 prefixEnd_5645401 2898804200372972076324779 := by
  unfold tailWord_5645401
  simp only [CollatzResearch.WordTrace]
  refine ⟨205904690220683809575392057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137269793480455873050261371 205904690220683809575392057)
  ·
    refine ⟨154428517665512857181544043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205904690220683809575392057 154428517665512857181544043)
    ·
      refine ⟨231642776498269285772316065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154428517665512857181544043 231642776498269285772316065)
      ·
        refine ⟨173732082373701964329237049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231642776498269285772316065 173732082373701964329237049)
        ·
          refine ⟨130299061780276473246927787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173732082373701964329237049 130299061780276473246927787)
          ·
            refine ⟨195448592670414709870391681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130299061780276473246927787 195448592670414709870391681)
            ·
              refine ⟨146586444502811032402793761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195448592670414709870391681 146586444502811032402793761)
              ·
                refine ⟨109939833377108274302095321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146586444502811032402793761 109939833377108274302095321)
                ·
                  refine ⟨82454875032831205726571491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109939833377108274302095321 82454875032831205726571491)
                  ·
                    refine ⟨123682312549246808589857237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82454875032831205726571491 123682312549246808589857237)
                    ·
                      refine ⟨2898804200372972076324779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123682312549246808589857237 2898804200372972076324779)
                      ·
                        rfl

theorem cell23_5645401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_5645401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645401 prefixEnd_5645401 := by exact prefixLift 5645401
  have htrace : WordTrace (prefixWord ++ tailWord_5645401) baseStart_5645401 baseEnd_5645401 := by
    simpa [prefixWord, tailWord_5645401, baseEnd_5645401] using wordTrace_append hprefix tailTrace_5645401
  have hstable : (prefixWord ++ tailWord_5645401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645401).length < 2 ^ (prefixWord ++ tailWord_5645401).sum := by decide
  have hdescent : baseEnd_5645401 < baseStart_5645401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645415 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_5645415 : Nat := 118140960795 + 5645415 * 2 ^ 59
def prefixEnd_5645415 : Nat := 4983230072969 + 3 ^ 40 * 5645415 * 2
def baseEnd_5645415 : Nat := 2898811389102135021549715

theorem tailTrace_5645415 : CollatzResearch.WordTrace tailWord_5645415 prefixEnd_5645415 2898811389102135021549715 := by
  unfold tailWord_5645415
  simp only [CollatzResearch.WordTrace]
  refine ⟨205905200842633089966401699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137270133895088726644267799 205905200842633089966401699)
  ·
    refine ⟨308857801263949634949602549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205905200842633089966401699 308857801263949634949602549)
    ·
      refine ⟨28955418868495278276525239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308857801263949634949602549 28955418868495278276525239)
      ·
        refine ⟨43433128302742917414787859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28955418868495278276525239 43433128302742917414787859)
        ·
          refine ⟨65149692454114376122181789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43433128302742917414787859 65149692454114376122181789)
          ·
            refine ⟨24431134670292891045818171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65149692454114376122181789 24431134670292891045818171)
            ·
              refine ⟨36646702005439336568727257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24431134670292891045818171 36646702005439336568727257)
              ·
                refine ⟨27485026504079502426545443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36646702005439336568727257 27485026504079502426545443)
                ·
                  refine ⟨41227539756119253639818165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27485026504079502426545443 41227539756119253639818165)
                  ·
                    refine ⟨3865081852136180028732953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41227539756119253639818165 3865081852136180028732953)
                    ·
                      refine ⟨2898811389102135021549715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865081852136180028732953 2898811389102135021549715)
                      ·
                        rfl

theorem cell23_5645415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_5645415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645415 prefixEnd_5645415 := by exact prefixLift 5645415
  have htrace : WordTrace (prefixWord ++ tailWord_5645415) baseStart_5645415 baseEnd_5645415 := by
    simpa [prefixWord, tailWord_5645415, baseEnd_5645415] using wordTrace_append hprefix tailTrace_5645415
  have hstable : (prefixWord ++ tailWord_5645415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645415).length < 2 ^ (prefixWord ++ tailWord_5645415).sum := by decide
  have hdescent : baseEnd_5645415 < baseStart_5645415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645422 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5645422 : Nat := 118140960795 + 5645422 * 2 ^ 59
def prefixEnd_5645422 : Nat := 4983230072969 + 3 ^ 40 * 5645422 * 2
def baseEnd_5645422 : Nat := 2898814983466716494162183

theorem tailTrace_5645422 : CollatzResearch.WordTrace tailWord_5645422 prefixEnd_5645422 2898814983466716494162183 := by
  unfold tailWord_5645422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25738182019200966270238315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137270304102405153441271013 25738182019200966270238315)
  ·
    refine ⟨38607273028801449405357473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25738182019200966270238315 38607273028801449405357473)
    ·
      refine ⟨28955454771601087054018105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38607273028801449405357473 28955454771601087054018105)
      ·
        refine ⟨21716591078700815290513579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28955454771601087054018105 21716591078700815290513579)
        ·
          refine ⟨32574886618051222935770369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21716591078700815290513579 32574886618051222935770369)
          ·
            refine ⟨24431164963538417201827777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32574886618051222935770369 24431164963538417201827777)
            ·
              refine ⟨18323373722653812901370833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24431164963538417201827777 18323373722653812901370833)
              ·
                refine ⟨13742530291990359676028125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18323373722653812901370833 13742530291990359676028125)
                ·
                  refine ⟨5153448859496384878510547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13742530291990359676028125 5153448859496384878510547)
                  ·
                    refine ⟨7730173289244577317765821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5153448859496384878510547 7730173289244577317765821)
                    ·
                      refine ⟨2898814983466716494162183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730173289244577317765821 2898814983466716494162183)
                      ·
                        rfl

theorem cell23_5645422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5645422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645422 prefixEnd_5645422 := by exact prefixLift 5645422
  have htrace : WordTrace (prefixWord ++ tailWord_5645422) baseStart_5645422 baseEnd_5645422 := by
    simpa [prefixWord, tailWord_5645422, baseEnd_5645422] using wordTrace_append hprefix tailTrace_5645422
  have hstable : (prefixWord ++ tailWord_5645422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645422).length < 2 ^ (prefixWord ++ tailWord_5645422).sum := by decide
  have hdescent : baseEnd_5645422 < baseStart_5645422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645468 : List Nat := [2, 2, 3, 2, 1, 2, 1, 10]
def baseStart_5645468 : Nat := 118140960795 + 5645468 * 2 ^ 59
def prefixEnd_5645468 : Nat := 4983230072969 + 3 ^ 40 * 5645468 * 2
def baseEnd_5645468 : Nat := 107364392725067530155073

theorem tailTrace_5645468 : CollatzResearch.WordTrace tailWord_5645468 prefixEnd_5645468 107364392725067530155073 := by
  unfold tailWord_5645468
  simp only [CollatzResearch.WordTrace]
  refine ⟨102953566955720540009040529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137271422607627386678720705 102953566955720540009040529)
  ·
    refine ⟨77215175216790405006780397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102953566955720540009040529 77215175216790405006780397)
    ·
      refine ⟨28955690706296401877542649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77215175216790405006780397 28955690706296401877542649)
      ·
        refine ⟨21716768029722301408156987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28955690706296401877542649 21716768029722301408156987)
        ·
          refine ⟨32575152044583452112235481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21716768029722301408156987 32575152044583452112235481)
          ·
            refine ⟨24431364033437589084176611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32575152044583452112235481 24431364033437589084176611)
            ·
              refine ⟨36647046050156383626264917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24431364033437589084176611 36647046050156383626264917)
              ·
                refine ⟨107364392725067530155073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36647046050156383626264917 107364392725067530155073)
                ·
                  rfl

theorem cell23_5645468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 10].length) (baseStart_5645468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645468 prefixEnd_5645468 := by exact prefixLift 5645468
  have htrace : WordTrace (prefixWord ++ tailWord_5645468) baseStart_5645468 baseEnd_5645468 := by
    simpa [prefixWord, tailWord_5645468, baseEnd_5645468] using wordTrace_append hprefix tailTrace_5645468
  have hstable : (prefixWord ++ tailWord_5645468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645468).length < 2 ^ (prefixWord ++ tailWord_5645468).sum := by decide
  have hdescent : baseEnd_5645468 < baseStart_5645468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645479 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5645479 : Nat := 118140960795 + 5645479 * 2 ^ 59
def prefixEnd_5645479 : Nat := 4983230072969 + 3 ^ 40 * 5645479 * 2
def baseEnd_5645479 : Nat := 2898844251864022771149421

theorem tailTrace_5645479 : CollatzResearch.WordTrace tailWord_5645479 prefixEnd_5645479 2898844251864022771149421 := by
  unfold tailWord_5645479
  simp only [CollatzResearch.WordTrace]
  refine ⟨205907535114401228896731491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137271690076267485931154327 205907535114401228896731491)
  ·
    refine ⟨308861302671601843345097237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205907535114401228896731491 308861302671601843345097237)
    ·
      refine ⟨14477873562731336406801433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 308861302671601843345097237 14477873562731336406801433)
      ·
        refine ⟨10858405172048502305101075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14477873562731336406801433 10858405172048502305101075)
        ·
          refine ⟨16287607758072753457651613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10858405172048502305101075 16287607758072753457651613)
          ·
            refine ⟨6107852909277282546619355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16287607758072753457651613 6107852909277282546619355)
            ·
              refine ⟨9161779363915923819929033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107852909277282546619355 9161779363915923819929033)
              ·
                refine ⟨6871334522936942864946775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9161779363915923819929033 6871334522936942864946775)
                ·
                  refine ⟨10307001784405414297420163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6871334522936942864946775 10307001784405414297420163)
                  ·
                    refine ⟨15460502676608121446130245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10307001784405414297420163 15460502676608121446130245)
                    ·
                      refine ⟨2898844251864022771149421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15460502676608121446130245 2898844251864022771149421)
                      ·
                        rfl

theorem cell23_5645479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5645479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645479 prefixEnd_5645479 := by exact prefixLift 5645479
  have htrace : WordTrace (prefixWord ++ tailWord_5645479) baseStart_5645479 baseEnd_5645479 := by
    simpa [prefixWord, tailWord_5645479, baseEnd_5645479] using wordTrace_append hprefix tailTrace_5645479
  have hstable : (prefixWord ++ tailWord_5645479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645479).length < 2 ^ (prefixWord ++ tailWord_5645479).sum := by decide
  have hdescent : baseEnd_5645479 < baseStart_5645479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645495 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_5645495 : Nat := 118140960795 + 5645495 * 2 ^ 59
def prefixEnd_5645495 : Nat := 4983230072969 + 3 ^ 40 * 5645495 * 2
def baseEnd_5645495 : Nat := 2898852467554494708549347

theorem tailTrace_5645495 : CollatzResearch.WordTrace tailWord_5645495 prefixEnd_5645495 2898852467554494708549347 := by
  unfold tailWord_5645495
  simp only [CollatzResearch.WordTrace]
  refine ⟨205908118682343263629313939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137272079121562175752875959 205908118682343263629313939)
  ·
    refine ⟨308862178023514895443970909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205908118682343263629313939 308862178023514895443970909)
    ·
      refine ⟨115823316758818085791489091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308862178023514895443970909 115823316758818085791489091)
      ·
        refine ⟨173734975138227128687233637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115823316758818085791489091 173734975138227128687233637)
        ·
          refine ⟨32575307838417586628856307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173734975138227128687233637 32575307838417586628856307)
          ·
            refine ⟨48862961757626379943284461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32575307838417586628856307 48862961757626379943284461)
            ·
              refine ⟨18323610659109892478731673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48862961757626379943284461 18323610659109892478731673)
              ·
                refine ⟨13742707994332419359048755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18323610659109892478731673 13742707994332419359048755)
                ·
                  refine ⟨20614061991498629038573133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13742707994332419359048755 20614061991498629038573133)
                  ·
                    refine ⟨7730273246811985889464925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20614061991498629038573133 7730273246811985889464925)
                    ·
                      refine ⟨2898852467554494708549347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730273246811985889464925 2898852467554494708549347)
                      ·
                        rfl

theorem cell23_5645495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_5645495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645495 prefixEnd_5645495 := by exact prefixLift 5645495
  have htrace : WordTrace (prefixWord ++ tailWord_5645495) baseStart_5645495 baseEnd_5645495 := by
    simpa [prefixWord, tailWord_5645495, baseEnd_5645495] using wordTrace_append hprefix tailTrace_5645495
  have hstable : (prefixWord ++ tailWord_5645495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645495).length < 2 ^ (prefixWord ++ tailWord_5645495).sum := by decide
  have hdescent : baseEnd_5645495 < baseStart_5645495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645512 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_5645512 : Nat := 118140960795 + 5645512 * 2 ^ 59
def prefixEnd_5645512 : Nat := 4983230072969 + 3 ^ 40 * 5645512 * 2
def baseEnd_5645512 : Nat := 2898861196725621142036769

theorem tailTrace_5645512 : CollatzResearch.WordTrace tailWord_5645512 prefixEnd_5645512 2898861196725621142036769 := by
  unfold tailWord_5645512
  simp only [CollatzResearch.WordTrace]
  refine ⟨102954369361640837766341395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137272492482187783688455193 102954369361640837766341395)
  ·
    refine ⟨154431554042461256649512093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102954369361640837766341395 154431554042461256649512093)
    ·
      refine ⟨57911832765922971243567035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154431554042461256649512093 57911832765922971243567035)
      ·
        refine ⟨86867749148884456865350553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57911832765922971243567035 86867749148884456865350553)
        ·
          refine ⟨65150811861663342649012915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86867749148884456865350553 65150811861663342649012915)
          ·
            refine ⟨97726217792495013973519373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65150811861663342649012915 97726217792495013973519373)
            ·
              refine ⟨36647331672185630240069765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97726217792495013973519373 36647331672185630240069765)
              ·
                refine ⟨6871374688534805670013081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36647331672185630240069765 6871374688534805670013081)
                ·
                  refine ⟨5153531016401104252509811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6871374688534805670013081 5153531016401104252509811)
                  ·
                    refine ⟨7730296524601656378764717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5153531016401104252509811 7730296524601656378764717)
                    ·
                      refine ⟨2898861196725621142036769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730296524601656378764717 2898861196725621142036769)
                      ·
                        rfl

theorem cell23_5645512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_5645512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645512 prefixEnd_5645512 := by exact prefixLift 5645512
  have htrace : WordTrace (prefixWord ++ tailWord_5645512) baseStart_5645512 baseEnd_5645512 := by
    simpa [prefixWord, tailWord_5645512, baseEnd_5645512] using wordTrace_append hprefix tailTrace_5645512
  have hstable : (prefixWord ++ tailWord_5645512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645512).length < 2 ^ (prefixWord ++ tailWord_5645512).sum := by decide
  have hdescent : baseEnd_5645512 < baseStart_5645512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645522 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5645522 : Nat := 118140960795 + 5645522 * 2 ^ 59
def prefixEnd_5645522 : Nat := 4983230072969 + 3 ^ 40 * 5645522 * 2
def baseEnd_5645522 : Nat := 2898866331532166102911723

theorem tailTrace_5645522 : CollatzResearch.WordTrace tailWord_5645522 prefixEnd_5645522 2898866331532166102911723 := by
  unfold tailWord_5645522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51477275863311361810136705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137272735635496964827031213 51477275863311361810136705)
  ·
    refine ⟨38607956897483521357602529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51477275863311361810136705 38607956897483521357602529)
    ·
      refine ⟨28955967673112641018201897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38607956897483521357602529 28955967673112641018201897)
      ·
        refine ⟨21716975754834480763651423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28955967673112641018201897 21716975754834480763651423)
        ·
          refine ⟨32575463632251721145477135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21716975754834480763651423 32575463632251721145477135)
          ·
            refine ⟨48863195448377581718215703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32575463632251721145477135 48863195448377581718215703)
            ·
              refine ⟨73294793172566372577323555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48863195448377581718215703 73294793172566372577323555)
              ·
                refine ⟨109942189758849558865985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73294793172566372577323555 109942189758849558865985333)
                ·
                  refine ⟨10307080289892146143686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109942189758849558865985333 10307080289892146143686125)
                  ·
                    refine ⟨3865155108709554803882297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10307080289892146143686125 3865155108709554803882297)
                    ·
                      refine ⟨2898866331532166102911723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865155108709554803882297 2898866331532166102911723)
                      ·
                        rfl

theorem cell23_5645522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5645522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645522 prefixEnd_5645522 := by exact prefixLift 5645522
  have htrace : WordTrace (prefixWord ++ tailWord_5645522) baseStart_5645522 baseEnd_5645522 := by
    simpa [prefixWord, tailWord_5645522, baseEnd_5645522] using wordTrace_append hprefix tailTrace_5645522
  have hstable : (prefixWord ++ tailWord_5645522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645522).length < 2 ^ (prefixWord ++ tailWord_5645522).sum := by decide
  have hdescent : baseEnd_5645522 < baseStart_5645522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645569 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_5645569 : Nat := 118140960795 + 5645569 * 2 ^ 59
def prefixEnd_5645569 : Nat := 4983230072969 + 3 ^ 40 * 5645569 * 2
def baseEnd_5645569 : Nat := 2898890465122927419024007

theorem tailTrace_5645569 : CollatzResearch.WordTrace tailWord_5645569 prefixEnd_5645569 2898890465122927419024007 := by
  unfold tailWord_5645569
  simp only [CollatzResearch.WordTrace]
  refine ⟨205910817684075174267507761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137273878456050116178338507 205910817684075174267507761)
  ·
    refine ⟨154433113263056380700630821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205910817684075174267507761 154433113263056380700630821)
    ·
      refine ⟨28956208736823071381368279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154433113263056380700630821 28956208736823071381368279)
      ·
        refine ⟨43434313105234607072052419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28956208736823071381368279 43434313105234607072052419)
        ·
          refine ⟨65151469657851910608078629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43434313105234607072052419 65151469657851910608078629)
          ·
            refine ⟨12215900560847233239014743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65151469657851910608078629 12215900560847233239014743)
            ·
              refine ⟨18323850841270849858522115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12215900560847233239014743 18323850841270849858522115)
              ·
                refine ⟨27485776261906274787783173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18323850841270849858522115 27485776261906274787783173)
                ·
                  refine ⟨5153583049107426522709345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27485776261906274787783173 5153583049107426522709345)
                  ·
                    refine ⟨3865187286830569892032009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5153583049107426522709345 3865187286830569892032009)
                    ·
                      refine ⟨2898890465122927419024007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865187286830569892032009 2898890465122927419024007)
                      ·
                        rfl

theorem cell23_5645569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_5645569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645569 prefixEnd_5645569 := by exact prefixLift 5645569
  have htrace : WordTrace (prefixWord ++ tailWord_5645569) baseStart_5645569 baseEnd_5645569 := by
    simpa [prefixWord, tailWord_5645569, baseEnd_5645569] using wordTrace_append hprefix tailTrace_5645569
  have hstable : (prefixWord ++ tailWord_5645569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645569).length < 2 ^ (prefixWord ++ tailWord_5645569).sum := by decide
  have hdescent : baseEnd_5645569 < baseStart_5645569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645585 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_5645585 : Nat := 118140960795 + 5645585 * 2 ^ 59
def prefixEnd_5645585 : Nat := 4983230072969 + 3 ^ 40 * 5645585 * 2
def baseEnd_5645585 : Nat := 2898898680813399356423933

theorem tailTrace_5645585 : CollatzResearch.WordTrace tailWord_5645585 prefixEnd_5645585 2898898680813399356423933 := by
  unfold tailWord_5645585
  simp only [CollatzResearch.WordTrace]
  refine ⟨205911401252017209000090209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137274267501344806000060139 205911401252017209000090209)
  ·
    refine ⟨154433550939012906750067657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205911401252017209000090209 154433550939012906750067657)
    ·
      refine ⟨115825163204259680062550743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154433550939012906750067657 115825163204259680062550743)
      ·
        refine ⟨173737744806389520093826115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115825163204259680062550743 173737744806389520093826115)
        ·
          refine ⟨260606617209584280140739173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173737744806389520093826115 260606617209584280140739173)
          ·
            refine ⟨48863740726797052526388595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260606617209584280140739173 48863740726797052526388595)
            ·
              refine ⟨73295611090195578789582893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48863740726797052526388595 73295611090195578789582893)
              ·
                refine ⟨27485854158823342046093585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73295611090195578789582893 27485854158823342046093585)
                ·
                  refine ⟨20614390619117506534570189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27485854158823342046093585 20614390619117506534570189)
                  ·
                    refine ⟨7730396482169064950463821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20614390619117506534570189 7730396482169064950463821)
                    ·
                      refine ⟨2898898680813399356423933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730396482169064950463821 2898898680813399356423933)
                      ·
                        rfl

theorem cell23_5645585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_5645585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645585 prefixEnd_5645585 := by exact prefixLift 5645585
  have htrace : WordTrace (prefixWord ++ tailWord_5645585) baseStart_5645585 baseEnd_5645585 := by
    simpa [prefixWord, tailWord_5645585, baseEnd_5645585] using wordTrace_append hprefix tailTrace_5645585
  have hstable : (prefixWord ++ tailWord_5645585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645585).length < 2 ^ (prefixWord ++ tailWord_5645585).sum := by decide
  have hdescent : baseEnd_5645585 < baseStart_5645585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645605 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_5645605 : Nat := 118140960795 + 5645605 * 2 ^ 59
def prefixEnd_5645605 : Nat := 4983230072969 + 3 ^ 40 * 5645605 * 2
def baseEnd_5645605 : Nat := 966302983475496426057947

theorem tailTrace_5645605 : CollatzResearch.WordTrace tailWord_5645605 prefixEnd_5645605 966302983475496426057947 := by
  unfold tailWord_5645605
  simp only [CollatzResearch.WordTrace]
  refine ⟨205912130711944752415818269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137274753807963168277212179 205912130711944752415818269)
  ·
    refine ⟨77217049016979282155931851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205912130711944752415818269 77217049016979282155931851)
    ·
      refine ⟨115825573525468923233897777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77217049016979282155931851 115825573525468923233897777)
      ·
        refine ⟨86869180144101692425423333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115825573525468923233897777 86869180144101692425423333)
        ·
          refine ⟨16287971277019067329766875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86869180144101692425423333 16287971277019067329766875)
          ·
            refine ⟨24431956915528600994650313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16287971277019067329766875 24431956915528600994650313)
            ·
              refine ⟨18323967686646450745987735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24431956915528600994650313 18323967686646450745987735)
              ·
                refine ⟨27485951529969676118981603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18323967686646450745987735 27485951529969676118981603)
                ·
                  refine ⟨41228927294954514178472405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27485951529969676118981603 41228927294954514178472405)
                  ·
                    refine ⟨966302983475496426057947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41228927294954514178472405 966302983475496426057947)
                    ·
                      rfl

theorem cell23_5645605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_5645605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645605 prefixEnd_5645605 := by exact prefixLift 5645605
  have htrace : WordTrace (prefixWord ++ tailWord_5645605) baseStart_5645605 baseEnd_5645605 := by
    simpa [prefixWord, tailWord_5645605, baseEnd_5645605] using wordTrace_append hprefix tailTrace_5645605
  have hstable : (prefixWord ++ tailWord_5645605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645605).length < 2 ^ (prefixWord ++ tailWord_5645605).sum := by decide
  have hdescent : baseEnd_5645605 < baseStart_5645605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645642 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_5645642 : Nat := 118140960795 + 5645642 * 2 ^ 59
def prefixEnd_5645642 : Nat := 4983230072969 + 3 ^ 40 * 5645642 * 2
def baseEnd_5645642 : Nat := 2898927949210705633411171

theorem tailTrace_5645642 : CollatzResearch.WordTrace tailWord_5645642 prefixEnd_5645642 2898927949210705633411171 := by
  unfold tailWord_5645642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51478370053202676933728795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137275653475207138489943453 51478370053202676933728795)
  ·
    refine ⟨77217555079804015400593193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51478370053202676933728795 77217555079804015400593193)
    ·
      refine ⟨57913166309853011550444895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77217555079804015400593193 57913166309853011550444895)
      ·
        refine ⟨86869749464779517325667343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57913166309853011550444895 86869749464779517325667343)
        ·
          refine ⟨130304624197169275988501015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86869749464779517325667343 130304624197169275988501015)
          ·
            refine ⟨195456936295753913982751523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130304624197169275988501015 195456936295753913982751523)
            ·
              refine ⟨293185404443630870974127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195456936295753913982751523 293185404443630870974127285)
              ·
                refine ⟨27486131666590394153824433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293185404443630870974127285 27486131666590394153824433)
                ·
                  refine ⟨20614598749942795615368325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27486131666590394153824433 20614598749942795615368325)
                  ·
                    refine ⟨3865237265614274177881561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20614598749942795615368325 3865237265614274177881561)
                    ·
                      refine ⟨2898927949210705633411171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865237265614274177881561 2898927949210705633411171)
                      ·
                        rfl

theorem cell23_5645642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_5645642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645642 prefixEnd_5645642 := by exact prefixLift 5645642
  have htrace : WordTrace (prefixWord ++ tailWord_5645642) baseStart_5645642 baseEnd_5645642 := by
    simpa [prefixWord, tailWord_5645642, baseEnd_5645642] using wordTrace_append hprefix tailTrace_5645642
  have hstable : (prefixWord ++ tailWord_5645642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645642).length < 2 ^ (prefixWord ++ tailWord_5645642).sum := by decide
  have hdescent : baseEnd_5645642 < baseStart_5645642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645652 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_5645652 : Nat := 118140960795 + 5645652 * 2 ^ 59
def prefixEnd_5645652 : Nat := 4983230072969 + 3 ^ 40 * 5645652 * 2
def baseEnd_5645652 : Nat := 966311028005750198095375

theorem tailTrace_5645652 : CollatzResearch.WordTrace tailWord_5645652 prefixEnd_5645652 966311028005750198095375 := by
  unfold tailWord_5645652
  simp only [CollatzResearch.WordTrace]
  refine ⟨102956922471387239721389605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137275896628516319628519473 102956922471387239721389605)
  ·
    refine ⟨19304422963385107447760551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102956922471387239721389605 19304422963385107447760551)
    ·
      refine ⟨28956634445077661171640827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19304422963385107447760551 28956634445077661171640827)
      ·
        refine ⟨43434951667616491757461241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28956634445077661171640827 43434951667616491757461241)
        ·
          refine ⟨32576213750712368818095931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43434951667616491757461241 32576213750712368818095931)
          ·
            refine ⟨48864320626068553227143897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32576213750712368818095931 48864320626068553227143897)
            ·
              refine ⟨36648240469551414920357923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48864320626068553227143897 36648240469551414920357923)
              ·
                refine ⟨54972360704327122380536885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36648240469551414920357923 54972360704327122380536885)
                ·
                  refine ⟨5153658816030667723175333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54972360704327122380536885 5153658816030667723175333)
                  ·
                    refine ⟨966311028005750198095375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153658816030667723175333 966311028005750198095375)
                    ·
                      rfl

theorem cell23_5645652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_5645652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645652 prefixEnd_5645652 := by exact prefixLift 5645652
  have htrace : WordTrace (prefixWord ++ tailWord_5645652) baseStart_5645652 baseEnd_5645652 := by
    simpa [prefixWord, tailWord_5645652, baseEnd_5645652] using wordTrace_append hprefix tailTrace_5645652
  have hstable : (prefixWord ++ tailWord_5645652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645652).length < 2 ^ (prefixWord ++ tailWord_5645652).sum := by decide
  have hdescent : baseEnd_5645652 < baseStart_5645652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645669 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_5645669 : Nat := 118140960795 + 5645669 * 2 ^ 59
def prefixEnd_5645669 : Nat := 4983230072969 + 3 ^ 40 * 5645669 * 2
def baseEnd_5645669 : Nat := 966313937729459009257849

theorem tailTrace_5645669 : CollatzResearch.WordTrace tailWord_5645669 prefixEnd_5645669 966313937729459009257849 := by
  unfold tailWord_5645669
  simp only [CollatzResearch.WordTrace]
  refine ⟨205914464983712891346148061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137276309989141927564098707 205914464983712891346148061)
  ·
    refine ⟨77217924368892334254805523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205914464983712891346148061 77217924368892334254805523)
    ·
      refine ⟨115826886553338501382208285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77217924368892334254805523 115826886553338501382208285)
      ·
        refine ⟨43435082457501938018328107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115826886553338501382208285 43435082457501938018328107)
        ·
          refine ⟨65152623686252907027492161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43435082457501938018328107 65152623686252907027492161)
          ·
            refine ⟨48864467764689680270619121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65152623686252907027492161 48864467764689680270619121)
            ·
              refine ⟨36648350823517260202964341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48864467764689680270619121 36648350823517260202964341)
              ·
                refine ⟨3435782889704743144027907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36648350823517260202964341 3435782889704743144027907)
                ·
                  refine ⟨5153674334557114716041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435782889704743144027907 5153674334557114716041861)
                  ·
                    refine ⟨966313937729459009257849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153674334557114716041861 966313937729459009257849)
                    ·
                      rfl

theorem cell23_5645669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_5645669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645669 prefixEnd_5645669 := by exact prefixLift 5645669
  have htrace : WordTrace (prefixWord ++ tailWord_5645669) baseStart_5645669 baseEnd_5645669 := by
    simpa [prefixWord, tailWord_5645669, baseEnd_5645669] using wordTrace_append hprefix tailTrace_5645669
  have hstable : (prefixWord ++ tailWord_5645669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645669).length < 2 ^ (prefixWord ++ tailWord_5645669).sum := by decide
  have hdescent : baseEnd_5645669 < baseStart_5645669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645682 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_5645682 : Nat := 118140960795 + 5645682 * 2 ^ 59
def prefixEnd_5645682 : Nat := 4983230072969 + 3 ^ 40 * 5645682 * 2
def baseEnd_5645682 : Nat := 322105387604098386323443

theorem tailTrace_5645682 : CollatzResearch.WordTrace tailWord_5645682 prefixEnd_5645682 322105387604098386323443 := by
  unfold tailWord_5645682
  simp only [CollatzResearch.WordTrace]
  refine ⟨51478734783166448641592825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137276626088443863044247533 51478734783166448641592825)
  ·
    refine ⟨38609051087374836481194619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51478734783166448641592825 38609051087374836481194619)
    ·
      refine ⟨57913576631062254721791929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38609051087374836481194619 57913576631062254721791929)
      ·
        refine ⟨43435182473296691041343947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57913576631062254721791929 43435182473296691041343947)
        ·
          refine ⟨65152773709945036562015921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43435182473296691041343947 65152773709945036562015921)
          ·
            refine ⟨48864580282458777421511941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65152773709945036562015921 48864580282458777421511941)
            ·
              refine ⟨9162108802961020766533489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48864580282458777421511941 9162108802961020766533489)
              ·
                refine ⟨6871581602220765574900117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9162108802961020766533489 6871581602220765574900117)
                ·
                  refine ⟨322105387604098386323443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6871581602220765574900117 322105387604098386323443)
                  ·
                    rfl

theorem cell23_5645682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_5645682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645682 prefixEnd_5645682 := by exact prefixLift 5645682
  have htrace : WordTrace (prefixWord ++ tailWord_5645682) baseStart_5645682 baseEnd_5645682 := by
    simpa [prefixWord, tailWord_5645682, baseEnd_5645682] using wordTrace_append hprefix tailTrace_5645682
  have hstable : (prefixWord ++ tailWord_5645682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645682).length < 2 ^ (prefixWord ++ tailWord_5645682).sum := by decide
  have hdescent : baseEnd_5645682 < baseStart_5645682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645752 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_5645752 : Nat := 118140960795 + 5645752 * 2 ^ 59
def prefixEnd_5645752 : Nat := 4983230072969 + 3 ^ 40 * 5645752 * 2
def baseEnd_5645752 : Nat := 2898984432082700203035665

theorem tailTrace_5645752 : CollatzResearch.WordTrace tailWord_5645752 prefixEnd_5645752 2898984432082700203035665 := by
  unfold tailWord_5645752
  simp only [CollatzResearch.WordTrace]
  refine ⟨102958746121206098260709755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137278328161608131014279673 102958746121206098260709755)
  ·
    refine ⟨154438119181809147391064633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102958746121206098260709755 154438119181809147391064633)
    ·
      refine ⟨115828589386356860543298475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154438119181809147391064633 115828589386356860543298475)
      ·
        refine ⟨173742884079535290814947713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115828589386356860543298475 173742884079535290814947713)
        ·
          refine ⟨130307163059651468111210785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173742884079535290814947713 130307163059651468111210785)
          ·
            refine ⟨97730372294738601083408089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130307163059651468111210785 97730372294738601083408089)
            ·
              refine ⟨73297779221053950812556067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97730372294738601083408089 73297779221053950812556067)
              ·
                refine ⟨109946668831580926218834101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73297779221053950812556067 109946668831580926218834101)
                ·
                  refine ⟨10307500202960711833015697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109946668831580926218834101 10307500202960711833015697)
                  ·
                    refine ⟨7730625152220533874761773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10307500202960711833015697 7730625152220533874761773)
                    ·
                      refine ⟨2898984432082700203035665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730625152220533874761773 2898984432082700203035665)
                      ·
                        rfl

theorem cell23_5645752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_5645752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645752 prefixEnd_5645752 := by exact prefixLift 5645752
  have htrace : WordTrace (prefixWord ++ tailWord_5645752) baseStart_5645752 baseEnd_5645752 := by
    simpa [prefixWord, tailWord_5645752, baseEnd_5645752] using wordTrace_append hprefix tailTrace_5645752
  have hstable : (prefixWord ++ tailWord_5645752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645752).length < 2 ^ (prefixWord ++ tailWord_5645752).sum := by decide
  have hdescent : baseEnd_5645752 < baseStart_5645752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645772 : List Nat := [2, 2, 1, 4, 2, 2, 1, 9]
def baseStart_5645772 : Nat := 118140960795 + 5645772 * 2 ^ 59
def prefixEnd_5645772 : Nat := 4983230072969 + 3 ^ 40 * 5645772 * 2
def baseEnd_5645772 : Nat := 107370174136881115732799

theorem tailTrace_5645772 : CollatzResearch.WordTrace tailWord_5645772 prefixEnd_5645772 107370174136881115732799 := by
  unfold tailWord_5645772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102959110851169869968573785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137278814468226493291431713 102959110851169869968573785)
  ·
    refine ⟨77219333138377402476430339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102959110851169869968573785 77219333138377402476430339)
    ·
      refine ⟨115828999707566103714645509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77219333138377402476430339 115828999707566103714645509)
      ·
        refine ⟨21717937445168644446496033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115828999707566103714645509 21717937445168644446496033)
        ·
          refine ⟨16288453083876483334872025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21717937445168644446496033 16288453083876483334872025)
          ·
            refine ⟨12216339812907362501154019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16288453083876483334872025 12216339812907362501154019)
            ·
              refine ⟨18324509719361043751731029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216339812907362501154019 18324509719361043751731029)
              ·
                refine ⟨107370174136881115732799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18324509719361043751731029 107370174136881115732799)
                ·
                  rfl

theorem cell23_5645772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 9].length) (baseStart_5645772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645772 prefixEnd_5645772 := by exact prefixLift 5645772
  have htrace : WordTrace (prefixWord ++ tailWord_5645772) baseStart_5645772 baseEnd_5645772 := by
    simpa [prefixWord, tailWord_5645772, baseEnd_5645772] using wordTrace_append hprefix tailTrace_5645772
  have hstable : (prefixWord ++ tailWord_5645772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645772).length < 2 ^ (prefixWord ++ tailWord_5645772).sum := by decide
  have hdescent : baseEnd_5645772 < baseStart_5645772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645800 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5645800 : Nat := 118140960795 + 5645800 * 2 ^ 59
def prefixEnd_5645800 : Nat := 4983230072969 + 3 ^ 40 * 5645800 * 2
def baseEnd_5645800 : Nat := 2899009079154116015235445

theorem tailTrace_5645800 : CollatzResearch.WordTrace tailWord_5645800 prefixEnd_5645800 2899009079154116015235445 := by
  unfold tailWord_5645800
  simp only [CollatzResearch.WordTrace]
  refine ⟨102959621473119150359583427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137279495297492200479444569 102959621473119150359583427)
  ·
    refine ⟨154439432209678725539375141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102959621473119150359583427 154439432209678725539375141)
    ·
      refine ⟨28957393539314761038632839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154439432209678725539375141 28957393539314761038632839)
      ·
        refine ⟨43436090308972141557949259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28957393539314761038632839 43436090308972141557949259)
        ·
          refine ⟨65154135463458212336923889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43436090308972141557949259 65154135463458212336923889)
          ·
            refine ⟨48865601597593659252692917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65154135463458212336923889 48865601597593659252692917)
            ·
              refine ⟨4581150149774405554939961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48865601597593659252692917 4581150149774405554939961)
              ·
                refine ⟨3435862612330804166204971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4581150149774405554939961 3435862612330804166204971)
                ·
                  refine ⟨5153793918496206249307457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435862612330804166204971 5153793918496206249307457)
                  ·
                    refine ⟨3865345438872154686980593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5153793918496206249307457 3865345438872154686980593)
                    ·
                      refine ⟨2899009079154116015235445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865345438872154686980593 2899009079154116015235445)
                      ·
                        rfl

theorem cell23_5645800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5645800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645800 prefixEnd_5645800 := by exact prefixLift 5645800
  have htrace : WordTrace (prefixWord ++ tailWord_5645800) baseStart_5645800 baseEnd_5645800 := by
    simpa [prefixWord, tailWord_5645800, baseEnd_5645800] using wordTrace_append hprefix tailTrace_5645800
  have hstable : (prefixWord ++ tailWord_5645800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645800).length < 2 ^ (prefixWord ++ tailWord_5645800).sum := by decide
  have hdescent : baseEnd_5645800 < baseStart_5645800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645816 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_5645816 : Nat := 118140960795 + 5645816 * 2 ^ 59
def prefixEnd_5645816 : Nat := 4983230072969 + 3 ^ 40 * 5645816 * 2
def baseEnd_5645816 : Nat := 2899017294844587952635371

theorem tailTrace_5645816 : CollatzResearch.WordTrace tailWord_5645816 prefixEnd_5645816 2899017294844587952635371 := by
  unfold tailWord_5645816
  simp only [CollatzResearch.WordTrace]
  refine ⟨102959913257090167725874651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137279884342786890301166201 102959913257090167725874651)
  ·
    refine ⟨154439869885635251588811977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102959913257090167725874651 154439869885635251588811977)
    ·
      refine ⟨115829902414226438691608983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154439869885635251588811977 115829902414226438691608983)
      ·
        refine ⟨173744853621339658037413475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115829902414226438691608983 173744853621339658037413475)
        ·
          refine ⟨260617280432009487056120213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173744853621339658037413475 260617280432009487056120213)
          ·
            refine ⟨12216435020250444705755635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260617280432009487056120213 12216435020250444705755635)
            ·
              refine ⟨18324652530375667058633453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216435020250444705755635 18324652530375667058633453)
              ·
                refine ⟨6871744698890875146987545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18324652530375667058633453 6871744698890875146987545)
                ·
                  refine ⟨5153808524168156360240659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6871744698890875146987545 5153808524168156360240659)
                  ·
                    refine ⟨7730712786252234540360989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5153808524168156360240659 7730712786252234540360989)
                    ·
                      refine ⟨2899017294844587952635371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730712786252234540360989 2899017294844587952635371)
                      ·
                        rfl

theorem cell23_5645816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_5645816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645816 prefixEnd_5645816 := by exact prefixLift 5645816
  have htrace : WordTrace (prefixWord ++ tailWord_5645816) baseStart_5645816 baseEnd_5645816 := by
    simpa [prefixWord, tailWord_5645816, baseEnd_5645816] using wordTrace_append hprefix tailTrace_5645816
  have hstable : (prefixWord ++ tailWord_5645816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645816).length < 2 ^ (prefixWord ++ tailWord_5645816).sum := by decide
  have hdescent : baseEnd_5645816 < baseStart_5645816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645830 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5645830 : Nat := 118140960795 + 5645830 * 2 ^ 59
def prefixEnd_5645830 : Nat := 4983230072969 + 3 ^ 40 * 5645830 * 2
def baseEnd_5645830 : Nat := 2899024483573750897860307

theorem tailTrace_5645830 : CollatzResearch.WordTrace tailWord_5645830 prefixEnd_5645830 2899024483573750897860307 := by
  unfold tailWord_5645830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435010535504050495086217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137280224757419743895172629 6435010535504050495086217)
  ·
    refine ⟨4826257901628037871314663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6435010535504050495086217 4826257901628037871314663)
    ·
      refine ⟨7239386852442056806971995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826257901628037871314663 7239386852442056806971995)
      ·
        refine ⟨10859080278663085210457993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239386852442056806971995 10859080278663085210457993)
        ·
          refine ⟨8144310208997313907843495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859080278663085210457993 8144310208997313907843495)
          ·
            refine ⟨12216465313495970861765243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144310208997313907843495 12216465313495970861765243)
            ·
              refine ⟨18324697970243956292647865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216465313495970861765243 18324697970243956292647865)
              ·
                refine ⟨13743523477682967219485899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18324697970243956292647865 13743523477682967219485899)
                ·
                  refine ⟨20615285216524450829228849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13743523477682967219485899 20615285216524450829228849)
                  ·
                    refine ⟨15461463912393338121921637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20615285216524450829228849 15461463912393338121921637)
                    ·
                      refine ⟨2899024483573750897860307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15461463912393338121921637 2899024483573750897860307)
                      ·
                        rfl

theorem cell23_5645830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5645830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645830 prefixEnd_5645830 := by exact prefixLift 5645830
  have htrace : WordTrace (prefixWord ++ tailWord_5645830) baseStart_5645830 baseEnd_5645830 := by
    simpa [prefixWord, tailWord_5645830, baseEnd_5645830] using wordTrace_append hprefix tailTrace_5645830
  have hstable : (prefixWord ++ tailWord_5645830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645830).length < 2 ^ (prefixWord ++ tailWord_5645830).sum := by decide
  have hdescent : baseEnd_5645830 < baseStart_5645830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645837 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5645837 : Nat := 118140960795 + 5645837 * 2 ^ 59
def prefixEnd_5645837 : Nat := 4983230072969 + 3 ^ 40 * 5645837 * 2
def baseEnd_5645837 : Nat := 2899028077938332370472775

theorem tailTrace_5645837 : CollatzResearch.WordTrace tailWord_5645837 prefixEnd_5645837 2899028077938332370472775 := by
  unfold tailWord_5645837
  simp only [CollatzResearch.WordTrace]
  refine ⟨205920592447104256038263765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137280394964736170692175843 205920592447104256038263765)
  ·
    refine ⟨4826263885479006000896807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 205920592447104256038263765 4826263885479006000896807)
    ·
      refine ⟨7239395828218509001345211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826263885479006000896807 7239395828218509001345211)
      ·
        refine ⟨10859093742327763502017817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239395828218509001345211 10859093742327763502017817)
        ·
          refine ⟨8144320306745822626513363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859093742327763502017817 8144320306745822626513363)
          ·
            refine ⟨12216480460118733939770045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144320306745822626513363 12216480460118733939770045)
            ·
              refine ⟨4581180172544525227413767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12216480460118733939770045 4581180172544525227413767)
              ·
                refine ⟨6871770258816787841120651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581180172544525227413767 6871770258816787841120651)
                ·
                  refine ⟨10307655388225181761680977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6871770258816787841120651 10307655388225181761680977)
                  ·
                    refine ⟨7730741541168886321260733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10307655388225181761680977 7730741541168886321260733)
                    ·
                      refine ⟨2899028077938332370472775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730741541168886321260733 2899028077938332370472775)
                      ·
                        rfl

theorem cell23_5645837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5645837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645837 prefixEnd_5645837 := by exact prefixLift 5645837
  have htrace : WordTrace (prefixWord ++ tailWord_5645837) baseStart_5645837 baseEnd_5645837 := by
    simpa [prefixWord, tailWord_5645837, baseEnd_5645837] using wordTrace_append hprefix tailTrace_5645837
  have hstable : (prefixWord ++ tailWord_5645837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645837).length < 2 ^ (prefixWord ++ tailWord_5645837).sum := by decide
  have hdescent : baseEnd_5645837 < baseStart_5645837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645843 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 1, 3, 2]
def baseStart_5645843 : Nat := 118140960795 + 5645843 * 2 ^ 59
def prefixEnd_5645843 : Nat := 4983230072969 + 3 ^ 40 * 5645843 * 2
def baseEnd_5645843 : Nat := 2899031158822259346997747

theorem tailTrace_5645843 : CollatzResearch.WordTrace tailWord_5645843 prefixEnd_5645843 2899031158822259346997747 := by
  unfold tailWord_5645843
  simp only [CollatzResearch.WordTrace]
  refine ⟨205920811285082519062982183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137280540856721679375321455 205920811285082519062982183)
  ·
    refine ⟨308881216927623778594473275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205920811285082519062982183 308881216927623778594473275)
    ·
      refine ⟨463321825391435667891709913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308881216927623778594473275 463321825391435667891709913)
      ·
        refine ⟨347491369043576750918782435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463321825391435667891709913 347491369043576750918782435)
        ·
          refine ⟨521237053565365126378173653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347491369043576750918782435 521237053565365126378173653)
          ·
            refine ⟨12216493442938245149488445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 521237053565365126378173653 12216493442938245149488445)
            ·
              refine ⟨4581185041101841931058167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12216493442938245149488445 4581185041101841931058167)
              ·
                refine ⟨6871777561652762896587251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581185041101841931058167 6871777561652762896587251)
                ·
                  refine ⟨10307666342479144344880877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6871777561652762896587251 10307666342479144344880877)
                  ·
                    refine ⟨3865374878429679129330329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10307666342479144344880877 3865374878429679129330329)
                    ·
                      refine ⟨2899031158822259346997747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865374878429679129330329 2899031158822259346997747)
                      ·
                        rfl

theorem cell23_5645843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 3, 2].length) (baseStart_5645843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645843 prefixEnd_5645843 := by exact prefixLift 5645843
  have htrace : WordTrace (prefixWord ++ tailWord_5645843) baseStart_5645843 baseEnd_5645843 := by
    simpa [prefixWord, tailWord_5645843, baseEnd_5645843] using wordTrace_append hprefix tailTrace_5645843
  have hstable : (prefixWord ++ tailWord_5645843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645843).length < 2 ^ (prefixWord ++ tailWord_5645843).sum := by decide
  have hdescent : baseEnd_5645843 < baseStart_5645843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645889 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5645889 : Nat := 118140960795 + 5645889 * 2 ^ 59
def prefixEnd_5645889 : Nat := 4983230072969 + 3 ^ 40 * 5645889 * 2
def baseEnd_5645889 : Nat := 2899054778932366167022535

theorem tailTrace_5645889 : CollatzResearch.WordTrace tailWord_5645889 prefixEnd_5645889 2899054778932366167022535 := by
  unfold tailWord_5645889
  simp only [CollatzResearch.WordTrace]
  refine ⟨205922489042915868919156721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137281659361943912612771147 205922489042915868919156721)
  ·
    refine ⟨154441866782186901689367541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205922489042915868919156721 154441866782186901689367541)
    ·
      refine ⟨14478925010830022033378207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154441866782186901689367541 14478925010830022033378207)
      ·
        refine ⟨21718387516245033050067311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478925010830022033378207 21718387516245033050067311)
        ·
          refine ⟨32577581274367549575100967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21718387516245033050067311 32577581274367549575100967)
          ·
            refine ⟨48866371911551324362651451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32577581274367549575100967 48866371911551324362651451)
            ·
              refine ⟨73299557867326986543977177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48866371911551324362651451 73299557867326986543977177)
              ·
                refine ⟨54974668400495239907982883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73299557867326986543977177 54974668400495239907982883)
                ·
                  refine ⟨82462002600742859861974325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54974668400495239907982883 82462002600742859861974325)
                  ·
                    refine ⟨7730812743819643112060093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82462002600742859861974325 7730812743819643112060093)
                    ·
                      refine ⟨2899054778932366167022535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730812743819643112060093 2899054778932366167022535)
                      ·
                        rfl

theorem cell23_5645889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5645889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645889 prefixEnd_5645889 := by exact prefixLift 5645889
  have htrace : WordTrace (prefixWord ++ tailWord_5645889) baseStart_5645889 baseEnd_5645889 := by
    simpa [prefixWord, tailWord_5645889, baseEnd_5645889] using wordTrace_append hprefix tailTrace_5645889
  have hstable : (prefixWord ++ tailWord_5645889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645889).length < 2 ^ (prefixWord ++ tailWord_5645889).sum := by decide
  have hdescent : baseEnd_5645889 < baseStart_5645889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645894 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5645894 : Nat := 118140960795 + 5645894 * 2 ^ 59
def prefixEnd_5645894 : Nat := 4983230072969 + 3 ^ 40 * 5645894 * 2
def baseEnd_5645894 : Nat := 2899057346335638647460013

theorem tailTrace_5645894 : CollatzResearch.WordTrace tailWord_5645894 prefixEnd_5645894 2899057346335638647460013 := by
  unfold tailWord_5645894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435083481496804836659023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137281780938598503182059157 6435083481496804836659023)
  ·
    refine ⟨9652625222245207254988535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435083481496804836659023 9652625222245207254988535)
    ·
      refine ⟨14478937833367810882482803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9652625222245207254988535 14478937833367810882482803)
      ·
        refine ⟨21718406750051716323724205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478937833367810882482803 21718406750051716323724205)
        ·
          refine ⟨8144402531269393621396577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21718406750051716323724205 8144402531269393621396577)
          ·
            refine ⟨6108301898452045216047433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8144402531269393621396577 6108301898452045216047433)
            ·
              refine ⟨4581226423839033912035575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108301898452045216047433 4581226423839033912035575)
              ·
                refine ⟨6871839635758550868053363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581226423839033912035575 6871839635758550868053363)
                ·
                  refine ⟨10307759453637826302080045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6871839635758550868053363 10307759453637826302080045)
                  ·
                    refine ⟨3865409795114184863280017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10307759453637826302080045 3865409795114184863280017)
                    ·
                      refine ⟨2899057346335638647460013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865409795114184863280017 2899057346335638647460013)
                      ·
                        rfl

theorem cell23_5645894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5645894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645894 prefixEnd_5645894 := by exact prefixLift 5645894
  have htrace : WordTrace (prefixWord ++ tailWord_5645894) baseStart_5645894 baseEnd_5645894 := by
    simpa [prefixWord, tailWord_5645894, baseEnd_5645894] using wordTrace_append hprefix tailTrace_5645894
  have hstable : (prefixWord ++ tailWord_5645894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645894).length < 2 ^ (prefixWord ++ tailWord_5645894).sum := by decide
  have hdescent : baseEnd_5645894 < baseStart_5645894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645952 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 10]
def baseStart_5645952 : Nat := 118140960795 + 5645952 * 2 ^ 59
def prefixEnd_5645952 : Nat := 4983230072969 + 3 ^ 40 * 5645952 * 2
def baseEnd_5645952 : Nat := 322120792023733268948305

theorem tailTrace_5645952 : CollatzResearch.WordTrace tailWord_5645952 prefixEnd_5645952 322120792023733268948305 := by
  unfold tailWord_5645952
  simp only [CollatzResearch.WordTrace]
  refine ⟨102962393420843815339350055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137283191227791753785800073 102962393420843815339350055)
  ·
    refine ⟨154443590131265723009025083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102962393420843815339350055 154443590131265723009025083)
    ·
      refine ⟨231665385196898584513537625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154443590131265723009025083 231665385196898584513537625)
      ·
        refine ⟨173749038897673938385153219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231665385196898584513537625 173749038897673938385153219)
        ·
          refine ⟨260623558346510907577729829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173749038897673938385153219 260623558346510907577729829)
          ·
            refine ⟨48866917189970795170824343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260623558346510907577729829 48866917189970795170824343)
            ·
              refine ⟨73300375784956192756236515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48866917189970795170824343 73300375784956192756236515)
              ·
                refine ⟨109950563677434289134354773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73300375784956192756236515 109950563677434289134354773)
                ·
                  refine ⟨322120792023733268948305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 109950563677434289134354773 322120792023733268948305)
                  ·
                    rfl

theorem cell23_5645952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_5645952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645952 prefixEnd_5645952 := by exact prefixLift 5645952
  have htrace : WordTrace (prefixWord ++ tailWord_5645952) baseStart_5645952 baseEnd_5645952 := by
    simpa [prefixWord, tailWord_5645952, baseEnd_5645952] using wordTrace_append hprefix tailTrace_5645952
  have hstable : (prefixWord ++ tailWord_5645952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645952).length < 2 ^ (prefixWord ++ tailWord_5645952).sum := by decide
  have hdescent : baseEnd_5645952 < baseStart_5645952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645966 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_5645966 : Nat := 118140960795 + 5645966 * 2 ^ 59
def prefixEnd_5645966 : Nat := 4983230072969 + 3 ^ 40 * 5645966 * 2
def baseEnd_5645966 : Nat := 2899094316942762365759681

theorem tailTrace_5645966 : CollatzResearch.WordTrace tailWord_5645966 prefixEnd_5645966 2899094316942762365759681 := by
  unfold tailWord_5645966
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740662182954613883713719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137283531642424607379806501 25740662182954613883713719)
  ·
    refine ⟨38610993274431920825570579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25740662182954613883713719 38610993274431920825570579)
    ·
      refine ⟨57916489911647881238355869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38610993274431920825570579 57916489911647881238355869)
      ·
        refine ⟨21718683716867955464383451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57916489911647881238355869 21718683716867955464383451)
        ·
          refine ⟨32578025575301933196575177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21718683716867955464383451 32578025575301933196575177)
          ·
            refine ⟨24433519181476449897431383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32578025575301933196575177 24433519181476449897431383)
            ·
              refine ⟨36650278772214674846147075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24433519181476449897431383 36650278772214674846147075)
              ·
                refine ⟨54975418158322012269220613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36650278772214674846147075 54975418158322012269220613)
                ·
                  refine ⟨10307890904685377300478865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54975418158322012269220613 10307890904685377300478865)
                  ·
                    refine ⟨7730918178514032975359149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10307890904685377300478865 7730918178514032975359149)
                    ·
                      refine ⟨2899094316942762365759681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7730918178514032975359149 2899094316942762365759681)
                      ·
                        rfl

theorem cell23_5645966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_5645966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645966 prefixEnd_5645966 := by exact prefixLift 5645966
  have htrace : WordTrace (prefixWord ++ tailWord_5645966) baseStart_5645966 baseEnd_5645966 := by
    simpa [prefixWord, tailWord_5645966, baseEnd_5645966] using wordTrace_append hprefix tailTrace_5645966
  have hstable : (prefixWord ++ tailWord_5645966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645966).length < 2 ^ (prefixWord ++ tailWord_5645966).sum := by decide
  have hdescent : baseEnd_5645966 < baseStart_5645966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5645999 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 3, 5]
def baseStart_5645999 : Nat := 118140960795 + 5645999 * 2 ^ 59
def prefixEnd_5645999 : Nat := 4983230072969 + 3 ^ 40 * 5645999 * 2
def baseEnd_5645999 : Nat := 966370420601453578882343

theorem tailTrace_5645999 : CollatzResearch.WordTrace tailWord_5645999 prefixEnd_5645999 966370420601453578882343 := by
  unfold tailWord_5645999
  simp only [CollatzResearch.WordTrace]
  refine ⟨205926501072517357705661051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137284334048344905137107367 205926501072517357705661051)
  ·
    refine ⟨308889751608776036558491577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205926501072517357705661051 308889751608776036558491577)
    ·
      refine ⟨231667313706582027418868683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308889751608776036558491577 231667313706582027418868683)
      ·
        refine ⟨347500970559873041128303025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231667313706582027418868683 347500970559873041128303025)
        ·
          refine ⟨260625727919904780846227269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347500970559873041128303025 260625727919904780846227269)
          ·
            refine ⟨48867323984982146408667613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260625727919904780846227269 48867323984982146408667613)
            ·
              refine ⟨18325246494368304903250355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48867323984982146408667613 18325246494368304903250355)
              ·
                refine ⟨27487869741552457354875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18325246494368304903250355 27487869741552457354875533)
                ·
                  refine ⟨10307951153082171508078325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27487869741552457354875533 10307951153082171508078325)
                  ·
                    refine ⟨966370420601453578882343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10307951153082171508078325 966370420601453578882343)
                    ·
                      rfl

theorem cell23_5645999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_5645999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5645999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5645999 prefixEnd_5645999 := by exact prefixLift 5645999
  have htrace : WordTrace (prefixWord ++ tailWord_5645999) baseStart_5645999 baseEnd_5645999 := by
    simpa [prefixWord, tailWord_5645999, baseEnd_5645999] using wordTrace_append hprefix tailTrace_5645999
  have hstable : (prefixWord ++ tailWord_5645999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5645999).length < 2 ^ (prefixWord ++ tailWord_5645999).sum := by decide
  have hdescent : baseEnd_5645999 < baseStart_5645999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5645999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646030 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_5646030 : Nat := 118140960795 + 5646030 * 2 ^ 59
def prefixEnd_5646030 : Nat := 4983230072969 + 3 ^ 40 * 5646030 * 2
def baseEnd_5646030 : Nat := 2899127179704650115359387

theorem tailTrace_5646030 : CollatzResearch.WordTrace tailWord_5646030 prefixEnd_5646030 2899127179704650115359387 := by
  unfold tailWord_5646030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740953966925631250004943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137285087823603366666693029 25740953966925631250004943)
  ·
    refine ⟨38611430950388446875007415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25740953966925631250004943 38611430950388446875007415)
    ·
      refine ⟨57917146425582670312511123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38611430950388446875007415 57917146425582670312511123)
      ·
        refine ⟨86875719638374005468766685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57917146425582670312511123 86875719638374005468766685)
        ·
          refine ⟨32578394864390252050787507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86875719638374005468766685 32578394864390252050787507)
          ·
            refine ⟨48867592296585378076181261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32578394864390252050787507 48867592296585378076181261)
            ·
              refine ⟨18325347111219516778567973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48867592296585378076181261 18325347111219516778567973)
              ·
                refine ⟨3436002583353659395981495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18325347111219516778567973 3436002583353659395981495)
                ·
                  refine ⟨5154003875030489093972243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436002583353659395981495 5154003875030489093972243)
                  ·
                    refine ⟨7731005812545733640958365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154003875030489093972243 7731005812545733640958365)
                    ·
                      refine ⟨2899127179704650115359387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7731005812545733640958365 2899127179704650115359387)
                      ·
                        rfl

theorem cell23_5646030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_5646030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646030 prefixEnd_5646030 := by exact prefixLift 5646030
  have htrace : WordTrace (prefixWord ++ tailWord_5646030) baseStart_5646030 baseEnd_5646030 := by
    simpa [prefixWord, tailWord_5646030, baseEnd_5646030] using wordTrace_append hprefix tailTrace_5646030
  have hstable : (prefixWord ++ tailWord_5646030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646030).length < 2 ^ (prefixWord ++ tailWord_5646030).sum := by decide
  have hdescent : baseEnd_5646030 < baseStart_5646030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646039 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_5646039 : Nat := 118140960795 + 5646039 * 2 ^ 59
def prefixEnd_5646039 : Nat := 4983230072969 + 3 ^ 40 * 5646039 * 2
def baseEnd_5646039 : Nat := 2899131801030540580146845

theorem tailTrace_5646039 : CollatzResearch.WordTrace tailWord_5646039 prefixEnd_5646039 2899131801030540580146845 := by
  unfold tailWord_5646039
  simp only [CollatzResearch.WordTrace]
  refine ⟨205927959992372444537117171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137285306661581629691411447 205927959992372444537117171)
  ·
    refine ⟨308891939988558666805675757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205927959992372444537117171 308891939988558666805675757)
    ·
      refine ⟨115834477495709500052128409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308891939988558666805675757 115834477495709500052128409)
      ·
        refine ⟨86875858121782125039096307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115834477495709500052128409 86875858121782125039096307)
        ·
          refine ⟨130313787182673187558644461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86875858121782125039096307 130313787182673187558644461)
          ·
            refine ⟨48867670193502445334491673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130313787182673187558644461 48867670193502445334491673)
            ·
              refine ⟨36650752645126834000868755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48867670193502445334491673 36650752645126834000868755)
              ·
                refine ⟨54976128967690251001303133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36650752645126834000868755 54976128967690251001303133)
                ·
                  refine ⟨20616048362883844125488675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54976128967690251001303133 20616048362883844125488675)
                  ·
                    refine ⟨30924072544325766188233013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20616048362883844125488675 30924072544325766188233013)
                    ·
                      refine ⟨2899131801030540580146845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30924072544325766188233013 2899131801030540580146845)
                      ·
                        rfl

theorem cell23_5646039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_5646039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646039 prefixEnd_5646039 := by exact prefixLift 5646039
  have htrace : WordTrace (prefixWord ++ tailWord_5646039) baseStart_5646039 baseEnd_5646039 := by
    simpa [prefixWord, tailWord_5646039, baseEnd_5646039] using wordTrace_append hprefix tailTrace_5646039
  have hstable : (prefixWord ++ tailWord_5646039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646039).length < 2 ^ (prefixWord ++ tailWord_5646039).sum := by decide
  have hdescent : baseEnd_5646039 < baseStart_5646039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646066 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5646066 : Nat := 118140960795 + 5646066 * 2 ^ 59
def prefixEnd_5646066 : Nat := 4983230072969 + 3 ^ 40 * 5646066 * 2
def baseEnd_5646066 : Nat := 2899145665008211974509221

theorem tailTrace_5646066 : CollatzResearch.WordTrace tailWord_5646066 prefixEnd_5646066 2899145665008211974509221 := by
  unfold tailWord_5646066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51482236190818657037087513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137285963175516418765566701 51482236190818657037087513)
  ·
    refine ⟨38611677143113992777815635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51482236190818657037087513 38611677143113992777815635)
    ·
      refine ⟨57917515714670989166723453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38611677143113992777815635 57917515714670989166723453)
      ·
        refine ⟨21719068393001620937521295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57917515714670989166723453 21719068393001620937521295)
        ·
          refine ⟨32578602589502431406281943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21719068393001620937521295 32578602589502431406281943)
          ·
            refine ⟨48867903884253647109422915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32578602589502431406281943 48867903884253647109422915)
            ·
              refine ⟨73301855826380470664134373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48867903884253647109422915 73301855826380470664134373)
              ·
                refine ⟨13744097967446338249525195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73301855826380470664134373 13744097967446338249525195)
                ·
                  refine ⟨20616146951169507374287793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13744097967446338249525195 20616146951169507374287793)
                  ·
                    refine ⟨15462110213377130530715845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20616146951169507374287793 15462110213377130530715845)
                    ·
                      refine ⟨2899145665008211974509221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15462110213377130530715845 2899145665008211974509221)
                      ·
                        rfl

theorem cell23_5646066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5646066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646066 prefixEnd_5646066 := by exact prefixLift 5646066
  have htrace : WordTrace (prefixWord ++ tailWord_5646066) baseStart_5646066 baseEnd_5646066 := by
    simpa [prefixWord, tailWord_5646066, baseEnd_5646066] using wordTrace_append hprefix tailTrace_5646066
  have hstable : (prefixWord ++ tailWord_5646066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646066).length < 2 ^ (prefixWord ++ tailWord_5646066).sum := by decide
  have hdescent : baseEnd_5646066 < baseStart_5646066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646070 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5646070 : Nat := 118140960795 + 5646070 * 2 ^ 59
def prefixEnd_5646070 : Nat := 4983230072969 + 3 ^ 40 * 5646070 * 2
def baseEnd_5646070 : Nat := 2899147718930829958859203

theorem tailTrace_5646070 : CollatzResearch.WordTrace tailWord_5646070 prefixEnd_5646070 2899147718930829958859203 := by
  unfold tailWord_5646070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870568165953758551968479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137286060436840091220997109 12870568165953758551968479)
  ·
    refine ⟨19305852248930637827952719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12870568165953758551968479 19305852248930637827952719)
    ·
      refine ⟨28958778373395956741929079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19305852248930637827952719 28958778373395956741929079)
      ·
        refine ⟨43438167560093935112893619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28958778373395956741929079 43438167560093935112893619)
        ·
          refine ⟨65157251340140902669340429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43438167560093935112893619 65157251340140902669340429)
          ·
            refine ⟨24433969252552838501002661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65157251340140902669340429 24433969252552838501002661)
            ·
              refine ⟨4581369234853657218937999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24433969252552838501002661 4581369234853657218937999)
              ·
                refine ⟨6872053852280485828406999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581369234853657218937999 6872053852280485828406999)
                ·
                  refine ⟨10308080778420728742610499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6872053852280485828406999 10308080778420728742610499)
                  ·
                    refine ⟨15462121167631093113915749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10308080778420728742610499 15462121167631093113915749)
                    ·
                      refine ⟨2899147718930829958859203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15462121167631093113915749 2899147718930829958859203)
                      ·
                        rfl

theorem cell23_5646070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5646070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646070 prefixEnd_5646070 := by exact prefixLift 5646070
  have htrace : WordTrace (prefixWord ++ tailWord_5646070) baseStart_5646070 baseEnd_5646070 := by
    simpa [prefixWord, tailWord_5646070, baseEnd_5646070] using wordTrace_append hprefix tailTrace_5646070
  have hstable : (prefixWord ++ tailWord_5646070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646070).length < 2 ^ (prefixWord ++ tailWord_5646070).sum := by decide
  have hdescent : baseEnd_5646070 < baseStart_5646070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646087 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5646087 : Nat := 118140960795 + 5646087 * 2 ^ 59
def prefixEnd_5646087 : Nat := 4983230072969 + 3 ^ 40 * 5646087 * 2
def baseEnd_5646087 : Nat := 2899156448101956392346625

theorem tailTrace_5646087 : CollatzResearch.WordTrace tailWord_5646087 prefixEnd_5646087 2899156448101956392346625 := by
  unfold tailWord_5646087
  simp only [CollatzResearch.WordTrace]
  refine ⟨205929710696198548734864515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137286473797465699156576343 205929710696198548734864515)
  ·
    refine ⟨308894566044297823102296773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205929710696198548734864515 308894566044297823102296773)
    ·
      refine ⟨57917731133305841831680645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308894566044297823102296773 57917731133305841831680645)
      ·
        refine ⟨10859574587494845343440121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57917731133305841831680645 10859574587494845343440121)
        ·
          refine ⟨8144680940621134007580091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859574587494845343440121 8144680940621134007580091)
          ·
            refine ⟨12217021410931701011370137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144680940621134007580091 12217021410931701011370137)
            ·
              refine ⟨9162766058198775758527603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12217021410931701011370137 9162766058198775758527603)
              ·
                refine ⟨13744149087298163637791405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9162766058198775758527603 13744149087298163637791405)
                ·
                  refine ⟨5154055907736811364171777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13744149087298163637791405 5154055907736811364171777)
                  ·
                    refine ⟨3865541930802608523128833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5154055907736811364171777 3865541930802608523128833)
                    ·
                      refine ⟨2899156448101956392346625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865541930802608523128833 2899156448101956392346625)
                      ·
                        rfl

theorem cell23_5646087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5646087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646087 prefixEnd_5646087 := by exact prefixLift 5646087
  have htrace : WordTrace (prefixWord ++ tailWord_5646087) baseStart_5646087 baseEnd_5646087 := by
    simpa [prefixWord, tailWord_5646087, baseEnd_5646087] using wordTrace_append hprefix tailTrace_5646087
  have hstable : (prefixWord ++ tailWord_5646087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646087).length < 2 ^ (prefixWord ++ tailWord_5646087).sum := by decide
  have hdescent : baseEnd_5646087 < baseStart_5646087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646103 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_5646103 : Nat := 118140960795 + 5646103 * 2 ^ 59
def prefixEnd_5646103 : Nat := 4983230072969 + 3 ^ 40 * 5646103 * 2
def baseEnd_5646103 : Nat := 2899164663792428329746551

theorem tailTrace_5646103 : CollatzResearch.WordTrace tailWord_5646103 prefixEnd_5646103 2899164663792428329746551 := by
  unfold tailWord_5646103
  simp only [CollatzResearch.WordTrace]
  refine ⟨205930294264140583467446963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137286862842760388978297975 205930294264140583467446963)
  ·
    refine ⟨308895441396210875201170445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205930294264140583467446963 308895441396210875201170445)
    ·
      refine ⟨115835790523579078200438917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308895441396210875201170445 115835790523579078200438917)
      ·
        refine ⟨21719210723171077162582297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115835790523579078200438917 21719210723171077162582297)
        ·
          refine ⟨16289408042378307871936723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21719210723171077162582297 16289408042378307871936723)
          ·
            refine ⟨24434112063567461807905085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16289408042378307871936723 24434112063567461807905085)
            ·
              refine ⟨9162792023837798177964407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24434112063567461807905085 9162792023837798177964407)
              ·
                refine ⟨13744188035756697266946611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9162792023837798177964407 13744188035756697266946611)
                ·
                  refine ⟨20616282053635045900419917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13744188035756697266946611 20616282053635045900419917)
                  ·
                    refine ⟨7731105770113142212657469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20616282053635045900419917 7731105770113142212657469)
                    ·
                      refine ⟨2899164663792428329746551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7731105770113142212657469 2899164663792428329746551)
                      ·
                        rfl

theorem cell23_5646103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_5646103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646103 prefixEnd_5646103 := by exact prefixLift 5646103
  have htrace : WordTrace (prefixWord ++ tailWord_5646103) baseStart_5646103 baseEnd_5646103 := by
    simpa [prefixWord, tailWord_5646103, baseEnd_5646103] using wordTrace_append hprefix tailTrace_5646103
  have hstable : (prefixWord ++ tailWord_5646103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646103).length < 2 ^ (prefixWord ++ tailWord_5646103).sum := by decide
  have hdescent : baseEnd_5646103 < baseStart_5646103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646110 : List Nat := [4, 3, 2, 2, 1, 1, 1, 9]
def baseStart_5646110 : Nat := 118140960795 + 5646110 * 2 ^ 59
def prefixEnd_5646110 : Nat := 4983230072969 + 3 ^ 40 * 5646110 * 2
def baseEnd_5646110 : Nat := 107376602153963326013297

theorem tailTrace_5646110 : CollatzResearch.WordTrace tailWord_5646110 prefixEnd_5646110 107376602153963326013297 := by
  unfold tailWord_5646110
  simp only [CollatzResearch.WordTrace]
  refine ⟨25741318696889402957868973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137287033050076815775301189 25741318696889402957868973)
  ·
    refine ⟨9652994511333526109200865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25741318696889402957868973 9652994511333526109200865)
    ·
      refine ⟨7239745883500144581900649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652994511333526109200865 7239745883500144581900649)
      ·
        refine ⟨5429809412625108436425487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239745883500144581900649 5429809412625108436425487)
        ·
          refine ⟨8144714118937662654638231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429809412625108436425487 8144714118937662654638231)
          ·
            refine ⟨12217071178406493981957347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144714118937662654638231 12217071178406493981957347)
            ·
              refine ⟨18325606767609740972936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12217071178406493981957347 18325606767609740972936021)
              ·
                refine ⟨107376602153963326013297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18325606767609740972936021 107376602153963326013297)
                ·
                  rfl

theorem cell23_5646110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_5646110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646110 prefixEnd_5646110 := by exact prefixLift 5646110
  have htrace : WordTrace (prefixWord ++ tailWord_5646110) baseStart_5646110 baseEnd_5646110 := by
    simpa [prefixWord, tailWord_5646110, baseEnd_5646110] using wordTrace_append hprefix tailTrace_5646110
  have hstable : (prefixWord ++ tailWord_5646110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646110).length < 2 ^ (prefixWord ++ tailWord_5646110).sum := by decide
  have hdescent : baseEnd_5646110 < baseStart_5646110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646116 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_5646116 : Nat := 118140960795 + 5646116 * 2 ^ 59
def prefixEnd_5646116 : Nat := 4983230072969 + 3 ^ 40 * 5646116 * 2
def baseEnd_5646116 : Nat := 2899171339040936778883991

theorem tailTrace_5646116 : CollatzResearch.WordTrace tailWord_5646116 prefixEnd_5646116 2899171339040936778883991 := by
  unfold tailWord_5646116
  simp only [CollatzResearch.WordTrace]
  refine ⟨102965384206546743343835101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137287178942062324458446801 102965384206546743343835101)
  ·
    refine ⟨38612019077455028753938163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102965384206546743343835101 38612019077455028753938163)
    ·
      refine ⟨57918028616182543130907245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38612019077455028753938163 57918028616182543130907245)
      ·
        refine ⟨21719260731068453674090217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57918028616182543130907245 21719260731068453674090217)
        ·
          refine ⟨16289445548301340255567663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21719260731068453674090217 16289445548301340255567663)
          ·
            refine ⟨24434168322452010383351495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16289445548301340255567663 24434168322452010383351495)
            ·
              refine ⟨36651252483678015575027243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24434168322452010383351495 36651252483678015575027243)
              ·
                refine ⟨54976878725517023362540865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36651252483678015575027243 54976878725517023362540865)
                ·
                  refine ⟨41232659044137767521905649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54976878725517023362540865 41232659044137767521905649)
                  ·
                    refine ⟨30924494283103325641429237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41232659044137767521905649 30924494283103325641429237)
                    ·
                      refine ⟨2899171339040936778883991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30924494283103325641429237 2899171339040936778883991)
                      ·
                        rfl

theorem cell23_5646116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_5646116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646116 prefixEnd_5646116 := by exact prefixLift 5646116
  have htrace : WordTrace (prefixWord ++ tailWord_5646116) baseStart_5646116 baseEnd_5646116 := by
    simpa [prefixWord, tailWord_5646116, baseEnd_5646116] using wordTrace_append hprefix tailTrace_5646116
  have hstable : (prefixWord ++ tailWord_5646116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646116).length < 2 ^ (prefixWord ++ tailWord_5646116).sum := by decide
  have hdescent : baseEnd_5646116 < baseStart_5646116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646130 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_5646130 : Nat := 118140960795 + 5646130 * 2 ^ 59
def prefixEnd_5646130 : Nat := 4983230072969 + 3 ^ 40 * 5646130 * 2
def baseEnd_5646130 : Nat := 2899178527770099724108927

theorem tailTrace_5646130 : CollatzResearch.WordTrace tailWord_5646130 prefixEnd_5646130 2899178527770099724108927 := by
  unfold tailWord_5646130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51482819758760691769669961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137287519356695178052453229 51482819758760691769669961)
  ·
    refine ⟨38612114819070518827252471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51482819758760691769669961 38612114819070518827252471)
    ·
      refine ⟨57918172228605778240878707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38612114819070518827252471 57918172228605778240878707)
      ·
        refine ⟨86877258342908667361318061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57918172228605778240878707 86877258342908667361318061)
        ·
          refine ⟨32578971878590750260494273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86877258342908667361318061 32578971878590750260494273)
          ·
            refine ⟨24434228908943062695370705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32578971878590750260494273 24434228908943062695370705)
            ·
              refine ⟨18325671681707297021528029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24434228908943062695370705 18325671681707297021528029)
              ·
                refine ⟨6872126880640236383073011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18325671681707297021528029 6872126880640236383073011)
                ·
                  refine ⟨10308190320960354574609517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6872126880640236383073011 10308190320960354574609517)
                  ·
                    refine ⟨3865571370360132965478569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10308190320960354574609517 3865571370360132965478569)
                    ·
                      refine ⟨2899178527770099724108927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865571370360132965478569 2899178527770099724108927)
                      ·
                        rfl

theorem cell23_5646130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_5646130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646130 prefixEnd_5646130 := by exact prefixLift 5646130
  have htrace : WordTrace (prefixWord ++ tailWord_5646130) baseStart_5646130 baseEnd_5646130 := by
    simpa [prefixWord, tailWord_5646130, baseEnd_5646130] using wordTrace_append hprefix tailTrace_5646130
  have hstable : (prefixWord ++ tailWord_5646130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646130).length < 2 ^ (prefixWord ++ tailWord_5646130).sum := by decide
  have hdescent : baseEnd_5646130 < baseStart_5646130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646183 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 5]
def baseStart_5646183 : Nat := 118140960795 + 5646183 * 2 ^ 59
def prefixEnd_5646183 : Nat := 4983230072969 + 3 ^ 40 * 5646183 * 2
def baseEnd_5646183 : Nat := 322133971360532001860687

theorem tailTrace_5646183 : CollatzResearch.WordTrace tailWord_5646183 prefixEnd_5646183 322133971360532001860687 := by
  unfold tailWord_5646183
  simp only [CollatzResearch.WordTrace]
  refine ⟨205933212103850757130359203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137288808069233838086906135 205933212103850757130359203)
  ·
    refine ⟨308899818155776135695538805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205933212103850757130359203 308899818155776135695538805)
    ·
      refine ⟨28959357952104012721456763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 308899818155776135695538805 28959357952104012721456763)
      ·
        refine ⟨43439036928156019082185145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28959357952104012721456763 43439036928156019082185145)
        ·
          refine ⟨32579277696117014311638859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43439036928156019082185145 32579277696117014311638859)
          ·
            refine ⟨48868916544175521467458289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32579277696117014311638859 48868916544175521467458289)
            ·
              refine ⟨36651687408131641100593717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48868916544175521467458289 36651687408131641100593717)
              ·
                refine ⟨3436095694512341353180661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36651687408131641100593717 3436095694512341353180661)
                ·
                  refine ⟨322133971360532001860687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3436095694512341353180661 322133971360532001860687)
                  ·
                    rfl

theorem cell23_5646183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 5].length) (baseStart_5646183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646183 prefixEnd_5646183 := by exact prefixLift 5646183
  have htrace : WordTrace (prefixWord ++ tailWord_5646183) baseStart_5646183 baseEnd_5646183 := by
    simpa [prefixWord, tailWord_5646183, baseEnd_5646183] using wordTrace_append hprefix tailTrace_5646183
  have hstable : (prefixWord ++ tailWord_5646183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646183).length < 2 ^ (prefixWord ++ tailWord_5646183).sum := by decide
  have hdescent : baseEnd_5646183 < baseStart_5646183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646233 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 4]
def baseStart_5646233 : Nat := 118140960795 + 5646233 * 2 ^ 59
def prefixEnd_5646233 : Nat := 4983230072969 + 3 ^ 40 * 5646233 * 2
def baseEnd_5646233 : Nat := 2899231416277512821120953

theorem tailTrace_5646233 : CollatzResearch.WordTrace tailWord_5646233 prefixEnd_5646233 2899231416277512821120953 := by
  unfold tailWord_5646233
  simp only [CollatzResearch.WordTrace]
  refine ⟨205935035753669615669679353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137290023835779743779786235 205935035753669615669679353)
  ·
    refine ⟨154451276815252211752259515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205935035753669615669679353 154451276815252211752259515)
    ·
      refine ⟨231676915222878317628389273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154451276815252211752259515 231676915222878317628389273)
      ·
        refine ⟨173757686417158738221291955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231676915222878317628389273 173757686417158738221291955)
        ·
          refine ⟨260636529625738107331937933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173757686417158738221291955 260636529625738107331937933)
          ·
            refine ⟨97738698609651790249476725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260636529625738107331937933 97738698609651790249476725)
            ·
              refine ⟨9163002994654855335888443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97738698609651790249476725 9163002994654855335888443)
              ·
                refine ⟨13744504491982283003832665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163002994654855335888443 13744504491982283003832665)
                ·
                  refine ⟨10308378368986712252874499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13744504491982283003832665 10308378368986712252874499)
                  ·
                    refine ⟨15462567553480068379311749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10308378368986712252874499 15462567553480068379311749)
                    ·
                      refine ⟨2899231416277512821120953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15462567553480068379311749 2899231416277512821120953)
                      ·
                        rfl

theorem cell23_5646233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_5646233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646233 prefixEnd_5646233 := by exact prefixLift 5646233
  have htrace : WordTrace (prefixWord ++ tailWord_5646233) baseStart_5646233 baseEnd_5646233 := by
    simpa [prefixWord, tailWord_5646233, baseEnd_5646233] using wordTrace_append hprefix tailTrace_5646233
  have hstable : (prefixWord ++ tailWord_5646233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646233).length < 2 ^ (prefixWord ++ tailWord_5646233).sum := by decide
  have hdescent : baseEnd_5646233 < baseStart_5646233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646423 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 6]
def baseStart_5646423 : Nat := 118140960795 + 5646423 * 2 ^ 59
def prefixEnd_5646423 : Nat := 4983230072969 + 3 ^ 40 * 5646423 * 2
def baseEnd_5646423 : Nat := 966442992533955692581693

theorem tailTrace_5646423 : CollatzResearch.WordTrace tailWord_5646423 prefixEnd_5646423 966442992533955692581693 := by
  unfold tailWord_5646423
  simp only [CollatzResearch.WordTrace]
  refine ⟨205941965622981278119095923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137294643748654185412730615 205941965622981278119095923)
  ·
    refine ⟨308912948434471917178643885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205941965622981278119095923 308912948434471917178643885)
    ·
      refine ⟨115842355662926968941991457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308912948434471917178643885 115842355662926968941991457)
      ·
        refine ⟨86881766747195226706493593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115842355662926968941991457 86881766747195226706493593)
        ·
          refine ⟨65161325060396420029870195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86881766747195226706493593 65161325060396420029870195)
          ·
            refine ⟨97741987590594630044805293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65161325060396420029870195 97741987590594630044805293)
            ·
              refine ⟨36653245346472986266801985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97741987590594630044805293 36653245346472986266801985)
              ·
                refine ⟨27489934009854739700101489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36653245346472986266801985 27489934009854739700101489)
                ·
                  refine ⟨20617450507391054775076117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27489934009854739700101489 20617450507391054775076117)
                  ·
                    refine ⟨966442992533955692581693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20617450507391054775076117 966442992533955692581693)
                    ·
                      rfl

theorem cell23_5646423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_5646423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646423 prefixEnd_5646423 := by exact prefixLift 5646423
  have htrace : WordTrace (prefixWord ++ tailWord_5646423) baseStart_5646423 baseEnd_5646423 := by
    simpa [prefixWord, tailWord_5646423, baseEnd_5646423] using wordTrace_append hprefix tailTrace_5646423
  have hstable : (prefixWord ++ tailWord_5646423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646423).length < 2 ^ (prefixWord ++ tailWord_5646423).sum := by decide
  have hdescent : baseEnd_5646423 < baseStart_5646423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646424 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_5646424 : Nat := 118140960795 + 5646424 * 2 ^ 59
def prefixEnd_5646424 : Nat := 4983230072969 + 3 ^ 40 * 5646424 * 2
def baseEnd_5646424 : Nat := 2899329491082521573832575

theorem tailTrace_5646424 : CollatzResearch.WordTrace tailWord_5646424 prefixEnd_5646424 2899329491082521573832575 := by
  unfold tailWord_5646424
  simp only [CollatzResearch.WordTrace]
  refine ⟨102971001047988827644941163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137294668063985103526588217 102971001047988827644941163)
  ·
    refine ⟨154456501571983241467411745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102971001047988827644941163 154456501571983241467411745)
    ·
      refine ⟨115842376178987431100558809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154456501571983241467411745 115842376178987431100558809)
      ·
        refine ⟨86881782134240573325419107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115842376178987431100558809 86881782134240573325419107)
        ·
          refine ⟨130322673201360859988128661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86881782134240573325419107 130322673201360859988128661)
          ·
            refine ⟨6108875306313790311943531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130322673201360859988128661 6108875306313790311943531)
            ·
              refine ⟨9163312959470685467915297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108875306313790311943531 9163312959470685467915297)
              ·
                refine ⟨6872484719603014100936473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9163312959470685467915297 6872484719603014100936473)
                ·
                  refine ⟨5154363539702260575702355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6872484719603014100936473 5154363539702260575702355)
                  ·
                    refine ⟨7731545309553390863553533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154363539702260575702355 7731545309553390863553533)
                    ·
                      refine ⟨2899329491082521573832575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7731545309553390863553533 2899329491082521573832575)
                      ·
                        rfl

theorem cell23_5646424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_5646424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646424 prefixEnd_5646424 := by exact prefixLift 5646424
  have htrace : WordTrace (prefixWord ++ tailWord_5646424) baseStart_5646424 baseEnd_5646424 := by
    simpa [prefixWord, tailWord_5646424, baseEnd_5646424] using wordTrace_append hprefix tailTrace_5646424
  have hstable : (prefixWord ++ tailWord_5646424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646424).length < 2 ^ (prefixWord ++ tailWord_5646424).sum := by decide
  have hdescent : baseEnd_5646424 < baseStart_5646424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5646433 : Nat := 118140960795 + 5646433 * 2 ^ 59
def prefixEnd_5646433 : Nat := 4983230072969 + 3 ^ 40 * 5646433 * 2
def baseEnd_5646433 : Nat := 2899334112408412038620033

theorem tailTrace_5646433 : CollatzResearch.WordTrace tailWord_5646433 prefixEnd_5646433 2899334112408412038620033 := by
  unfold tailWord_5646433
  simp only [CollatzResearch.WordTrace]
  refine ⟨205942330352945049826959953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137294886901963366551306635 205942330352945049826959953)
  ·
    refine ⟨154456747764708787370219965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205942330352945049826959953 154456747764708787370219965)
    ·
      refine ⟨57921280411765795263832487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154456747764708787370219965 57921280411765795263832487)
      ·
        refine ⟨86881920617648692895748731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57921280411765795263832487 86881920617648692895748731)
        ·
          refine ⟨130322880926473039343623097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86881920617648692895748731 130322880926473039343623097)
          ·
            refine ⟨97742160694854779507717323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130322880926473039343623097 97742160694854779507717323)
            ·
              refine ⟨146613241042282169261575985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97742160694854779507717323 146613241042282169261575985)
              ·
                refine ⟨109959930781711626946181989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146613241042282169261575985 109959930781711626946181989)
                ·
                  refine ⟨20617487021570930052409123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109959930781711626946181989 20617487021570930052409123)
                  ·
                    refine ⟨30926230532356395078613685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20617487021570930052409123 30926230532356395078613685)
                    ·
                      refine ⟨2899334112408412038620033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30926230532356395078613685 2899334112408412038620033)
                      ·
                        rfl

theorem cell23_5646433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5646433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646433 prefixEnd_5646433 := by exact prefixLift 5646433
  have htrace : WordTrace (prefixWord ++ tailWord_5646433) baseStart_5646433 baseEnd_5646433 := by
    simpa [prefixWord, tailWord_5646433, baseEnd_5646433] using wordTrace_append hprefix tailTrace_5646433
  have hstable : (prefixWord ++ tailWord_5646433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646433).length < 2 ^ (prefixWord ++ tailWord_5646433).sum := by decide
  have hdescent : baseEnd_5646433 < baseStart_5646433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646447 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 4, 2]
def baseStart_5646447 : Nat := 118140960795 + 5646447 * 2 ^ 59
def prefixEnd_5646447 : Nat := 4983230072969 + 3 ^ 40 * 5646447 * 2
def baseEnd_5646447 : Nat := 2899341301137574983844969

theorem tailTrace_5646447 : CollatzResearch.WordTrace tailWord_5646447 prefixEnd_5646447 2899341301137574983844969 := by
  unfold tailWord_5646447
  simp only [CollatzResearch.WordTrace]
  refine ⟨205942840974894330217969595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137295227316596220145313063 205942840974894330217969595)
  ·
    refine ⟨308914261462341495326954393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205942840974894330217969595 308914261462341495326954393)
    ·
      refine ⟨231685696096756121495215795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308914261462341495326954393 231685696096756121495215795)
      ·
        refine ⟨347528544145134182242823693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231685696096756121495215795 347528544145134182242823693)
        ·
          refine ⟨130323204054425318341058885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347528544145134182242823693 130323204054425318341058885)
          ·
            refine ⟨24435600760204747188948541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130323204054425318341058885 24435600760204747188948541)
            ·
              refine ⟨9163350285076780195855703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24435600760204747188948541 9163350285076780195855703)
              ·
                refine ⟨13745025427615170293783555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163350285076780195855703 13745025427615170293783555)
                ·
                  refine ⟨20617538141422755440675333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13745025427615170293783555 20617538141422755440675333)
                  ·
                    refine ⟨3865788401516766645126625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20617538141422755440675333 3865788401516766645126625)
                    ·
                      refine ⟨2899341301137574983844969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865788401516766645126625 2899341301137574983844969)
                      ·
                        rfl

theorem cell23_5646447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4, 2].length) (baseStart_5646447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646447 prefixEnd_5646447 := by exact prefixLift 5646447
  have htrace : WordTrace (prefixWord ++ tailWord_5646447) baseStart_5646447 baseEnd_5646447 := by
    simpa [prefixWord, tailWord_5646447, baseEnd_5646447] using wordTrace_append hprefix tailTrace_5646447
  have hstable : (prefixWord ++ tailWord_5646447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646447).length < 2 ^ (prefixWord ++ tailWord_5646447).sum := by decide
  have hdescent : baseEnd_5646447 < baseStart_5646447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646487 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 7]
def baseStart_5646487 : Nat := 118140960795 + 5646487 * 2 ^ 59
def prefixEnd_5646487 : Nat := 4983230072969 + 3 ^ 40 * 5646487 * 2
def baseEnd_5646487 : Nat := 322151315595972758593865

theorem tailTrace_5646487 : CollatzResearch.WordTrace tailWord_5646487 prefixEnd_5646487 322151315595972758593865 := by
  unfold tailWord_5646487
  simp only [CollatzResearch.WordTrace]
  refine ⟨205944299894749417049425715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137296199929832944699617143 205944299894749417049425715)
  ·
    refine ⟨308916449842124125574138573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205944299894749417049425715 308916449842124125574138573)
    ·
      refine ⟨115843668690796547090301965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308916449842124125574138573 115843668690796547090301965)
      ·
        refine ⟨43441375759048705158863237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115843668690796547090301965 43441375759048705158863237)
        ·
          refine ⟨8145257954821632217286857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43441375759048705158863237 8145257954821632217286857)
          ·
            refine ⟨6108943466116224162965143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8145257954821632217286857 6108943466116224162965143)
            ·
              refine ⟨9163415199174336244447715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108943466116224162965143 9163415199174336244447715)
              ·
                refine ⟨13745122798761504366671573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163415199174336244447715 13745122798761504366671573)
                ·
                  refine ⟨322151315595972758593865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13745122798761504366671573 322151315595972758593865)
                  ·
                    rfl

theorem cell23_5646487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 7].length) (baseStart_5646487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646487 prefixEnd_5646487 := by exact prefixLift 5646487
  have htrace : WordTrace (prefixWord ++ tailWord_5646487) baseStart_5646487 baseEnd_5646487 := by
    simpa [prefixWord, tailWord_5646487, baseEnd_5646487] using wordTrace_append hprefix tailTrace_5646487
  have hstable : (prefixWord ++ tailWord_5646487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646487).length < 2 ^ (prefixWord ++ tailWord_5646487).sum := by decide
  have hdescent : baseEnd_5646487 < baseStart_5646487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646498 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5646498 : Nat := 118140960795 + 5646498 * 2 ^ 59
def prefixEnd_5646498 : Nat := 4983230072969 + 3 ^ 40 * 5646498 * 2
def baseEnd_5646498 : Nat := 2899367488650954284307235

theorem tailTrace_5646498 : CollatzResearch.WordTrace tailWord_5646498 prefixEnd_5646498 2899367488650954284307235 := by
  unfold tailWord_5646498
  simp only [CollatzResearch.WordTrace]
  refine ⟨51486175274427391482019037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137296467398473043952050765 51486175274427391482019037)
  ·
    refine ⟨19307315727910271805757139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51486175274427391482019037 19307315727910271805757139)
    ·
      refine ⟨28960973591865407708635709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307315727910271805757139 28960973591865407708635709)
      ·
        refine ⟨10860365096949527890738391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28960973591865407708635709 10860365096949527890738391)
        ·
          refine ⟨16290547645424291836107587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10860365096949527890738391 16290547645424291836107587)
          ·
            refine ⟨24435821468136437754161381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16290547645424291836107587 24435821468136437754161381)
            ·
              refine ⟨4581716525275582078905259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24435821468136437754161381 4581716525275582078905259)
              ·
                refine ⟨6872574787913373118357889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581716525275582078905259 6872574787913373118357889)
                ·
                  refine ⟨5154431090935029838768417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6872574787913373118357889 5154431090935029838768417)
                  ·
                    refine ⟨3865823318201272379076313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5154431090935029838768417 3865823318201272379076313)
                    ·
                      refine ⟨2899367488650954284307235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865823318201272379076313 2899367488650954284307235)
                      ·
                        rfl

theorem cell23_5646498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5646498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646498 prefixEnd_5646498 := by exact prefixLift 5646498
  have htrace : WordTrace (prefixWord ++ tailWord_5646498) baseStart_5646498 baseEnd_5646498 := by
    simpa [prefixWord, tailWord_5646498, baseEnd_5646498] using wordTrace_append hprefix tailTrace_5646498
  have hstable : (prefixWord ++ tailWord_5646498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646498).length < 2 ^ (prefixWord ++ tailWord_5646498).sum := by decide
  have hdescent : baseEnd_5646498 < baseStart_5646498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646560 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 6]
def baseStart_5646560 : Nat := 118140960795 + 5646560 * 2 ^ 59
def prefixEnd_5646560 : Nat := 4983230072969 + 3 ^ 40 * 5646560 * 2
def baseEnd_5646560 : Nat := 322155480494614782414661

theorem tailTrace_5646560 : CollatzResearch.WordTrace tailWord_5646560 prefixEnd_5646560 322155480494614782414661 := by
  unfold tailWord_5646560
  simp only [CollatzResearch.WordTrace]
  refine ⟨102973481211742475258416567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137297974948989967011222089 102973481211742475258416567)
  ·
    refine ⟨154460221817613712887624851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102973481211742475258416567 154460221817613712887624851)
    ·
      refine ⟨231690332726420569331437277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154460221817613712887624851 231690332726420569331437277)
      ·
        refine ⟨86883874772407713499288979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231690332726420569331437277 86883874772407713499288979)
        ·
          refine ⟨130325812158611570248933469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86883874772407713499288979 130325812158611570248933469)
          ·
            refine ⟨48872179559479338843350051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130325812158611570248933469 48872179559479338843350051)
            ·
              refine ⟨73308269339219008265025077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48872179559479338843350051 73308269339219008265025077)
              ·
                refine ⟨6872650250551782024846101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73308269339219008265025077 6872650250551782024846101)
                ·
                  refine ⟨322155480494614782414661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6872650250551782024846101 322155480494614782414661)
                  ·
                    rfl

theorem cell23_5646560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_5646560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646560 prefixEnd_5646560 := by exact prefixLift 5646560
  have htrace : WordTrace (prefixWord ++ tailWord_5646560) baseStart_5646560 baseEnd_5646560 := by
    simpa [prefixWord, tailWord_5646560, baseEnd_5646560] using wordTrace_append hprefix tailTrace_5646560
  have hstable : (prefixWord ++ tailWord_5646560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646560).length < 2 ^ (prefixWord ++ tailWord_5646560).sum := by decide
  have hdescent : baseEnd_5646560 < baseStart_5646560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646594 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5646594 : Nat := 118140960795 + 5646594 * 2 ^ 59
def prefixEnd_5646594 : Nat := 4983230072969 + 3 ^ 40 * 5646594 * 2
def baseEnd_5646594 : Nat := 322157420310420656522977

theorem tailTrace_5646594 : CollatzResearch.WordTrace tailWord_5646594 prefixEnd_5646594 322157420310420656522977 := by
  unfold tailWord_5646594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487050626340443580892709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137298801670241182882380557 51487050626340443580892709)
  ·
    refine ⟨9653821992438833171417383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51487050626340443580892709 9653821992438833171417383)
    ·
      refine ⟨14480732988658249757126075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653821992438833171417383 14480732988658249757126075)
      ·
        refine ⟨21721099482987374635689113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14480732988658249757126075 21721099482987374635689113)
        ·
          refine ⟨16290824612240530976766835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21721099482987374635689113 16290824612240530976766835)
          ·
            refine ⟨24436236918360796465150253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16290824612240530976766835 24436236918360796465150253)
            ·
              refine ⟨9163588844385298674431345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24436236918360796465150253 9163588844385298674431345)
              ·
                refine ⟨6872691633288974005823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9163588844385298674431345 6872691633288974005823509)
                ·
                  refine ⟨322157420310420656522977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6872691633288974005823509 322157420310420656522977)
                  ·
                    rfl

theorem cell23_5646594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5646594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646594 prefixEnd_5646594 := by exact prefixLift 5646594
  have htrace : WordTrace (prefixWord ++ tailWord_5646594) baseStart_5646594 baseEnd_5646594 := by
    simpa [prefixWord, tailWord_5646594, baseEnd_5646594] using wordTrace_append hprefix tailTrace_5646594
  have hstable : (prefixWord ++ tailWord_5646594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646594).length < 2 ^ (prefixWord ++ tailWord_5646594).sum := by decide
  have hdescent : baseEnd_5646594 < baseStart_5646594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646604 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_5646604 : Nat := 118140960795 + 5646604 * 2 ^ 59
def prefixEnd_5646604 : Nat := 4983230072969 + 3 ^ 40 * 5646604 * 2
def baseEnd_5646604 : Nat := 2899421917600330869581747

theorem tailTrace_5646604 : CollatzResearch.WordTrace tailWord_5646604 prefixEnd_5646604 2899421917600330869581747 := by
  unfold tailWord_5646604
  simp only [CollatzResearch.WordTrace]
  refine ⟨102974283617662773015717433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137299044823550364020956577 102974283617662773015717433)
  ·
    refine ⟨77230712713247079761788075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102974283617662773015717433 77230712713247079761788075)
    ·
      refine ⟨115846069069870619642682113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77230712713247079761788075 115846069069870619642682113)
      ·
        refine ⟨86884551802402964732011585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115846069069870619642682113 86884551802402964732011585)
        ·
          refine ⟨65163413851802223549008689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86884551802402964732011585 65163413851802223549008689)
          ·
            refine ⟨48872560388851667661756517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65163413851802223549008689 48872560388851667661756517)
            ·
              refine ⟨9163605072909687686579347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48872560388851667661756517 9163605072909687686579347)
              ·
                refine ⟨13745407609364531529869021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163605072909687686579347 13745407609364531529869021)
                ·
                  refine ⟨5154527853511699323700883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13745407609364531529869021 5154527853511699323700883)
                  ·
                    refine ⟨7731791780267548985551325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154527853511699323700883 7731791780267548985551325)
                    ·
                      refine ⟨2899421917600330869581747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7731791780267548985551325 2899421917600330869581747)
                      ·
                        rfl

theorem cell23_5646604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_5646604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646604 prefixEnd_5646604 := by exact prefixLift 5646604
  have htrace : WordTrace (prefixWord ++ tailWord_5646604) baseStart_5646604 baseEnd_5646604 := by
    simpa [prefixWord, tailWord_5646604, baseEnd_5646604] using wordTrace_append hprefix tailTrace_5646604
  have hstable : (prefixWord ++ tailWord_5646604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646604).length < 2 ^ (prefixWord ++ tailWord_5646604).sum := by decide
  have hdescent : baseEnd_5646604 < baseStart_5646604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646624 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_5646624 : Nat := 118140960795 + 5646624 * 2 ^ 59
def prefixEnd_5646624 : Nat := 4983230072969 + 3 ^ 40 * 5646624 * 2
def baseEnd_5646624 : Nat := 966477395737806930443885

theorem tailTrace_5646624 : CollatzResearch.WordTrace tailWord_5646624 prefixEnd_5646624 966477395737806930443885 := by
  unfold tailWord_5646624
  simp only [CollatzResearch.WordTrace]
  refine ⟨102974648347626544723581463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137299531130168726298108617 102974648347626544723581463)
  ·
    refine ⟨154461972521439817085372195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102974648347626544723581463 154461972521439817085372195)
    ·
      refine ⟨231692958782159725628058293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154461972521439817085372195 231692958782159725628058293)
      ·
        refine ⟨21721214885827474277630465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231692958782159725628058293 21721214885827474277630465)
        ·
          refine ⟨16290911164370605708222849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21721214885827474277630465 16290911164370605708222849)
          ·
            refine ⟨12218183373277954281167137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16290911164370605708222849 12218183373277954281167137)
            ·
              refine ⟨9163637529958465710875353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12218183373277954281167137 9163637529958465710875353)
              ·
                refine ⟨6872728147468849283156515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9163637529958465710875353 6872728147468849283156515)
                ·
                  refine ⟨10309092221203273924734773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6872728147468849283156515 10309092221203273924734773)
                  ·
                    refine ⟨966477395737806930443885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10309092221203273924734773 966477395737806930443885)
                    ·
                      rfl

theorem cell23_5646624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_5646624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646624 prefixEnd_5646624 := by exact prefixLift 5646624
  have htrace : WordTrace (prefixWord ++ tailWord_5646624) baseStart_5646624 baseEnd_5646624 := by
    simpa [prefixWord, tailWord_5646624, baseEnd_5646624] using wordTrace_append hprefix tailTrace_5646624
  have hstable : (prefixWord ++ tailWord_5646624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646624).length < 2 ^ (prefixWord ++ tailWord_5646624).sum := by decide
  have hdescent : baseEnd_5646624 < baseStart_5646624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646627 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 6, 2]
def baseStart_5646627 : Nat := 118140960795 + 5646627 * 2 ^ 59
def prefixEnd_5646627 : Nat := 4983230072969 + 3 ^ 40 * 5646627 * 2
def baseEnd_5646627 : Nat := 2899433727655384279594141

theorem tailTrace_5646627 : CollatzResearch.WordTrace tailWord_5646627 prefixEnd_5646627 2899433727655384279594141 := by
  unfold tailWord_5646627
  simp only [CollatzResearch.WordTrace]
  refine ⟨205949406114242220959522135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137299604076161480639681423 205949406114242220959522135)
  ·
    refine ⟨308924109171363331439283203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205949406114242220959522135 308924109171363331439283203)
    ·
      refine ⟨463386163757044997158924805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308924109171363331439283203 463386163757044997158924805)
      ·
        refine ⟨86884905704445936967298401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463386163757044997158924805 86884905704445936967298401)
        ·
          refine ⟨65163679278334452725473801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86884905704445936967298401 65163679278334452725473801)
          ·
            refine ⟨48872759458750839544105351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65163679278334452725473801 48872759458750839544105351)
            ·
              refine ⟨73309139188126259316158027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48872759458750839544105351 73309139188126259316158027)
              ·
                refine ⟨109963708782189388974237041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73309139188126259316158027 109963708782189388974237041)
                ·
                  refine ⟨82472781586642041730677781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109963708782189388974237041 82472781586642041730677781)
                  ·
                    refine ⟨3865911636873845706125521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82472781586642041730677781 3865911636873845706125521)
                    ·
                      refine ⟨2899433727655384279594141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865911636873845706125521 2899433727655384279594141)
                      ·
                        rfl

theorem cell23_5646627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_5646627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646627 prefixEnd_5646627 := by exact prefixLift 5646627
  have htrace : WordTrace (prefixWord ++ tailWord_5646627) baseStart_5646627 baseEnd_5646627 := by
    simpa [prefixWord, tailWord_5646627, baseEnd_5646627] using wordTrace_append hprefix tailTrace_5646627
  have hstable : (prefixWord ++ tailWord_5646627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646627).length < 2 ^ (prefixWord ++ tailWord_5646627).sum := by decide
  have hdescent : baseEnd_5646627 < baseStart_5646627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646650 : List Nat := [3, 1, 1, 1, 4, 2, 11]
def baseStart_5646650 : Nat := 118140960795 + 5646650 * 2 ^ 59
def prefixEnd_5646650 : Nat := 4983230072969 + 3 ^ 40 * 5646650 * 2
def baseEnd_5646650 : Nat := 35795623922351082587735

theorem tailTrace_5646650 : CollatzResearch.WordTrace tailWord_5646650 prefixEnd_5646650 35795623922351082587735 := by
  unfold tailWord_5646650
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487561248289723971902351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137300163328772597258406269 51487561248289723971902351)
  ·
    refine ⟨77231341872434585957853527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51487561248289723971902351 77231341872434585957853527)
    ·
      refine ⟨115847012808651878936780291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77231341872434585957853527 115847012808651878936780291)
      ·
        refine ⟨173770519212977818405170437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115847012808651878936780291 173770519212977818405170437)
        ·
          refine ⟨32581972352433340950969457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173770519212977818405170437 32581972352433340950969457)
          ·
            refine ⟨24436479264325005713227093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32581972352433340950969457 24436479264325005713227093)
            ·
              refine ⟨35795623922351082587735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24436479264325005713227093 35795623922351082587735)
              ·
                rfl

theorem cell23_5646650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 11].length) (baseStart_5646650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646650 prefixEnd_5646650 := by exact prefixLift 5646650
  have htrace : WordTrace (prefixWord ++ tailWord_5646650) baseStart_5646650 baseEnd_5646650 := by
    simpa [prefixWord, tailWord_5646650, baseEnd_5646650] using wordTrace_append hprefix tailTrace_5646650
  have hstable : (prefixWord ++ tailWord_5646650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646650).length < 2 ^ (prefixWord ++ tailWord_5646650).sum := by decide
  have hdescent : baseEnd_5646650 < baseStart_5646650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646654 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5646654 : Nat := 118140960795 + 5646654 * 2 ^ 59
def prefixEnd_5646654 : Nat := 4983230072969 + 3 ^ 40 * 5646654 * 2
def baseEnd_5646654 : Nat := 966482530544351891318839

theorem tailTrace_5646654 : CollatzResearch.WordTrace tailWord_5646654 prefixEnd_5646654 966482530544351891318839 := by
  unfold tailWord_5646654
  simp only [CollatzResearch.WordTrace]
  refine ⟨25743798860643050571344377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137300260590096269713836677 25743798860643050571344377)
  ·
    refine ⟨19307849145482287928508283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25743798860643050571344377 19307849145482287928508283)
    ·
      refine ⟨28961773718223431892762425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307849145482287928508283 28961773718223431892762425)
      ·
        refine ⟨21721330288667573919571819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28961773718223431892762425 21721330288667573919571819)
        ·
          refine ⟨32581995433001360879357729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21721330288667573919571819 32581995433001360879357729)
          ·
            refine ⟨24436496574751020659518297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32581995433001360879357729 24436496574751020659518297)
            ·
              refine ⟨18327372431063265494638723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24436496574751020659518297 18327372431063265494638723)
              ·
                refine ⟨27491058646594898241958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18327372431063265494638723 27491058646594898241958085)
                ·
                  refine ⟨5154573496236543420367141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27491058646594898241958085 5154573496236543420367141)
                  ·
                    refine ⟨966482530544351891318839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5154573496236543420367141 966482530544351891318839)
                    ·
                      rfl

theorem cell23_5646654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5646654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646654 prefixEnd_5646654 := by exact prefixLift 5646654
  have htrace : WordTrace (prefixWord ++ tailWord_5646654) baseStart_5646654 baseEnd_5646654 := by
    simpa [prefixWord, tailWord_5646654, baseEnd_5646654] using wordTrace_append hprefix tailTrace_5646654
  have hstable : (prefixWord ++ tailWord_5646654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646654).length < 2 ^ (prefixWord ++ tailWord_5646654).sum := by decide
  have hdescent : baseEnd_5646654 < baseStart_5646654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646680 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_5646680 : Nat := 118140960795 + 5646680 * 2 ^ 59
def prefixEnd_5646680 : Nat := 4983230072969 + 3 ^ 40 * 5646680 * 2
def baseEnd_5646680 : Nat := 966486980710024190743799

theorem tailTrace_5646680 : CollatzResearch.WordTrace tailWord_5646680 prefixEnd_5646680 966486980710024190743799 := by
  unfold tailWord_5646680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102975669591525105505600747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137300892788700140674134329 102975669591525105505600747)
  ·
    refine ⟨154463504387287658258401121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102975669591525105505600747 154463504387287658258401121)
    ·
      refine ⟨115847628290465743693800841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154463504387287658258401121 115847628290465743693800841)
      ·
        refine ⟨86885721217849307770350631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115847628290465743693800841 86885721217849307770350631)
        ·
          refine ⟨130328581826773961655525947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86885721217849307770350631 130328581826773961655525947)
          ·
            refine ⟨195492872740160942483288921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130328581826773961655525947 195492872740160942483288921)
            ·
              refine ⟨146619654555120706862466691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195492872740160942483288921 146619654555120706862466691)
              ·
                refine ⟨219929481832681060293700037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146619654555120706862466691 219929481832681060293700037)
                ·
                  refine ⟨41236777843627698805068757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219929481832681060293700037 41236777843627698805068757)
                  ·
                    refine ⟨966486980710024190743799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41236777843627698805068757 966486980710024190743799)
                    ·
                      rfl

theorem cell23_5646680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_5646680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646680 prefixEnd_5646680 := by exact prefixLift 5646680
  have htrace : WordTrace (prefixWord ++ tailWord_5646680) baseStart_5646680 baseEnd_5646680 := by
    simpa [prefixWord, tailWord_5646680, baseEnd_5646680] using wordTrace_append hprefix tailTrace_5646680
  have hstable : (prefixWord ++ tailWord_5646680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646680).length < 2 ^ (prefixWord ++ tailWord_5646680).sum := by decide
  have hdescent : baseEnd_5646680 < baseStart_5646680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646698 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5646698 : Nat := 118140960795 + 5646698 * 2 ^ 59
def prefixEnd_5646698 : Nat := 4983230072969 + 3 ^ 40 * 5646698 * 2
def baseEnd_5646698 : Nat := 2899470184781853501806315

theorem tailTrace_5646698 : CollatzResearch.WordTrace tailWord_5646698 prefixEnd_5646698 2899470184781853501806315 := by
  unfold tailWord_5646698
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487998924246250021339187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137301330464656666723571165 51487998924246250021339187)
  ·
    refine ⟨77231998386369375032008781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51487998924246250021339187 77231998386369375032008781)
    ·
      refine ⟨28961999394888515637003293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77231998386369375032008781 28961999394888515637003293)
      ·
        refine ⟨10860749773083193363876235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28961999394888515637003293 10860749773083193363876235)
        ·
          refine ⟨16291124659624790045814353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10860749773083193363876235 16291124659624790045814353)
          ·
            refine ⟨12218343494718592534360765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16291124659624790045814353 12218343494718592534360765)
            ·
              refine ⟨4581878810519472200385287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12218343494718592534360765 4581878810519472200385287)
              ·
                refine ⟨6872818215779208300577931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581878810519472200385287 6872818215779208300577931)
                ·
                  refine ⟨10309227323668812450866897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6872818215779208300577931 10309227323668812450866897)
                  ·
                    refine ⟨7731920492751609338150173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10309227323668812450866897 7731920492751609338150173)
                    ·
                      refine ⟨2899470184781853501806315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7731920492751609338150173 2899470184781853501806315)
                      ·
                        rfl

theorem cell23_5646698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5646698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646698 prefixEnd_5646698 := by exact prefixLift 5646698
  have htrace : WordTrace (prefixWord ++ tailWord_5646698) baseStart_5646698 baseEnd_5646698 := by
    simpa [prefixWord, tailWord_5646698, baseEnd_5646698] using wordTrace_append hprefix tailTrace_5646698
  have hstable : (prefixWord ++ tailWord_5646698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646698).length < 2 ^ (prefixWord ++ tailWord_5646698).sum := by decide
  have hdescent : baseEnd_5646698 < baseStart_5646698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646717 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_5646717 : Nat := 118140960795 + 5646717 * 2 ^ 59
def prefixEnd_5646717 : Nat := 4983230072969 + 3 ^ 40 * 5646717 * 2
def baseEnd_5646717 : Nat := 2899479940914288927468727

theorem tailTrace_5646717 : CollatzResearch.WordTrace tailWord_5646717 prefixEnd_5646717 2899479940914288927468727 := by
  unfold tailWord_5646717
  simp only [CollatzResearch.WordTrace]
  refine ⟨205952688683916166330298405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137301792455944110886865603 205952688683916166330298405)
  ·
    refine ⟨38616129128234281186930951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205952688683916166330298405 38616129128234281186930951)
    ·
      refine ⟨57924193692351421780396427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38616129128234281186930951 57924193692351421780396427)
      ·
        refine ⟨86886290538527132670594641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57924193692351421780396427 86886290538527132670594641)
        ·
          refine ⟨65164717903895349502945981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86886290538527132670594641 65164717903895349502945981)
          ·
            refine ⟨24436769213960756063604743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65164717903895349502945981 24436769213960756063604743)
            ·
              refine ⟨36655153820941134095407115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24436769213960756063604743 36655153820941134095407115)
              ·
                refine ⟨54982730731411701143110673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36655153820941134095407115 54982730731411701143110673)
                ·
                  refine ⟨41237048048558775857333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54982730731411701143110673 41237048048558775857333005)
                  ·
                    refine ⟨15463893018209540946499877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41237048048558775857333005 15463893018209540946499877)
                    ·
                      refine ⟨2899479940914288927468727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15463893018209540946499877 2899479940914288927468727)
                      ·
                        rfl

theorem cell23_5646717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_5646717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646717 prefixEnd_5646717 := by exact prefixLift 5646717
  have htrace : WordTrace (prefixWord ++ tailWord_5646717) baseStart_5646717 baseEnd_5646717 := by
    simpa [prefixWord, tailWord_5646717, baseEnd_5646717] using wordTrace_append hprefix tailTrace_5646717
  have hstable : (prefixWord ++ tailWord_5646717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646717).length < 2 ^ (prefixWord ++ tailWord_5646717).sum := by decide
  have hdescent : baseEnd_5646717 < baseStart_5646717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646721 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5646721 : Nat := 118140960795 + 5646721 * 2 ^ 59
def prefixEnd_5646721 : Nat := 4983230072969 + 3 ^ 40 * 5646721 * 2
def baseEnd_5646721 : Nat := 2899481994836906911818709

theorem tailTrace_5646721 : CollatzResearch.WordTrace tailWord_5646721 prefixEnd_5646721 2899481994836906911818709 := by
  unfold tailWord_5646721
  simp only [CollatzResearch.WordTrace]
  refine ⟨205952834575901675013444017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137301889717267783342296011 205952834575901675013444017)
  ·
    refine ⟨154464625931926256260083013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205952834575901675013444017 154464625931926256260083013)
    ·
      refine ⟨28962117362236173048765565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154464625931926256260083013 28962117362236173048765565)
      ·
        refine ⟨10860794010838564893287087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28962117362236173048765565 10860794010838564893287087)
        ·
          refine ⟨16291191016257847339930631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10860794010838564893287087 16291191016257847339930631)
          ·
            refine ⟨24436786524386771009895947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291191016257847339930631 24436786524386771009895947)
            ·
              refine ⟨36655179786580156514843921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24436786524386771009895947 36655179786580156514843921)
              ·
                refine ⟨27491384839935117386132941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36655179786580156514843921 27491384839935117386132941)
                ·
                  refine ⟨10309269314975669019799853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27491384839935117386132941 10309269314975669019799853)
                  ·
                    refine ⟨3865975993115875882424945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10309269314975669019799853 3865975993115875882424945)
                    ·
                      refine ⟨2899481994836906911818709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865975993115875882424945 2899481994836906911818709)
                      ·
                        rfl

theorem cell23_5646721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5646721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646721 prefixEnd_5646721 := by exact prefixLift 5646721
  have htrace : WordTrace (prefixWord ++ tailWord_5646721) baseStart_5646721 baseEnd_5646721 := by
    simpa [prefixWord, tailWord_5646721, baseEnd_5646721] using wordTrace_append hprefix tailTrace_5646721
  have hstable : (prefixWord ++ tailWord_5646721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646721).length < 2 ^ (prefixWord ++ tailWord_5646721).sum := by decide
  have hdescent : baseEnd_5646721 < baseStart_5646721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646727 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 6]
def baseStart_5646727 : Nat := 118140960795 + 5646727 * 2 ^ 59
def prefixEnd_5646727 : Nat := 4983230072969 + 3 ^ 40 * 5646727 * 2
def baseEnd_5646727 : Nat := 966495025240277962781227

theorem tailTrace_5646727 : CollatzResearch.WordTrace tailWord_5646727 prefixEnd_5646727 966495025240277962781227 := by
  unfold tailWord_5646727
  simp only [CollatzResearch.WordTrace]
  refine ⟨205953053413879938038162435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137302035609253292025441623 205953053413879938038162435)
  ·
    refine ⟨308929580120819907057243653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205953053413879938038162435 308929580120819907057243653)
    ·
      refine ⟨57924296272653732573233185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308929580120819907057243653 57924296272653732573233185)
      ·
        refine ⟨43443222204490299429924889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57924296272653732573233185 43443222204490299429924889)
        ·
          refine ⟨32582416653367724572443667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43443222204490299429924889 32582416653367724572443667)
          ·
            refine ⟨48873624980051586858665501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32582416653367724572443667 48873624980051586858665501)
            ·
              refine ⟨18327609367519345071999563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48873624980051586858665501 18327609367519345071999563)
              ·
                refine ⟨27491414051279017607999345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18327609367519345071999563 27491414051279017607999345)
                ·
                  refine ⟨20618560538459263205999509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27491414051279017607999345 20618560538459263205999509)
                  ·
                    refine ⟨966495025240277962781227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20618560538459263205999509 966495025240277962781227)
                    ·
                      rfl

theorem cell23_5646727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_5646727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646727 prefixEnd_5646727 := by exact prefixLift 5646727
  have htrace : WordTrace (prefixWord ++ tailWord_5646727) baseStart_5646727 baseEnd_5646727 := by
    simpa [prefixWord, tailWord_5646727, baseEnd_5646727] using wordTrace_append hprefix tailTrace_5646727
  have hstable : (prefixWord ++ tailWord_5646727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646727).length < 2 ^ (prefixWord ++ tailWord_5646727).sum := by decide
  have hdescent : baseEnd_5646727 < baseStart_5646727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646751 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 4, 2, 2]
def baseStart_5646751 : Nat := 118140960795 + 5646751 * 2 ^ 59
def prefixEnd_5646751 : Nat := 4983230072969 + 3 ^ 40 * 5646751 * 2
def baseEnd_5646751 : Nat := 2899497399256541794443571

theorem tailTrace_5646751 : CollatzResearch.WordTrace tailWord_5646751 prefixEnd_5646751 2899497399256541794443571 := by
  unfold tailWord_5646751
  simp only [CollatzResearch.WordTrace]
  refine ⟨205953928765792990137036107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137302619177195326758024071 205953928765792990137036107)
  ·
    refine ⟨308930893148689485205554161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205953928765792990137036107 308930893148689485205554161)
    ·
      refine ⟨231698169861517113904165621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308930893148689485205554161 231698169861517113904165621)
      ·
        refine ⟨21721703424517229428515527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231698169861517113904165621 21721703424517229428515527)
        ·
          refine ⟨32582555136775844142773291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21721703424517229428515527 32582555136775844142773291)
          ·
            refine ⟨48873832705163766214159937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32582555136775844142773291 48873832705163766214159937)
            ·
              refine ⟨36655374528872824660619953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48873832705163766214159937 36655374528872824660619953)
              ·
                refine ⟨27491530896654618495464965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36655374528872824660619953 27491530896654618495464965)
                ·
                  refine ⟨5154662043122740967899681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27491530896654618495464965 5154662043122740967899681)
                  ·
                    refine ⟨3865996532342055725924761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5154662043122740967899681 3865996532342055725924761)
                    ·
                      refine ⟨2899497399256541794443571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3865996532342055725924761 2899497399256541794443571)
                      ·
                        rfl

theorem cell23_5646751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_5646751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646751 prefixEnd_5646751 := by exact prefixLift 5646751
  have htrace : WordTrace (prefixWord ++ tailWord_5646751) baseStart_5646751 baseEnd_5646751 := by
    simpa [prefixWord, tailWord_5646751, baseEnd_5646751] using wordTrace_append hprefix tailTrace_5646751
  have hstable : (prefixWord ++ tailWord_5646751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646751).length < 2 ^ (prefixWord ++ tailWord_5646751).sum := by decide
  have hdescent : baseEnd_5646751 < baseStart_5646751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646804 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_5646804 : Nat := 118140960795 + 5646804 * 2 ^ 59
def prefixEnd_5646804 : Nat := 4983230072969 + 3 ^ 40 * 5646804 * 2
def baseEnd_5646804 : Nat := 966508204577076695693609

theorem tailTrace_5646804 : CollatzResearch.WordTrace tailWord_5646804 prefixEnd_5646804 966508204577076695693609 := by
  unfold tailWord_5646804
  simp only [CollatzResearch.WordTrace]
  refine ⟨102977930917300490094357733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137303907889733986792476977 102977930917300490094357733)
  ·
    refine ⟨19308362046993841892692075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102977930917300490094357733 19308362046993841892692075)
    ·
      refine ⟨28962543070490762839038113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19308362046993841892692075 28962543070490762839038113)
      ·
        refine ⟨21721907302868072129278585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28962543070490762839038113 21721907302868072129278585)
        ·
          refine ⟨16291430477151054096958939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21721907302868072129278585 16291430477151054096958939)
          ·
            refine ⟨24437145715726581145438409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291430477151054096958939 24437145715726581145438409)
            ·
              refine ⟨18327859286794935859078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24437145715726581145438409 18327859286794935859078807)
              ·
                refine ⟨27491788930192403788618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18327859286794935859078807 27491788930192403788618211)
                ·
                  refine ⟨41237683395288605682927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27491788930192403788618211 41237683395288605682927317)
                  ·
                    refine ⟨966508204577076695693609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41237683395288605682927317 966508204577076695693609)
                    ·
                      rfl

theorem cell23_5646804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_5646804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646804 prefixEnd_5646804 := by exact prefixLift 5646804
  have htrace : WordTrace (prefixWord ++ tailWord_5646804) baseStart_5646804 baseEnd_5646804 := by
    simpa [prefixWord, tailWord_5646804, baseEnd_5646804] using wordTrace_append hprefix tailTrace_5646804
  have hstable : (prefixWord ++ tailWord_5646804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646804).length < 2 ^ (prefixWord ++ tailWord_5646804).sum := by decide
  have hdescent : baseEnd_5646804 < baseStart_5646804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646821 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_5646821 : Nat := 118140960795 + 5646821 * 2 ^ 59
def prefixEnd_5646821 : Nat := 4983230072969 + 3 ^ 40 * 5646821 * 2
def baseEnd_5646821 : Nat := 966511114300785506856083

theorem tailTrace_5646821 : CollatzResearch.WordTrace tailWord_5646821 prefixEnd_5646821 966511114300785506856083 := by
  unfold tailWord_5646821
  simp only [CollatzResearch.WordTrace]
  refine ⟨205956481875539392092084317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137304321250359594728056211 205956481875539392092084317)
  ·
    refine ⟨77233680703327272034531619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205956481875539392092084317 77233680703327272034531619)
    ·
      refine ⟨115850521054990908051797429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77233680703327272034531619 115850521054990908051797429)
      ·
        refine ⟨10860986348905397629856009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115850521054990908051797429 10860986348905397629856009)
        ·
          refine ⟨8145739761679048222392007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10860986348905397629856009 8145739761679048222392007)
          ·
            refine ⟨12218609642518572333588011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8145739761679048222392007 12218609642518572333588011)
            ·
              refine ⟨18327914463777858500382017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218609642518572333588011 18327914463777858500382017)
              ·
                refine ⟨13745935847833393875286513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18327914463777858500382017 13745935847833393875286513)
                ·
                  refine ⟨10309451885875045406464885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13745935847833393875286513 10309451885875045406464885)
                  ·
                    refine ⟨966511114300785506856083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10309451885875045406464885 966511114300785506856083)
                    ·
                      rfl

theorem cell23_5646821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_5646821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646821 prefixEnd_5646821 := by exact prefixLift 5646821
  have htrace : WordTrace (prefixWord ++ tailWord_5646821) baseStart_5646821 baseEnd_5646821 := by
    simpa [prefixWord, tailWord_5646821, baseEnd_5646821] using wordTrace_append hprefix tailTrace_5646821
  have hstable : (prefixWord ++ tailWord_5646821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646821).length < 2 ^ (prefixWord ++ tailWord_5646821).sum := by decide
  have hdescent : baseEnd_5646821 < baseStart_5646821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646824 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5646824 : Nat := 118140960795 + 5646824 * 2 ^ 59
def prefixEnd_5646824 : Nat := 4983230072969 + 3 ^ 40 * 5646824 * 2
def baseEnd_5646824 : Nat := 2899534883344320008830735

theorem tailTrace_5646824 : CollatzResearch.WordTrace tailWord_5646824 prefixEnd_5646824 2899534883344320008830735 := by
  unfold tailWord_5646824
  simp only [CollatzResearch.WordTrace]
  refine ⟨102978295647264261802221763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137304394196352349069629017 102978295647264261802221763)
  ·
    refine ⟨154467443470896392703332645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102978295647264261802221763 154467443470896392703332645)
    ·
      refine ⟨28962645650793073631874871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154467443470896392703332645 28962645650793073631874871)
      ·
        refine ⟨43443968476189610447812307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28962645650793073631874871 43443968476189610447812307)
        ·
          refine ⟨65165952714284415671718461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43443968476189610447812307 65165952714284415671718461)
          ·
            refine ⟨24437232267856655876894423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65165952714284415671718461 24437232267856655876894423)
            ·
              refine ⟨36655848401784983815341635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24437232267856655876894423 36655848401784983815341635)
              ·
                refine ⟨54983772602677475723012453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36655848401784983815341635 54983772602677475723012453)
                ·
                  refine ⟨10309457363002026698064835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54983772602677475723012453 10309457363002026698064835)
                  ·
                    refine ⟨15464186044503040047097253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10309457363002026698064835 15464186044503040047097253)
                    ·
                      refine ⟨2899534883344320008830735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15464186044503040047097253 2899534883344320008830735)
                      ·
                        rfl

theorem cell23_5646824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5646824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646824 prefixEnd_5646824 := by exact prefixLift 5646824
  have htrace : WordTrace (prefixWord ++ tailWord_5646824) baseStart_5646824 baseEnd_5646824 := by
    simpa [prefixWord, tailWord_5646824, baseEnd_5646824] using wordTrace_append hprefix tailTrace_5646824
  have hstable : (prefixWord ++ tailWord_5646824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646824).length < 2 ^ (prefixWord ++ tailWord_5646824).sum := by decide
  have hdescent : baseEnd_5646824 < baseStart_5646824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646844 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_5646844 : Nat := 118140960795 + 5646844 * 2 ^ 59
def prefixEnd_5646844 : Nat := 4983230072969 + 3 ^ 40 * 5646844 * 2
def baseEnd_5646844 : Nat := 2899545152957409930580643

theorem tailTrace_5646844 : CollatzResearch.WordTrace tailWord_5646844 prefixEnd_5646844 2899545152957409930580643 := by
  unfold tailWord_5646844
  simp only [CollatzResearch.WordTrace]
  refine ⟨102978660377228033510085793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137304880502970711346781057 102978660377228033510085793)
  ·
    refine ⟨77233995282921025132564345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102978660377228033510085793 77233995282921025132564345)
    ·
      refine ⟨57925496462190768849423259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77233995282921025132564345 57925496462190768849423259)
      ·
        refine ⟨86888244693286153274134889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57925496462190768849423259 86888244693286153274134889)
        ·
          refine ⟨65166183519964614955601167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86888244693286153274134889 65166183519964614955601167)
          ·
            refine ⟨97749275279946922433401751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65166183519964614955601167 97749275279946922433401751)
            ·
              refine ⟨146623912919920383650102627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97749275279946922433401751 146623912919920383650102627)
              ·
                refine ⟨219935869379880575475153941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146623912919920383650102627 219935869379880575475153941)
                ·
                  refine ⟨10309493877181901975397841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219935869379880575475153941 10309493877181901975397841)
                  ·
                    refine ⟨7732120407886426481548381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10309493877181901975397841 7732120407886426481548381)
                    ·
                      refine ⟨2899545152957409930580643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732120407886426481548381 2899545152957409930580643)
                      ·
                        rfl

theorem cell23_5646844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_5646844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646844 prefixEnd_5646844 := by exact prefixLift 5646844
  have htrace : WordTrace (prefixWord ++ tailWord_5646844) baseStart_5646844 baseEnd_5646844 := by
    simpa [prefixWord, tailWord_5646844, baseEnd_5646844] using wordTrace_append hprefix tailTrace_5646844
  have hstable : (prefixWord ++ tailWord_5646844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646844).length < 2 ^ (prefixWord ++ tailWord_5646844).sum := by decide
  have hdescent : baseEnd_5646844 < baseStart_5646844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646901 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_5646901 : Nat := 118140960795 + 5646901 * 2 ^ 59
def prefixEnd_5646901 : Nat := 4983230072969 + 3 ^ 40 * 5646901 * 2
def baseEnd_5646901 : Nat := 2899574421354716207567881

theorem tailTrace_5646901 : CollatzResearch.WordTrace tailWord_5646901 prefixEnd_5646901 2899574421354716207567881 := by
  unfold tailWord_5646901
  simp only [CollatzResearch.WordTrace]
  refine ⟨205959399715249565754996557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137306266476833043836664371 205959399715249565754996557)
  ·
    refine ⟨77234774893218587158123709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205959399715249565754996557 77234774893218587158123709)
    ·
      refine ⟨28963040584956970184296391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77234774893218587158123709 28963040584956970184296391)
      ·
        refine ⟨43444560877435455276444587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28963040584956970184296391 43444560877435455276444587)
        ·
          refine ⟨65166841316153182914666881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43444560877435455276444587 65166841316153182914666881)
          ·
            refine ⟨48875130987114887186000161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65166841316153182914666881 48875130987114887186000161)
            ·
              refine ⟨36656348240336165389500121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48875130987114887186000161 36656348240336165389500121)
              ·
                refine ⟨27492261180252124042125091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36656348240336165389500121 27492261180252124042125091)
                ·
                  refine ⟨41238391770378186063187637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27492261180252124042125091 41238391770378186063187637)
                  ·
                    refine ⟨3866099228472954943423841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41238391770378186063187637 3866099228472954943423841)
                    ·
                      refine ⟨2899574421354716207567881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866099228472954943423841 2899574421354716207567881)
                      ·
                        rfl

theorem cell23_5646901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_5646901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646901 prefixEnd_5646901 := by exact prefixLift 5646901
  have htrace : WordTrace (prefixWord ++ tailWord_5646901) baseStart_5646901 baseEnd_5646901 := by
    simpa [prefixWord, tailWord_5646901, baseEnd_5646901] using wordTrace_append hprefix tailTrace_5646901
  have hstable : (prefixWord ++ tailWord_5646901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646901).length < 2 ^ (prefixWord ++ tailWord_5646901).sum := by decide
  have hdescent : baseEnd_5646901 < baseStart_5646901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646908 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_5646908 : Nat := 118140960795 + 5646908 * 2 ^ 59
def prefixEnd_5646908 : Nat := 4983230072969 + 3 ^ 40 * 5646908 * 2
def baseEnd_5646908 : Nat := 2899578015719297680180349

theorem tailTrace_5646908 : CollatzResearch.WordTrace tailWord_5646908 prefixEnd_5646908 2899578015719297680180349 := by
  unfold tailWord_5646908
  simp only [CollatzResearch.WordTrace]
  refine ⟨102979827513112102975250689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137306436684149470633667585 102979827513112102975250689)
  ·
    refine ⟨77234870634834077231438017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102979827513112102975250689 77234870634834077231438017)
    ·
      refine ⟨57926152976125557923578513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77234870634834077231438017 57926152976125557923578513)
      ·
        refine ⟨43444614732094168442683885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57926152976125557923578513 43444614732094168442683885)
        ·
          refine ⟨16291730524535313166006457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43444614732094168442683885 16291730524535313166006457)
          ·
            refine ⟨12218797893401484874504843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16291730524535313166006457 12218797893401484874504843)
            ·
              refine ⟨18328196840102227311757265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218797893401484874504843 18328196840102227311757265)
              ·
                refine ⟨13746147630076670483817949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18328196840102227311757265 13746147630076670483817949)
                ·
                  refine ⟨5154805361278751431431731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13746147630076670483817949 5154805361278751431431731)
                  ·
                    refine ⟨7732208041918127147147597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154805361278751431431731 7732208041918127147147597)
                    ·
                      refine ⟨2899578015719297680180349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732208041918127147147597 2899578015719297680180349)
                      ·
                        rfl

theorem cell23_5646908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_5646908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646908 prefixEnd_5646908 := by exact prefixLift 5646908
  have htrace : WordTrace (prefixWord ++ tailWord_5646908) baseStart_5646908 baseEnd_5646908 := by
    simpa [prefixWord, tailWord_5646908, baseEnd_5646908] using wordTrace_append hprefix tailTrace_5646908
  have hstable : (prefixWord ++ tailWord_5646908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646908).length < 2 ^ (prefixWord ++ tailWord_5646908).sum := by decide
  have hdescent : baseEnd_5646908 < baseStart_5646908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646924 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_5646924 : Nat := 118140960795 + 5646924 * 2 ^ 59
def prefixEnd_5646924 : Nat := 4983230072969 + 3 ^ 40 * 5646924 * 2
def baseEnd_5646924 : Nat := 966528743803256539193425

theorem tailTrace_5646924 : CollatzResearch.WordTrace tailWord_5646924 prefixEnd_5646924 966528743803256539193425 := by
  unfold tailWord_5646924
  simp only [CollatzResearch.WordTrace]
  refine ⟨102980119297083120341541913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137306825729444160455389217 102980119297083120341541913)
  ·
    refine ⟨77235089472812340256156435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102980119297083120341541913 77235089472812340256156435)
    ·
      refine ⟨115852634209218510384234653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77235089472812340256156435 115852634209218510384234653)
      ·
        refine ⟨43444737828456941394087995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115852634209218510384234653 43444737828456941394087995)
        ·
          refine ⟨65167106742685412091131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43444737828456941394087995 65167106742685412091131993)
          ·
            refine ⟨48875330057014059068348995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65167106742685412091131993 48875330057014059068348995)
            ·
              refine ⟨73312995085521088602523493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48875330057014059068348995 73312995085521088602523493)
              ·
                refine ⟨13746186578535204112973155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73312995085521088602523493 13746186578535204112973155)
                ·
                  refine ⟨20619279867802806169459733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13746186578535204112973155 20619279867802806169459733)
                  ·
                    refine ⟨966528743803256539193425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20619279867802806169459733 966528743803256539193425)
                    ·
                      rfl

theorem cell23_5646924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_5646924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646924 prefixEnd_5646924 := by exact prefixLift 5646924
  have htrace : WordTrace (prefixWord ++ tailWord_5646924) baseStart_5646924 baseEnd_5646924 := by
    simpa [prefixWord, tailWord_5646924, baseEnd_5646924] using wordTrace_append hprefix tailTrace_5646924
  have hstable : (prefixWord ++ tailWord_5646924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646924).length < 2 ^ (prefixWord ++ tailWord_5646924).sum := by decide
  have hdescent : baseEnd_5646924 < baseStart_5646924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646944 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_5646944 : Nat := 118140960795 + 5646944 * 2 ^ 59
def prefixEnd_5646944 : Nat := 4983230072969 + 3 ^ 40 * 5646944 * 2
def baseEnd_5646944 : Nat := 2899596501022859539330183

theorem tailTrace_5646944 : CollatzResearch.WordTrace tailWord_5646944 prefixEnd_5646944 2899596501022859539330183 := by
  unfold tailWord_5646944
  simp only [CollatzResearch.WordTrace]
  refine ⟨102980484027046892049405943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137307312036062522732541257 102980484027046892049405943)
  ·
    refine ⟨154470726040570338074108915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102980484027046892049405943 154470726040570338074108915)
    ·
      refine ⟨231706089060855507111163373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154470726040570338074108915 231706089060855507111163373)
      ·
        refine ⟨86889783397820815166686265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231706089060855507111163373 86889783397820815166686265)
        ·
          refine ⟨65167337548365611375014699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86889783397820815166686265 65167337548365611375014699)
          ·
            refine ⟨97751006322548417062522049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65167337548365611375014699 97751006322548417062522049)
            ·
              refine ⟨73313254741911312796891537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97751006322548417062522049 73313254741911312796891537)
              ·
                refine ⟨54984941056433484597668653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73313254741911312796891537 54984941056433484597668653)
                ·
                  refine ⟨20619352896162556724125745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54984941056433484597668653 20619352896162556724125745)
                  ·
                    refine ⟨15464514672121917543094309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20619352896162556724125745 15464514672121917543094309)
                    ·
                      refine ⟨2899596501022859539330183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15464514672121917543094309 2899596501022859539330183)
                      ·
                        rfl

theorem cell23_5646944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_5646944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646944 prefixEnd_5646944 := by exact prefixLift 5646944
  have htrace : WordTrace (prefixWord ++ tailWord_5646944) baseStart_5646944 baseEnd_5646944 := by
    simpa [prefixWord, tailWord_5646944, baseEnd_5646944] using wordTrace_append hprefix tailTrace_5646944
  have hstable : (prefixWord ++ tailWord_5646944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646944).length < 2 ^ (prefixWord ++ tailWord_5646944).sum := by decide
  have hdescent : baseEnd_5646944 < baseStart_5646944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646954 : List Nat := [3, 1, 3, 2, 1, 1, 2, 10]
def baseStart_5646954 : Nat := 118140960795 + 5646954 * 2 ^ 59
def prefixEnd_5646954 : Nat := 4983230072969 + 3 ^ 40 * 5646954 * 2
def baseEnd_5646954 : Nat := 107392653178866833340931

theorem tailTrace_5646954 : CollatzResearch.WordTrace tailWord_5646954 prefixEnd_5646954 107392653178866833340931 := by
  unfold tailWord_5646954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51490333196014388951668979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137307555189371703871117277 51490333196014388951668979)
  ·
    refine ⟨77235499794021583427503469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51490333196014388951668979 77235499794021583427503469)
    ·
      refine ⟨28963312422758093785313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77235499794021583427503469 28963312422758093785313801)
      ·
        refine ⟨21722484317068570338985351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28963312422758093785313801 21722484317068570338985351)
        ·
          refine ⟨32583726475602855508478027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21722484317068570338985351 32583726475602855508478027)
          ·
            refine ⟨48875589713404283262717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32583726475602855508478027 48875589713404283262717041)
            ·
              refine ⟨36656692285053212447037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48875589713404283262717041 36656692285053212447037781)
              ·
                refine ⟨107392653178866833340931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36656692285053212447037781 107392653178866833340931)
                ·
                  rfl

theorem cell23_5646954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_5646954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646954 prefixEnd_5646954 := by exact prefixLift 5646954
  have htrace : WordTrace (prefixWord ++ tailWord_5646954) baseStart_5646954 baseEnd_5646954 := by
    simpa [prefixWord, tailWord_5646954, baseEnd_5646954] using wordTrace_append hprefix tailTrace_5646954
  have hstable : (prefixWord ++ tailWord_5646954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646954).length < 2 ^ (prefixWord ++ tailWord_5646954).sum := by decide
  have hdescent : baseEnd_5646954 < baseStart_5646954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646958 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_5646958 : Nat := 118140960795 + 5646958 * 2 ^ 59
def prefixEnd_5646958 : Nat := 4983230072969 + 3 ^ 40 * 5646958 * 2
def baseEnd_5646958 : Nat := 966534563250674161518373

theorem tailTrace_5646958 : CollatzResearch.WordTrace tailWord_5646958 prefixEnd_5646958 966534563250674161518373 := by
  unfold tailWord_5646958
  simp only [CollatzResearch.WordTrace]
  refine ⟨25745184834505383061227691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137307652450695376326547685 25745184834505383061227691)
  ·
    refine ⟨38617777251758074591841537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25745184834505383061227691 38617777251758074591841537)
    ·
      refine ⟨28963332938818555943881153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38617777251758074591841537 28963332938818555943881153)
      ·
        refine ⟨21722499704113916957910865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28963332938818555943881153 21722499704113916957910865)
        ·
          refine ⟨16291874778085437718433149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21722499704113916957910865 16291874778085437718433149)
          ·
            refine ⟨6109453041782039144412431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16291874778085437718433149 6109453041782039144412431)
            ·
              refine ⟨9164179562673058716618647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109453041782039144412431 9164179562673058716618647)
              ·
                refine ⟨13746269344009588074927971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9164179562673058716618647 13746269344009588074927971)
                ·
                  refine ⟨20619404016014382112391957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13746269344009588074927971 20619404016014382112391957)
                  ·
                    refine ⟨966534563250674161518373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20619404016014382112391957 966534563250674161518373)
                    ·
                      rfl

theorem cell23_5646958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_5646958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646958 prefixEnd_5646958 := by exact prefixLift 5646958
  have htrace : WordTrace (prefixWord ++ tailWord_5646958) baseStart_5646958 baseEnd_5646958 := by
    simpa [prefixWord, tailWord_5646958, baseEnd_5646958] using wordTrace_append hprefix tailTrace_5646958
  have hstable : (prefixWord ++ tailWord_5646958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646958).length < 2 ^ (prefixWord ++ tailWord_5646958).sum := by decide
  have hdescent : baseEnd_5646958 < baseStart_5646958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5646965 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5646965 : Nat := 118140960795 + 5646965 * 2 ^ 59
def prefixEnd_5646965 : Nat := 4983230072969 + 3 ^ 40 * 5646965 * 2
def baseEnd_5646965 : Nat := 2899607284116603957167587

theorem tailTrace_5646965 : CollatzResearch.WordTrace tailWord_5646965 prefixEnd_5646965 2899607284116603957167587 := by
  unfold tailWord_5646965
  simp only [CollatzResearch.WordTrace]
  refine ⟨205961733987017704685326349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137307822658011803123550899 205961733987017704685326349)
  ·
    refine ⟨77235650245131639256997381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205961733987017704685326349 77235650245131639256997381)
    ·
      refine ⟨14481684420962182360687009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77235650245131639256997381 14481684420962182360687009)
      ·
        refine ⟨10861263315721636770515257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14481684420962182360687009 10861263315721636770515257)
        ·
          refine ⟨8145947486791227577886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10861263315721636770515257 8145947486791227577886443)
          ·
            refine ⟨12218921230186841366829665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8145947486791227577886443 12218921230186841366829665)
            ·
              refine ⟨9164190922640131025122249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12218921230186841366829665 9164190922640131025122249)
              ·
                refine ⟨6873143191980098268841687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9164190922640131025122249 6873143191980098268841687)
                ·
                  refine ⟨10309714787970147403262531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6873143191980098268841687 10309714787970147403262531)
                  ·
                    refine ⟨15464572181955221104893797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10309714787970147403262531 15464572181955221104893797)
                    ·
                      refine ⟨2899607284116603957167587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15464572181955221104893797 2899607284116603957167587)
                      ·
                        rfl

theorem cell23_5646965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5646965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5646965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5646965 prefixEnd_5646965 := by exact prefixLift 5646965
  have htrace : WordTrace (prefixWord ++ tailWord_5646965) baseStart_5646965 baseEnd_5646965 := by
    simpa [prefixWord, tailWord_5646965, baseEnd_5646965] using wordTrace_append hprefix tailTrace_5646965
  have hstable : (prefixWord ++ tailWord_5646965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5646965).length < 2 ^ (prefixWord ++ tailWord_5646965).sum := by decide
  have hdescent : baseEnd_5646965 < baseStart_5646965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5646965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647068 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5647068 : Nat := 118140960795 + 5647068 * 2 ^ 59
def prefixEnd_5647068 : Nat := 4983230072969 + 3 ^ 40 * 5647068 * 2
def baseEnd_5647068 : Nat := 2899660172624017054179613

theorem tailTrace_5647068 : CollatzResearch.WordTrace tailWord_5647068 prefixEnd_5647068 2899660172624017054179613 := by
  unfold tailWord_5647068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102982745352822276638162929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137310327137096368850883905 102982745352822276638162929)
  ·
    refine ⟨77237059014616707478622197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102982745352822276638162929 77237059014616707478622197)
    ·
      refine ⟨7240974282620316326120831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77237059014616707478622197 7240974282620316326120831)
      ·
        refine ⟨10861461423930474489181247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7240974282620316326120831 10861461423930474489181247)
        ·
          refine ⟨16292192135895711733771871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861461423930474489181247 16292192135895711733771871)
          ·
            refine ⟨24438288203843567600657807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16292192135895711733771871 24438288203843567600657807)
            ·
              refine ⟨36657432305765351400986711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24438288203843567600657807 36657432305765351400986711)
              ·
                refine ⟨54986148458648027101480067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36657432305765351400986711 54986148458648027101480067)
                ·
                  refine ⟨82479222687972040652220101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54986148458648027101480067 82479222687972040652220101)
                  ·
                    refine ⟨15464854253994757622291269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82479222687972040652220101 15464854253994757622291269)
                    ·
                      refine ⟨2899660172624017054179613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15464854253994757622291269 2899660172624017054179613)
                      ·
                        rfl

theorem cell23_5647068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5647068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647068 prefixEnd_5647068 := by exact prefixLift 5647068
  have htrace : WordTrace (prefixWord ++ tailWord_5647068) baseStart_5647068 baseEnd_5647068 := by
    simpa [prefixWord, tailWord_5647068, baseEnd_5647068] using wordTrace_append hprefix tailTrace_5647068
  have hstable : (prefixWord ++ tailWord_5647068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647068).length < 2 ^ (prefixWord ++ tailWord_5647068).sum := by decide
  have hdescent : baseEnd_5647068 < baseStart_5647068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647071 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_5647071 : Nat := 118140960795 + 5647071 * 2 ^ 59
def prefixEnd_5647071 : Nat := 4983230072969 + 3 ^ 40 * 5647071 * 2
def baseEnd_5647071 : Nat := 2899661713065980542442099

theorem tailTrace_5647071 : CollatzResearch.WordTrace tailWord_5647071 prefixEnd_5647071 2899661713065980542442099 := by
  unfold tailWord_5647071
  simp only [CollatzResearch.WordTrace]
  refine ⟨205965600124633684788685067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137310400083089123192456711 205965600124633684788685067)
  ·
    refine ⟨308948400186950527183027601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205965600124633684788685067 308948400186950527183027601)
    ·
      refine ⟨231711300140212895387270701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308948400186950527183027601 231711300140212895387270701)
      ·
        refine ⟨86891737552579835770226513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231711300140212895387270701 86891737552579835770226513)
        ·
          refine ⟨65168803164434876827669885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86891737552579835770226513 65168803164434876827669885)
          ·
            refine ⟨24438301186663078810376207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65168803164434876827669885 24438301186663078810376207)
            ·
              refine ⟨36657451779994618215564311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24438301186663078810376207 36657451779994618215564311)
              ·
                refine ⟨54986177669991927323346467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36657451779994618215564311 54986177669991927323346467)
                ·
                  refine ⟨82479266504987890985019701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54986177669991927323346467 82479266504987890985019701)
                  ·
                    refine ⟨7732431234842614779845597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82479266504987890985019701 7732431234842614779845597)
                    ·
                      refine ⟨2899661713065980542442099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732431234842614779845597 2899661713065980542442099)
                      ·
                        rfl

theorem cell23_5647071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_5647071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647071 prefixEnd_5647071 := by exact prefixLift 5647071
  have htrace : WordTrace (prefixWord ++ tailWord_5647071) baseStart_5647071 baseEnd_5647071 := by
    simpa [prefixWord, tailWord_5647071, baseEnd_5647071] using wordTrace_append hprefix tailTrace_5647071
  have hstable : (prefixWord ++ tailWord_5647071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647071).length < 2 ^ (prefixWord ++ tailWord_5647071).sum := by decide
  have hdescent : baseEnd_5647071 < baseStart_5647071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647093 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5647093 : Nat := 118140960795 + 5647093 * 2 ^ 59
def prefixEnd_5647093 : Nat := 4983230072969 + 3 ^ 40 * 5647093 * 2
def baseEnd_5647093 : Nat := 2899673009640379456366999

theorem tailTrace_5647093 : CollatzResearch.WordTrace tailWord_5647093 prefixEnd_5647093 2899673009640379456366999 := by
  unfold tailWord_5647093
  simp only [CollatzResearch.WordTrace]
  refine ⟨205966402530553982545985933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137310935020369321697323955 205966402530553982545985933)
  ·
    refine ⟨77237400948957743454744725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205966402530553982545985933 77237400948957743454744725)
    ·
      refine ⟨3620503169482394224441159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77237400948957743454744725 3620503169482394224441159)
      ·
        refine ⟨5430754754223591336661739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620503169482394224441159 5430754754223591336661739)
        ·
          refine ⟨8146132131335387004992609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430754754223591336661739 8146132131335387004992609)
          ·
            refine ⟨6109599098501540253744457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8146132131335387004992609 6109599098501540253744457)
            ·
              refine ⟨4582199323876155190308343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109599098501540253744457 4582199323876155190308343)
              ·
                refine ⟨6873298985814232785462515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582199323876155190308343 6873298985814232785462515)
                ·
                  refine ⟨10309948478721349178193773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6873298985814232785462515 10309948478721349178193773)
                  ·
                    refine ⟨3866230679520505941822665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10309948478721349178193773 3866230679520505941822665)
                    ·
                      refine ⟨2899673009640379456366999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866230679520505941822665 2899673009640379456366999)
                      ·
                        rfl

theorem cell23_5647093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5647093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647093 prefixEnd_5647093 := by exact prefixLift 5647093
  have htrace : WordTrace (prefixWord ++ tailWord_5647093) baseStart_5647093 baseEnd_5647093 := by
    simpa [prefixWord, tailWord_5647093, baseEnd_5647093] using wordTrace_append hprefix tailTrace_5647093
  have hstable : (prefixWord ++ tailWord_5647093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647093).length < 2 ^ (prefixWord ++ tailWord_5647093).sum := by decide
  have hdescent : baseEnd_5647093 < baseStart_5647093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647141 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_5647141 : Nat := 118140960795 + 5647141 * 2 ^ 59
def prefixEnd_5647141 : Nat := 4983230072969 + 3 ^ 40 * 5647141 * 2
def baseEnd_5647141 : Nat := 2899697656711795268566777

theorem tailTrace_5647141 : CollatzResearch.WordTrace tailWord_5647141 prefixEnd_5647141 2899697656711795268566777 := by
  unfold tailWord_5647141
  simp only [CollatzResearch.WordTrace]
  refine ⟨205968153234380086743733277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137312102156253391162488851 205968153234380086743733277)
  ·
    refine ⟨77238057462892532528899979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205968153234380086743733277 77238057462892532528899979)
    ·
      refine ⟨115857086194338798793349969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77238057462892532528899979 115857086194338798793349969)
      ·
        refine ⟨86892814645754099095012477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115857086194338798793349969 86892814645754099095012477)
        ·
          refine ⟨32584805492157787160629679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86892814645754099095012477 32584805492157787160629679)
          ·
            refine ⟨48877208238236680740944519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32584805492157787160629679 48877208238236680740944519)
            ·
              refine ⟨73315812357355021111416779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48877208238236680740944519 73315812357355021111416779)
              ·
                refine ⟨109973718536032531667125169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73315812357355021111416779 109973718536032531667125169)
                ·
                  refine ⟨82480288902024398750343877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109973718536032531667125169 82480288902024398750343877)
                  ·
                    refine ⟨15465054169129574765689477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82480288902024398750343877 15465054169129574765689477)
                    ·
                      refine ⟨2899697656711795268566777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15465054169129574765689477 2899697656711795268566777)
                      ·
                        rfl

theorem cell23_5647141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_5647141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647141 prefixEnd_5647141 := by exact prefixLift 5647141
  have htrace : WordTrace (prefixWord ++ tailWord_5647141) baseStart_5647141 baseEnd_5647141 := by
    simpa [prefixWord, tailWord_5647141, baseEnd_5647141] using wordTrace_append hprefix tailTrace_5647141
  have hstable : (prefixWord ++ tailWord_5647141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647141).length < 2 ^ (prefixWord ++ tailWord_5647141).sum := by decide
  have hdescent : baseEnd_5647141 < baseStart_5647141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647148 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_5647148 : Nat := 118140960795 + 5647148 * 2 ^ 59
def prefixEnd_5647148 : Nat := 4983230072969 + 3 ^ 40 * 5647148 * 2
def baseEnd_5647148 : Nat := 2899701251076376741179245

theorem tailTrace_5647148 : CollatzResearch.WordTrace tailWord_5647148 prefixEnd_5647148 2899701251076376741179245 := by
  unfold tailWord_5647148
  simp only [CollatzResearch.WordTrace]
  refine ⟨102984204272677363469619049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137312272363569817959492065 102984204272677363469619049)
  ·
    refine ⟨77238153204508022602214287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102984204272677363469619049 77238153204508022602214287)
    ·
      refine ⟨115857229806762033903321431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77238153204508022602214287 115857229806762033903321431)
      ·
        refine ⟨173785844710143050854982147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115857229806762033903321431 173785844710143050854982147)
        ·
          refine ⟨260678767065214576282473221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173785844710143050854982147 260678767065214576282473221)
          ·
            refine ⟨48877268824727733052963729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260678767065214576282473221 48877268824727733052963729)
            ·
              refine ⟨36657951618545799789722797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48877268824727733052963729 36657951618545799789722797)
              ·
                refine ⟨13746731856954674921146049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36657951618545799789722797 13746731856954674921146049)
                ·
                  refine ⟨10310048892716006190859537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13746731856954674921146049 10310048892716006190859537)
                  ·
                    refine ⟨7732536669537004643144653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10310048892716006190859537 7732536669537004643144653)
                    ·
                      refine ⟨2899701251076376741179245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732536669537004643144653 2899701251076376741179245)
                      ·
                        rfl

theorem cell23_5647148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_5647148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647148 prefixEnd_5647148 := by exact prefixLift 5647148
  have htrace : WordTrace (prefixWord ++ tailWord_5647148) baseStart_5647148 baseEnd_5647148 := by
    simpa [prefixWord, tailWord_5647148, baseEnd_5647148] using wordTrace_append hprefix tailTrace_5647148
  have hstable : (prefixWord ++ tailWord_5647148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647148).length < 2 ^ (prefixWord ++ tailWord_5647148).sum := by decide
  have hdescent : baseEnd_5647148 < baseStart_5647148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647205 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_5647205 : Nat := 118140960795 + 5647205 * 2 ^ 59
def prefixEnd_5647205 : Nat := 4983230072969 + 3 ^ 40 * 5647205 * 2
def baseEnd_5647205 : Nat := 2899730519473683018166483

theorem tailTrace_5647205 : CollatzResearch.WordTrace tailWord_5647205 prefixEnd_5647205 2899730519473683018166483 := by
  unfold tailWord_5647205
  simp only [CollatzResearch.WordTrace]
  refine ⟨205970487506148225674063069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137313658337432150449375379 205970487506148225674063069)
  ·
    refine ⟨77238932814805584627773651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205970487506148225674063069 77238932814805584627773651)
    ·
      refine ⟨115858399222208376941660477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77238932814805584627773651 115858399222208376941660477)
      ·
        refine ⟨43446899708328141353122679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115858399222208376941660477 43446899708328141353122679)
        ·
          refine ⟨65170349562492212029684019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43446899708328141353122679 65170349562492212029684019)
          ·
            refine ⟨97755524343738318044526029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65170349562492212029684019 97755524343738318044526029)
            ·
              refine ⟨36658321628901869266697261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97755524343738318044526029 36658321628901869266697261)
              ·
                refine ⟨13746870610838200975011473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36658321628901869266697261 13746870610838200975011473)
                ·
                  refine ⟨10310152958128650731258605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13746870610838200975011473 10310152958128650731258605)
                  ·
                    refine ⟨3866307359298244024221977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10310152958128650731258605 3866307359298244024221977)
                    ·
                      refine ⟨2899730519473683018166483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866307359298244024221977 2899730519473683018166483)
                      ·
                        rfl

theorem cell23_5647205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_5647205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647205 prefixEnd_5647205 := by exact prefixLift 5647205
  have htrace : WordTrace (prefixWord ++ tailWord_5647205) baseStart_5647205 baseEnd_5647205 := by
    simpa [prefixWord, tailWord_5647205, baseEnd_5647205] using wordTrace_append hprefix tailTrace_5647205
  have hstable : (prefixWord ++ tailWord_5647205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647205).length < 2 ^ (prefixWord ++ tailWord_5647205).sum := by decide
  have hdescent : baseEnd_5647205 < baseStart_5647205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647211 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 6]
def baseStart_5647211 : Nat := 118140960795 + 5647211 * 2 ^ 59
def prefixEnd_5647211 : Nat := 4983230072969 + 3 ^ 40 * 5647211 * 2
def baseEnd_5647211 : Nat := 966577866785869998230485

theorem tailTrace_5647211 : CollatzResearch.WordTrace tailWord_5647211 prefixEnd_5647211 966577866785869998230485 := by
  unfold tailWord_5647211
  simp only [CollatzResearch.WordTrace]
  refine ⟨205970706344126488698781487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137313804229417659132520991 205970706344126488698781487)
  ·
    refine ⟨308956059516189733048172231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205970706344126488698781487 308956059516189733048172231)
    ·
      refine ⟨463434089274284599572258347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308956059516189733048172231 463434089274284599572258347)
      ·
        refine ⟨695151133911426899358387521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463434089274284599572258347 695151133911426899358387521)
        ·
          refine ⟨521363350433570174518790641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695151133911426899358387521 521363350433570174518790641)
          ·
            refine ⟨391022512825177630889092981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521363350433570174518790641 391022512825177630889092981)
            ·
              refine ⟨36658360577360402895852467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391022512825177630889092981 36658360577360402895852467)
              ·
                refine ⟨54987540866040604343778701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36658360577360402895852467 54987540866040604343778701)
                ·
                  refine ⟨20620327824765226628917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54987540866040604343778701 20620327824765226628917013)
                  ·
                    refine ⟨966577866785869998230485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20620327824765226628917013 966577866785869998230485)
                    ·
                      rfl

theorem cell23_5647211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 6].length) (baseStart_5647211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647211 prefixEnd_5647211 := by exact prefixLift 5647211
  have htrace : WordTrace (prefixWord ++ tailWord_5647211) baseStart_5647211 baseEnd_5647211 := by
    simpa [prefixWord, tailWord_5647211, baseEnd_5647211] using wordTrace_append hprefix tailTrace_5647211
  have hstable : (prefixWord ++ tailWord_5647211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647211).length < 2 ^ (prefixWord ++ tailWord_5647211).sum := by decide
  have hdescent : baseEnd_5647211 < baseStart_5647211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647212 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_5647212 : Nat := 118140960795 + 5647212 * 2 ^ 59
def prefixEnd_5647212 : Nat := 4983230072969 + 3 ^ 40 * 5647212 * 2
def baseEnd_5647212 : Nat := 2899734113838264490778951

theorem tailTrace_5647212 : CollatzResearch.WordTrace tailWord_5647212 prefixEnd_5647212 2899734113838264490778951 := by
  unfold tailWord_5647212
  simp only [CollatzResearch.WordTrace]
  refine ⟨102985371408561432934783945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137313828544748577246378593 102985371408561432934783945)
  ·
    refine ⟨77239028556421074701087959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102985371408561432934783945 77239028556421074701087959)
    ·
      refine ⟨115858542834631612051631939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77239028556421074701087959 115858542834631612051631939)
      ·
        refine ⟨173787814251947418077447909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115858542834631612051631939 173787814251947418077447909)
        ·
          refine ⟨32585215172240140889521483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173787814251947418077447909 32585215172240140889521483)
          ·
            refine ⟨48877822758360211334282225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32585215172240140889521483 48877822758360211334282225)
            ·
              refine ⟨36658367068770158500711669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48877822758360211334282225 36658367068770158500711669)
              ·
                refine ⟨3436721912697202359441719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36658367068770158500711669 3436721912697202359441719)
                ·
                  refine ⟨5155082869045803539162579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436721912697202359441719 5155082869045803539162579)
                  ·
                    refine ⟨7732624303568705308743869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155082869045803539162579 7732624303568705308743869)
                    ·
                      refine ⟨2899734113838264490778951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732624303568705308743869 2899734113838264490778951)
                      ·
                        rfl

theorem cell23_5647212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_5647212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647212 prefixEnd_5647212 := by exact prefixLift 5647212
  have htrace : WordTrace (prefixWord ++ tailWord_5647212) baseStart_5647212 baseEnd_5647212 := by
    simpa [prefixWord, tailWord_5647212, baseEnd_5647212] using wordTrace_append hprefix tailTrace_5647212
  have hstable : (prefixWord ++ tailWord_5647212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647212).length < 2 ^ (prefixWord ++ tailWord_5647212).sum := by decide
  have hdescent : baseEnd_5647212 < baseStart_5647212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647228 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_5647228 : Nat := 118140960795 + 5647228 * 2 ^ 59
def prefixEnd_5647228 : Nat := 4983230072969 + 3 ^ 40 * 5647228 * 2
def baseEnd_5647228 : Nat := 966580776509578809392959

theorem tailTrace_5647228 : CollatzResearch.WordTrace tailWord_5647228 prefixEnd_5647228 966580776509578809392959 := by
  unfold tailWord_5647228
  simp only [CollatzResearch.WordTrace]
  refine ⟨102985663192532450301075169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137314217590043267068100225 102985663192532450301075169)
  ·
    refine ⟨77239247394399337725806377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102985663192532450301075169 77239247394399337725806377)
    ·
      refine ⟨57929435545799503294354783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77239247394399337725806377 57929435545799503294354783)
      ·
        refine ⟨86894153318699254941532175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57929435545799503294354783 86894153318699254941532175)
        ·
          refine ⟨130341229978048882412298263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86894153318699254941532175 130341229978048882412298263)
          ·
            refine ⟨195511844967073323618447395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130341229978048882412298263 195511844967073323618447395)
            ·
              refine ⟨293267767450609985427671093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195511844967073323618447395 293267767450609985427671093)
              ·
                refine ⟨27493853198494686133844165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 293267767450609985427671093 27493853198494686133844165)
                ·
                  refine ⟨5155097474717753650095781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27493853198494686133844165 5155097474717753650095781)
                  ·
                    refine ⟨966580776509578809392959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155097474717753650095781 966580776509578809392959)
                    ·
                      rfl

theorem cell23_5647228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_5647228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647228 prefixEnd_5647228 := by exact prefixLift 5647228
  have htrace : WordTrace (prefixWord ++ tailWord_5647228) baseStart_5647228 baseEnd_5647228 := by
    simpa [prefixWord, tailWord_5647228, baseEnd_5647228] using wordTrace_append hprefix tailTrace_5647228
  have hstable : (prefixWord ++ tailWord_5647228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647228).length < 2 ^ (prefixWord ++ tailWord_5647228).sum := by decide
  have hdescent : baseEnd_5647228 < baseStart_5647228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647229 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_5647229 : Nat := 118140960795 + 5647229 * 2 ^ 59
def prefixEnd_5647229 : Nat := 4983230072969 + 3 ^ 40 * 5647229 * 2
def baseEnd_5647229 : Nat := 2899742843009390924266373

theorem tailTrace_5647229 : CollatzResearch.WordTrace tailWord_5647229 prefixEnd_5647229 2899742843009390924266373 := by
  unfold tailWord_5647229
  simp only [CollatzResearch.WordTrace]
  refine ⟨205971362858061277772936741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137314241905374185181957827 205971362858061277772936741)
  ·
    refine ⟨38619630535886489582425639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205971362858061277772936741 38619630535886489582425639)
    ·
      refine ⟨57929445803829734373638459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38619630535886489582425639 57929445803829734373638459)
      ·
        refine ⟨86894168705744601560457689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57929445803829734373638459 86894168705744601560457689)
        ·
          refine ⟨65170626529308451170343267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86894168705744601560457689 65170626529308451170343267)
          ·
            refine ⟨97755939793962676755514901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65170626529308451170343267 97755939793962676755514901)
            ·
              refine ⟨4582309677842000472914761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97755939793962676755514901 4582309677842000472914761)
              ·
                refine ⟨3436732258381500354686071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4582309677842000472914761 3436732258381500354686071)
                ·
                  refine ⟨5155098387572250532029107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436732258381500354686071 5155098387572250532029107)
                  ·
                    refine ⟨7732647581358375798043661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155098387572250532029107 7732647581358375798043661)
                    ·
                      refine ⟨2899742843009390924266373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732647581358375798043661 2899742843009390924266373)
                      ·
                        rfl

theorem cell23_5647229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_5647229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647229 prefixEnd_5647229 := by exact prefixLift 5647229
  have htrace : WordTrace (prefixWord ++ tailWord_5647229) baseStart_5647229 baseEnd_5647229 := by
    simpa [prefixWord, tailWord_5647229, baseEnd_5647229] using wordTrace_append hprefix tailTrace_5647229
  have hstable : (prefixWord ++ tailWord_5647229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647229).length < 2 ^ (prefixWord ++ tailWord_5647229).sum := by decide
  have hdescent : baseEnd_5647229 < baseStart_5647229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647231 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_5647231 : Nat := 118140960795 + 5647231 * 2 ^ 59
def prefixEnd_5647231 : Nat := 4983230072969 + 3 ^ 40 * 5647231 * 2
def baseEnd_5647231 : Nat := 2899743869970699916441363

theorem tailTrace_5647231 : CollatzResearch.WordTrace tailWord_5647231 prefixEnd_5647231 2899743869970699916441363 := by
  unfold tailWord_5647231
  simp only [CollatzResearch.WordTrace]
  refine ⟨205971435804054032114509547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137314290536036021409673031 205971435804054032114509547)
  ·
    refine ⟨308957153706081048171764321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205971435804054032114509547 308957153706081048171764321)
    ·
      refine ⟨231717865279560786128823241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308957153706081048171764321 231717865279560786128823241)
      ·
        refine ⟨173788398959670589596617431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231717865279560786128823241 173788398959670589596617431)
        ·
          refine ⟨260682598439505884394926147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173788398959670589596617431 260682598439505884394926147)
          ·
            refine ⟨391023897659258826592389221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260682598439505884394926147 391023897659258826592389221)
            ·
              refine ⟨73316980811111029986072979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 391023897659258826592389221 73316980811111029986072979)
              ·
                refine ⟨109975471216666544979109469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73316980811111029986072979 109975471216666544979109469)
                ·
                  refine ⟨41240801706249954367166051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109975471216666544979109469 41240801706249954367166051)
                  ·
                    refine ⟨61861202559374931550749077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41240801706249954367166051 61861202559374931550749077)
                    ·
                      refine ⟨2899743869970699916441363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61861202559374931550749077 2899743869970699916441363)
                      ·
                        rfl

theorem cell23_5647231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_5647231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647231 prefixEnd_5647231 := by exact prefixLift 5647231
  have htrace : WordTrace (prefixWord ++ tailWord_5647231) baseStart_5647231 baseEnd_5647231 := by
    simpa [prefixWord, tailWord_5647231, baseEnd_5647231] using wordTrace_append hprefix tailTrace_5647231
  have hstable : (prefixWord ++ tailWord_5647231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647231).length < 2 ^ (prefixWord ++ tailWord_5647231).sum := by decide
  have hdescent : baseEnd_5647231 < baseStart_5647231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647255 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 3]
def baseStart_5647255 : Nat := 118140960795 + 5647255 * 2 ^ 59
def prefixEnd_5647255 : Nat := 4983230072969 + 3 ^ 40 * 5647255 * 2
def baseEnd_5647255 : Nat := 2899756193506407822541253

theorem tailTrace_5647255 : CollatzResearch.WordTrace tailWord_5647255 prefixEnd_5647255 2899756193506407822541253 := by
  unfold tailWord_5647255
  simp only [CollatzResearch.WordTrace]
  refine ⟨205972311155967084213383219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137314874103978056142255479 205972311155967084213383219)
  ·
    refine ⟨308958466733950626320074829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205972311155967084213383219 308958466733950626320074829)
    ·
      refine ⟨115859425025231484870028061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308958466733950626320074829 115859425025231484870028061)
      ·
        refine ⟨43447284384461806826260523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115859425025231484870028061 43447284384461806826260523)
        ·
          refine ⟨65170926576692710239390785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43447284384461806826260523 65170926576692710239390785)
          ·
            refine ⟨48878194932519532679543089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65170926576692710239390785 48878194932519532679543089)
            ·
              refine ⟨36658646199389649509657317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48878194932519532679543089 36658646199389649509657317)
              ·
                refine ⟨6873496162385559283060747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36658646199389649509657317 6873496162385559283060747)
                ·
                  refine ⟨10310244243578338924591121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6873496162385559283060747 10310244243578338924591121)
                  ·
                    refine ⟨7732683182683754193443341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10310244243578338924591121 7732683182683754193443341)
                    ·
                      refine ⟨2899756193506407822541253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732683182683754193443341 2899756193506407822541253)
                      ·
                        rfl

theorem cell23_5647255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_5647255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647255 prefixEnd_5647255 := by exact prefixLift 5647255
  have htrace : WordTrace (prefixWord ++ tailWord_5647255) baseStart_5647255 baseEnd_5647255 := by
    simpa [prefixWord, tailWord_5647255, baseEnd_5647255] using wordTrace_append hprefix tailTrace_5647255
  have hstable : (prefixWord ++ tailWord_5647255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647255).length < 2 ^ (prefixWord ++ tailWord_5647255).sum := by decide
  have hdescent : baseEnd_5647255 < baseStart_5647255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647265 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5647265 : Nat := 118140960795 + 5647265 * 2 ^ 59
def prefixEnd_5647265 : Nat := 4983230072969 + 3 ^ 40 * 5647265 * 2
def baseEnd_5647265 : Nat := 2899761328312952783416207

theorem tailTrace_5647265 : CollatzResearch.WordTrace tailWord_5647265 prefixEnd_5647265 2899761328312952783416207 := by
  unfold tailWord_5647265
  simp only [CollatzResearch.WordTrace]
  refine ⟨205972675885930855921247249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137315117257287237280831499 205972675885930855921247249)
  ·
    refine ⟨154479506914448141940935437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205972675885930855921247249 154479506914448141940935437)
    ·
      refine ⟨57929815092918053227850789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154479506914448141940935437 57929815092918053227850789)
      ·
        refine ⟨10861840329922134980222023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57929815092918053227850789 10861840329922134980222023)
        ·
          refine ⟨16292760494883202470333035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861840329922134980222023 16292760494883202470333035)
          ·
            refine ⟨24439140742324803705499553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16292760494883202470333035 24439140742324803705499553)
            ·
              refine ⟨18329355556743602779124665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24439140742324803705499553 18329355556743602779124665)
              ·
                refine ⟨13747016667557702084343499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18329355556743602779124665 13747016667557702084343499)
                ·
                  refine ⟨20620525001336553126515249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13747016667557702084343499 20620525001336553126515249)
                  ·
                    refine ⟨15465393751002414844886437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20620525001336553126515249 15465393751002414844886437)
                    ·
                      refine ⟨2899761328312952783416207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15465393751002414844886437 2899761328312952783416207)
                      ·
                        rfl

theorem cell23_5647265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5647265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647265 prefixEnd_5647265 := by exact prefixLift 5647265
  have htrace : WordTrace (prefixWord ++ tailWord_5647265) baseStart_5647265 baseEnd_5647265 := by
    simpa [prefixWord, tailWord_5647265, baseEnd_5647265] using wordTrace_append hprefix tailTrace_5647265
  have hstable : (prefixWord ++ tailWord_5647265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647265).length < 2 ^ (prefixWord ++ tailWord_5647265).sum := by decide
  have hdescent : baseEnd_5647265 < baseStart_5647265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10]
def baseStart_5647291 : Nat := 118140960795 + 5647291 * 2 ^ 59
def prefixEnd_5647291 : Nat := 4983230072969 + 3 ^ 40 * 5647291 * 2
def baseEnd_5647291 : Nat := 2899774678809969681691087

theorem tailTrace_5647291 : CollatzResearch.WordTrace tailWord_5647291 prefixEnd_5647291 2899774678809969681691087 := by
  unfold tailWord_5647291
  simp only [CollatzResearch.WordTrace]
  refine ⟨205973624183836662361693727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137315749455891108241129151 205973624183836662361693727)
  ·
    refine ⟨308960436275754993542540591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205973624183836662361693727 308960436275754993542540591)
    ·
      refine ⟨463440654413632490313810887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308960436275754993542540591 463440654413632490313810887)
      ·
        refine ⟨695160981620448735470716331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463440654413632490313810887 695160981620448735470716331)
        ·
          refine ⟨1042741472430673103206074497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695160981620448735470716331 1042741472430673103206074497)
          ·
            refine ⟨782056104323004827404555873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042741472430673103206074497 782056104323004827404555873)
            ·
              refine ⟨586542078242253620553416905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782056104323004827404555873 586542078242253620553416905)
              ·
                refine ⟨439906558681690215415062679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586542078242253620553416905 439906558681690215415062679)
                ·
                  refine ⟨659859838022535323122594019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439906558681690215415062679 659859838022535323122594019)
                  ·
                    refine ⟨989789757033802984683891029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 659859838022535323122594019 989789757033802984683891029)
                    ·
                      refine ⟨2899774678809969681691087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 989789757033802984683891029 2899774678809969681691087)
                      ·
                        rfl

theorem cell23_5647291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_5647291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647291 prefixEnd_5647291 := by exact prefixLift 5647291
  have htrace : WordTrace (prefixWord ++ tailWord_5647291) baseStart_5647291 baseEnd_5647291 := by
    simpa [prefixWord, tailWord_5647291, baseEnd_5647291] using wordTrace_append hprefix tailTrace_5647291
  have hstable : (prefixWord ++ tailWord_5647291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647291).length < 2 ^ (prefixWord ++ tailWord_5647291).sum := by decide
  have hdescent : baseEnd_5647291 < baseStart_5647291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647295 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 3, 3, 2]
def baseStart_5647295 : Nat := 118140960795 + 5647295 * 2 ^ 59
def prefixEnd_5647295 : Nat := 4983230072969 + 3 ^ 40 * 5647295 * 2
def baseEnd_5647295 : Nat := 2899776732732587666041069

theorem tailTrace_5647295 : CollatzResearch.WordTrace tailWord_5647295 prefixEnd_5647295 2899776732732587666041069 := by
  unfold tailWord_5647295
  simp only [CollatzResearch.WordTrace]
  refine ⟨205973770075822171044839339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137315846717214780696559559 205973770075822171044839339)
  ·
    refine ⟨308960655113733256567259009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205973770075822171044839339 308960655113733256567259009)
    ·
      refine ⟨231720491335299942425444257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308960655113733256567259009 231720491335299942425444257)
      ·
        refine ⟨173790368501474956819083193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231720491335299942425444257 173790368501474956819083193)
        ·
          refine ⟨130342776376106217614312395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173790368501474956819083193 130342776376106217614312395)
          ·
            refine ⟨195514164564159326421468593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130342776376106217614312395 195514164564159326421468593)
            ·
              refine ⟨146635623423119494816101445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195514164564159326421468593 146635623423119494816101445)
              ·
                refine ⟨27494179391834905278019021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146635623423119494816101445 27494179391834905278019021)
                ·
                  refine ⟨10310317271938089479257133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27494179391834905278019021 10310317271938089479257133)
                  ·
                    refine ⟨3866368976976783554721425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10310317271938089479257133 3866368976976783554721425)
                    ·
                      refine ⟨2899776732732587666041069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866368976976783554721425 2899776732732587666041069)
                      ·
                        rfl

theorem cell23_5647295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_5647295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647295 prefixEnd_5647295 := by exact prefixLift 5647295
  have htrace : WordTrace (prefixWord ++ tailWord_5647295) baseStart_5647295 baseEnd_5647295 := by
    simpa [prefixWord, tailWord_5647295, baseEnd_5647295] using wordTrace_append hprefix tailTrace_5647295
  have hstable : (prefixWord ++ tailWord_5647295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647295).length < 2 ^ (prefixWord ++ tailWord_5647295).sum := by decide
  have hdescent : baseEnd_5647295 < baseStart_5647295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647309 : List Nat := [1, 6, 3, 1, 1, 1, 1, 9]
def baseStart_5647309 : Nat := 118140960795 + 5647309 * 2 ^ 59
def prefixEnd_5647309 : Nat := 4983230072969 + 3 ^ 40 * 5647309 * 2
def baseEnd_5647309 : Nat := 107399404498583355972815

theorem tailTrace_5647309 : CollatzResearch.WordTrace tailWord_5647309 prefixEnd_5647309 107399404498583355972815 := by
  unfold tailWord_5647309
  simp only [CollatzResearch.WordTrace]
  refine ⟨205974280697771451435848981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137316187131847634290565987 205974280697771451435848981)
  ·
    refine ⟨9655044407708036786055421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205974280697771451435848981 9655044407708036786055421)
    ·
      refine ⟨3620641652890513794770783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9655044407708036786055421 3620641652890513794770783)
      ·
        refine ⟨5430962479335770692156175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620641652890513794770783 5430962479335770692156175)
        ·
          refine ⟨8146443719003656038234263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430962479335770692156175 8146443719003656038234263)
          ·
            refine ⟨12219665578505484057351395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8146443719003656038234263 12219665578505484057351395)
            ·
              refine ⟨18329498367758226086027093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12219665578505484057351395 18329498367758226086027093)
              ·
                refine ⟨107399404498583355972815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18329498367758226086027093 107399404498583355972815)
                ·
                  rfl

theorem cell23_5647309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 9].length) (baseStart_5647309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647309 prefixEnd_5647309 := by exact prefixLift 5647309
  have htrace : WordTrace (prefixWord ++ tailWord_5647309) baseStart_5647309 baseEnd_5647309 := by
    simpa [prefixWord, tailWord_5647309, baseEnd_5647309] using wordTrace_append hprefix tailTrace_5647309
  have hstable : (prefixWord ++ tailWord_5647309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647309).length < 2 ^ (prefixWord ++ tailWord_5647309).sum := by decide
  have hdescent : baseEnd_5647309 < baseStart_5647309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647328 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_5647328 : Nat := 118140960795 + 5647328 * 2 ^ 59
def prefixEnd_5647328 : Nat := 4983230072969 + 3 ^ 40 * 5647328 * 2
def baseEnd_5647328 : Nat := 2899793677594186036928417

theorem tailTrace_5647328 : CollatzResearch.WordTrace tailWord_5647328 prefixEnd_5647328 2899793677594186036928417 := by
  unfold tailWord_5647328
  simp only [CollatzResearch.WordTrace]
  refine ⟨102987486842351308840395319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137316649123135078453860425 102987486842351308840395319)
  ·
    refine ⟨154481230263526963260592979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102987486842351308840395319 154481230263526963260592979)
    ·
      refine ⟨231721845395290444890889469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154481230263526963260592979 231721845395290444890889469)
      ·
        refine ⟨86895692023233916834083551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231721845395290444890889469 86895692023233916834083551)
        ·
          refine ⟨130343538034850875251125327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86895692023233916834083551 130343538034850875251125327)
          ·
            refine ⟨195515307052276312876687991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130343538034850875251125327 195515307052276312876687991)
            ·
              refine ⟨293272960578414469315031987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195515307052276312876687991 293272960578414469315031987)
              ·
                refine ⟨439909440867621703972547981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293272960578414469315031987 439909440867621703972547981)
                ·
                  refine ⟨164966040325358138989705493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439909440867621703972547981 164966040325358138989705493)
                  ·
                    refine ⟨7732783140251162765142445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164966040325358138989705493 7732783140251162765142445)
                    ·
                      refine ⟨2899793677594186036928417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732783140251162765142445 2899793677594186036928417)
                      ·
                        rfl

theorem cell23_5647328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_5647328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647328 prefixEnd_5647328 := by exact prefixLift 5647328
  have htrace : WordTrace (prefixWord ++ tailWord_5647328) baseStart_5647328 baseEnd_5647328 := by
    simpa [prefixWord, tailWord_5647328, baseEnd_5647328] using wordTrace_append hprefix tailTrace_5647328
  have hstable : (prefixWord ++ tailWord_5647328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647328).length < 2 ^ (prefixWord ++ tailWord_5647328).sum := by decide
  have hdescent : baseEnd_5647328 < baseStart_5647328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647395 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 2, 5]
def baseStart_5647395 : Nat := 118140960795 + 5647395 * 2 ^ 59
def prefixEnd_5647395 : Nat := 4983230072969 + 3 ^ 40 * 5647395 * 2
def baseEnd_5647395 : Nat := 966609360266012424930203

theorem tailTrace_5647395 : CollatzResearch.WordTrace tailWord_5647395 prefixEnd_5647395 966609360266012424930203 := by
  unfold tailWord_5647395
  simp only [CollatzResearch.WordTrace]
  refine ⟨205977417375459888123479639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137318278250306592082319759 205977417375459888123479639)
  ·
    refine ⟨308966126063189832185219459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205977417375459888123479639 308966126063189832185219459)
    ·
      refine ⟨463449189094784748277829189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308966126063189832185219459 463449189094784748277829189)
      ·
        refine ⟨86896722955272140302092973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463449189094784748277829189 86896722955272140302092973)
        ·
          refine ⟨32586271108227052613284865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86896722955272140302092973 32586271108227052613284865)
          ·
            refine ⟨24439703331170289459963649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32586271108227052613284865 24439703331170289459963649)
            ·
              refine ⟨18329777498377717094972737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24439703331170289459963649 18329777498377717094972737)
              ·
                refine ⟨13747333123783287821229553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18329777498377717094972737 13747333123783287821229553)
                ·
                  refine ⟨10310499842837465865922165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13747333123783287821229553 10310499842837465865922165)
                  ·
                    refine ⟨966609360266012424930203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10310499842837465865922165 966609360266012424930203)
                    ·
                      rfl

theorem cell23_5647395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 5].length) (baseStart_5647395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647395 prefixEnd_5647395 := by exact prefixLift 5647395
  have htrace : WordTrace (prefixWord ++ tailWord_5647395) baseStart_5647395 baseEnd_5647395 := by
    simpa [prefixWord, tailWord_5647395, baseEnd_5647395] using wordTrace_append hprefix tailTrace_5647395
  have hstable : (prefixWord ++ tailWord_5647395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647395).length < 2 ^ (prefixWord ++ tailWord_5647395).sum := by decide
  have hdescent : baseEnd_5647395 < baseStart_5647395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647399 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 5]
def baseStart_5647399 : Nat := 118140960795 + 5647399 * 2 ^ 59
def prefixEnd_5647399 : Nat := 4983230072969 + 3 ^ 40 * 5647399 * 2
def baseEnd_5647399 : Nat := 322203348302295028793399

theorem tailTrace_5647399 : CollatzResearch.WordTrace tailWord_5647399 prefixEnd_5647399 322203348302295028793399 := by
  unfold tailWord_5647399
  simp only [CollatzResearch.WordTrace]
  refine ⟨205977563267445396806625251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137318375511630264537750167 205977563267445396806625251)
  ·
    refine ⟨308966344901168095209937877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205977563267445396806625251 308966344901168095209937877)
    ·
      refine ⟨7241398708621127231482919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 308966344901168095209937877 7241398708621127231482919)
      ·
        refine ⟨10862098062931690847224379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241398708621127231482919 10862098062931690847224379)
        ·
          refine ⟨16293147094397536270836569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10862098062931690847224379 16293147094397536270836569)
          ·
            refine ⟨12219860320798152203127427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16293147094397536270836569 12219860320798152203127427)
            ·
              refine ⟨18329790481197228304691141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12219860320798152203127427 18329790481197228304691141)
              ·
                refine ⟨3436835715224480307129589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18329790481197228304691141 3436835715224480307129589)
                ·
                  refine ⟨322203348302295028793399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3436835715224480307129589 322203348302295028793399)
                  ·
                    rfl

theorem cell23_5647399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 5].length) (baseStart_5647399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647399 prefixEnd_5647399 := by exact prefixLift 5647399
  have htrace : WordTrace (prefixWord ++ tailWord_5647399) baseStart_5647399 baseEnd_5647399 := by
    simpa [prefixWord, tailWord_5647399, baseEnd_5647399] using wordTrace_append hprefix tailTrace_5647399
  have hstable : (prefixWord ++ tailWord_5647399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647399).length < 2 ^ (prefixWord ++ tailWord_5647399).sum := by decide
  have hdescent : baseEnd_5647399 < baseStart_5647399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647452 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5647452 : Nat := 118140960795 + 5647452 * 2 ^ 59
def prefixEnd_5647452 : Nat := 4983230072969 + 3 ^ 40 * 5647452 * 2
def baseEnd_5647452 : Nat := 2899857349195343551777847

theorem tailTrace_5647452 : CollatzResearch.WordTrace tailWord_5647452 prefixEnd_5647452 2899857349195343551777847 := by
  unfold tailWord_5647452
  simp only [CollatzResearch.WordTrace]
  refine ⟨102989748168126693429152305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137319664224168924572203073 102989748168126693429152305)
  ·
    refine ⟨77242311126095020071864229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102989748168126693429152305 77242311126095020071864229)
    ·
      refine ⟨14482933336142816263474543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77242311126095020071864229 14482933336142816263474543)
      ·
        refine ⟨21724400004214224395211815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14482933336142816263474543 21724400004214224395211815)
        ·
          refine ⟨32586600006321336592817723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21724400004214224395211815 32586600006321336592817723)
          ·
            refine ⟨48879900009482004889226585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32586600006321336592817723 48879900009482004889226585)
            ·
              refine ⟨36659925007111503666919939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48879900009482004889226585 36659925007111503666919939)
              ·
                refine ⟨54989887510667255500379909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36659925007111503666919939 54989887510667255500379909)
                ·
                  refine ⟨10310603908250110406321233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54989887510667255500379909 10310603908250110406321233)
                  ·
                    refine ⟨7732952931187582804740925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10310603908250110406321233 7732952931187582804740925)
                    ·
                      refine ⟨2899857349195343551777847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7732952931187582804740925 2899857349195343551777847)
                      ·
                        rfl

theorem cell23_5647452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5647452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647452 prefixEnd_5647452 := by exact prefixLift 5647452
  have htrace : WordTrace (prefixWord ++ tailWord_5647452) baseStart_5647452 baseEnd_5647452 := by
    simpa [prefixWord, tailWord_5647452, baseEnd_5647452] using wordTrace_append hprefix tailTrace_5647452
  have hstable : (prefixWord ++ tailWord_5647452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647452).length < 2 ^ (prefixWord ++ tailWord_5647452).sum := by decide
  have hdescent : baseEnd_5647452 < baseStart_5647452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647472 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 6]
def baseStart_5647472 : Nat := 118140960795 + 5647472 * 2 ^ 59
def prefixEnd_5647472 : Nat := 4983230072969 + 3 ^ 40 * 5647472 * 2
def baseEnd_5647472 : Nat := 322207513200937052614195

theorem tailTrace_5647472 : CollatzResearch.WordTrace tailWord_5647472 prefixEnd_5647472 322207513200937052614195 := by
  unfold tailWord_5647472
  simp only [CollatzResearch.WordTrace]
  refine ⟨102990112898090465137016335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137320150530787286849355113 102990112898090465137016335)
  ·
    refine ⟨154485169347135697705524503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102990112898090465137016335 154485169347135697705524503)
    ·
      refine ⟨231727754020703546558286755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154485169347135697705524503 231727754020703546558286755)
      ·
        refine ⟨347591631031055319837430133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231727754020703546558286755 347591631031055319837430133)
        ·
          refine ⟨32586715409161436234759075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 347591631031055319837430133 32586715409161436234759075)
          ·
            refine ⟨48880073113742154352138613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32586715409161436234759075 48880073113742154352138613)
            ·
              refine ⟨4582506854413326970512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48880073113742154352138613 4582506854413326970512995)
              ·
                refine ⟨6873760281619990455769493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582506854413326970512995 6873760281619990455769493)
                ·
                  refine ⟨322207513200937052614195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6873760281619990455769493 322207513200937052614195)
                  ·
                    rfl

theorem cell23_5647472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_5647472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647472 prefixEnd_5647472 := by exact prefixLift 5647472
  have htrace : WordTrace (prefixWord ++ tailWord_5647472) baseStart_5647472 baseEnd_5647472 := by
    simpa [prefixWord, tailWord_5647472, baseEnd_5647472] using wordTrace_append hprefix tailTrace_5647472
  have hstable : (prefixWord ++ tailWord_5647472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647472).length < 2 ^ (prefixWord ++ tailWord_5647472).sum := by decide
  have hdescent : baseEnd_5647472 < baseStart_5647472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647493 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_5647493 : Nat := 118140960795 + 5647493 * 2 ^ 59
def prefixEnd_5647493 : Nat := 4983230072969 + 3 ^ 40 * 5647493 * 2
def baseEnd_5647493 : Nat := 966626133967392630455053

theorem tailTrace_5647493 : CollatzResearch.WordTrace tailWord_5647493 prefixEnd_5647493 966626133967392630455053 := by
  unfold tailWord_5647493
  simp only [CollatzResearch.WordTrace]
  refine ⟨205980991729104850860547133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137320661152736567240364755 205980991729104850860547133)
  ·
    refine ⟨77242871898414319072705175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205980991729104850860547133 77242871898414319072705175)
    ·
      refine ⟨115864307847621478609057763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77242871898414319072705175 115864307847621478609057763)
      ·
        refine ⟨173796461771432217913586645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115864307847621478609057763 173796461771432217913586645)
        ·
          refine ⟨4073354572767942607349687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173796461771432217913586645 4073354572767942607349687)
          ·
            refine ⟨6110031859151913911024531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073354572767942607349687 6110031859151913911024531)
            ·
              refine ⟨9165047788727870866536797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110031859151913911024531 9165047788727870866536797)
              ·
                refine ⟨3436892920772951574951299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9165047788727870866536797 3436892920772951574951299)
                ·
                  refine ⟨5155339381159427362426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436892920772951574951299 5155339381159427362426949)
                  ·
                    refine ⟨966626133967392630455053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155339381159427362426949 966626133967392630455053)
                    ·
                      rfl

theorem cell23_5647493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_5647493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647493 prefixEnd_5647493 := by exact prefixLift 5647493
  have htrace : WordTrace (prefixWord ++ tailWord_5647493) baseStart_5647493 baseEnd_5647493 := by
    simpa [prefixWord, tailWord_5647493, baseEnd_5647493] using wordTrace_append hprefix tailTrace_5647493
  have hstable : (prefixWord ++ tailWord_5647493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647493).length < 2 ^ (prefixWord ++ tailWord_5647493).sum := by decide
  have hdescent : baseEnd_5647493 < baseStart_5647493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647516 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5647516 : Nat := 118140960795 + 5647516 * 2 ^ 59
def prefixEnd_5647516 : Nat := 4983230072969 + 3 ^ 40 * 5647516 * 2
def baseEnd_5647516 : Nat := 2899890211957231301377553

theorem tailTrace_5647516 : CollatzResearch.WordTrace tailWord_5647516 prefixEnd_5647516 2899890211957231301377553 := by
  unfold tailWord_5647516
  simp only [CollatzResearch.WordTrace]
  refine ⟨102990915304010762894317201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137321220405347683859089601 102990915304010762894317201)
  ·
    refine ⟨77243186478008072170737901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102990915304010762894317201 77243186478008072170737901)
    ·
      refine ⟨28966194929253027064026713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77243186478008072170737901 28966194929253027064026713)
      ·
        refine ⟨21724646196939770298020035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28966194929253027064026713 21724646196939770298020035)
        ·
          refine ⟨32586969295409655447030053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21724646196939770298020035 32586969295409655447030053)
          ·
            refine ⟨6110056742889310396318135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32586969295409655447030053 6110056742889310396318135)
            ·
              refine ⟨9165085114333965594477203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110056742889310396318135 9165085114333965594477203)
              ·
                refine ⟨13747627671500948391715805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165085114333965594477203 13747627671500948391715805)
                ·
                  refine ⟨5155360376812855646893427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13747627671500948391715805 5155360376812855646893427)
                  ·
                    refine ⟨7733040565219283470340141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155360376812855646893427 7733040565219283470340141)
                    ·
                      refine ⟨2899890211957231301377553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733040565219283470340141 2899890211957231301377553)
                      ·
                        rfl

theorem cell23_5647516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5647516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647516 prefixEnd_5647516 := by exact prefixLift 5647516
  have htrace : WordTrace (prefixWord ++ tailWord_5647516) baseStart_5647516 baseEnd_5647516 := by
    simpa [prefixWord, tailWord_5647516, baseEnd_5647516] using wordTrace_append hprefix tailTrace_5647516
  have hstable : (prefixWord ++ tailWord_5647516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647516).length < 2 ^ (prefixWord ++ tailWord_5647516).sum := by decide
  have hdescent : baseEnd_5647516 < baseStart_5647516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647535 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_5647535 : Nat := 118140960795 + 5647535 * 2 ^ 59
def prefixEnd_5647535 : Nat := 4983230072969 + 3 ^ 40 * 5647535 * 2
def baseEnd_5647535 : Nat := 2899899968089666727039965

theorem tailTrace_5647535 : CollatzResearch.WordTrace tailWord_5647535 prefixEnd_5647535 2899899968089666727039965 := by
  unfold tailWord_5647535
  simp only [CollatzResearch.WordTrace]
  refine ⟨205982523594952692033576059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137321682396635128022384039 205982523594952692033576059)
  ·
    refine ⟨308973785392429038050364089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205982523594952692033576059 308973785392429038050364089)
    ·
      refine ⟨231730339044321778537773067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308973785392429038050364089 231730339044321778537773067)
      ·
        refine ⟨347595508566482667806659601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231730339044321778537773067 347595508566482667806659601)
        ·
          refine ⟨260696631424862000854994701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347595508566482667806659601 260696631424862000854994701)
          ·
            refine ⟨97761236784323250320623013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260696631424862000854994701 97761236784323250320623013)
            ·
              refine ⟨18330231897060609435116815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97761236784323250320623013 18330231897060609435116815)
              ·
                refine ⟨27495347845590914152675223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18330231897060609435116815 27495347845590914152675223)
                ·
                  refine ⟨41243021768386371229012835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27495347845590914152675223 41243021768386371229012835)
                  ·
                    refine ⟨61864532652579556843519253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41243021768386371229012835 61864532652579556843519253)
                    ·
                      refine ⟨2899899968089666727039965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61864532652579556843519253 2899899968089666727039965)
                      ·
                        rfl

theorem cell23_5647535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_5647535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647535 prefixEnd_5647535 := by exact prefixLift 5647535
  have htrace : WordTrace (prefixWord ++ tailWord_5647535) baseStart_5647535 baseEnd_5647535 := by
    simpa [prefixWord, tailWord_5647535, baseEnd_5647535] using wordTrace_append hprefix tailTrace_5647535
  have hstable : (prefixWord ++ tailWord_5647535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647535).length < 2 ^ (prefixWord ++ tailWord_5647535).sum := by decide
  have hdescent : baseEnd_5647535 < baseStart_5647535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647539 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 3, 2, 2]
def baseStart_5647539 : Nat := 118140960795 + 5647539 * 2 ^ 59
def prefixEnd_5647539 : Nat := 4983230072969 + 3 ^ 40 * 5647539 * 2
def baseEnd_5647539 : Nat := 2899902022012284711389947

theorem tailTrace_5647539 : CollatzResearch.WordTrace tailWord_5647539 prefixEnd_5647539 2899902022012284711389947 := by
  unfold tailWord_5647539
  simp only [CollatzResearch.WordTrace]
  refine ⟨205982669486938200716721671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137321779657958800477814447 205982669486938200716721671)
  ·
    refine ⟨308974004230407301075082507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205982669486938200716721671 308974004230407301075082507)
    ·
      refine ⟨463461006345610951612623761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308974004230407301075082507 463461006345610951612623761)
      ·
        refine ⟨347595754759208213709467821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463461006345610951612623761 347595754759208213709467821)
        ·
          refine ⟨130348408034703080141050433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347595754759208213709467821 130348408034703080141050433)
          ·
            refine ⟨97761306026027310105787825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130348408034703080141050433 97761306026027310105787825)
            ·
              refine ⟨73320979519520482579340869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97761306026027310105787825 73320979519520482579340869)
              ·
                refine ⟨13747683659910090483626413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73320979519520482579340869 13747683659910090483626413)
                ·
                  refine ⟨5155381372466283931359905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13747683659910090483626413 5155381372466283931359905)
                  ·
                    refine ⟨3866536029349712948519929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5155381372466283931359905 3866536029349712948519929)
                    ·
                      refine ⟨2899902022012284711389947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866536029349712948519929 2899902022012284711389947)
                      ·
                        rfl

theorem cell23_5647539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2, 2].length) (baseStart_5647539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647539 prefixEnd_5647539 := by exact prefixLift 5647539
  have htrace : WordTrace (prefixWord ++ tailWord_5647539) baseStart_5647539 baseEnd_5647539 := by
    simpa [prefixWord, tailWord_5647539, baseEnd_5647539] using wordTrace_append hprefix tailTrace_5647539
  have hstable : (prefixWord ++ tailWord_5647539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647539).length < 2 ^ (prefixWord ++ tailWord_5647539).sum := by decide
  have hdescent : baseEnd_5647539 < baseStart_5647539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647545 : List Nat := [1, 2, 1, 4, 1, 3, 2, 9]
def baseStart_5647545 : Nat := 118140960795 + 5647545 * 2 ^ 59
def prefixEnd_5647545 : Nat := 4983230072969 + 3 ^ 40 * 5647545 * 2
def baseEnd_5647545 : Nat := 107403892699859692144997

theorem tailTrace_5647545 : CollatzResearch.WordTrace tailWord_5647545 prefixEnd_5647545 107403892699859692144997 := by
  unfold tailWord_5647545
  simp only [CollatzResearch.WordTrace]
  refine ⟨205982888324916463741440089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137321925549944309160960059 205982888324916463741440089)
  ·
    refine ⟨154487166243687347806080067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205982888324916463741440089 154487166243687347806080067)
    ·
      refine ⟨231730749365531021709120101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154487166243687347806080067 231730749365531021709120101)
      ·
        refine ⟨43449515506037066570460019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231730749365531021709120101 43449515506037066570460019)
        ·
          refine ⟨65174273259055599855690029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43449515506037066570460019 65174273259055599855690029)
          ·
            refine ⟨24440352472145849945883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65174273259055599855690029 24440352472145849945883761)
            ·
              refine ⟨18330264354109387459412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24440352472145849945883761 18330264354109387459412821)
              ·
                refine ⟨107403892699859692144997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18330264354109387459412821 107403892699859692144997)
                ·
                  rfl

theorem cell23_5647545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 9].length) (baseStart_5647545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647545 prefixEnd_5647545 := by exact prefixLift 5647545
  have htrace : WordTrace (prefixWord ++ tailWord_5647545) baseStart_5647545 baseEnd_5647545 := by
    simpa [prefixWord, tailWord_5647545, baseEnd_5647545] using wordTrace_append hprefix tailTrace_5647545
  have hstable : (prefixWord ++ tailWord_5647545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647545).length < 2 ^ (prefixWord ++ tailWord_5647545).sum := by decide
  have hdescent : baseEnd_5647545 < baseStart_5647545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647566 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_5647566 : Nat := 118140960795 + 5647566 * 2 ^ 59
def prefixEnd_5647566 : Nat := 4983230072969 + 3 ^ 40 * 5647566 * 2
def baseEnd_5647566 : Nat := 966638628663318701917441

theorem tailTrace_5647566 : CollatzResearch.WordTrace tailWord_5647566 prefixEnd_5647566 966638628663318701917441 := by
  unfold tailWord_5647566
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747956782230048040994319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137322436171893589551969701 25747956782230048040994319)
  ·
    refine ⟨38621935173345072061491479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25747956782230048040994319 38621935173345072061491479)
    ·
      refine ⟨57932902760017608092237219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38621935173345072061491479 57932902760017608092237219)
      ·
        refine ⟨86899354140026412138355829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57932902760017608092237219 86899354140026412138355829)
        ·
          refine ⟨8146814450627476137970859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86899354140026412138355829 8146814450627476137970859)
          ·
            refine ⟨12220221675941214206956289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8146814450627476137970859 12220221675941214206956289)
            ·
              refine ⟨9165166256955910655217217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12220221675941214206956289 9165166256955910655217217)
              ·
                refine ⟨6873874692716932991412913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9165166256955910655217217 6873874692716932991412913)
                ·
                  refine ⟨5155406019537699743559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6873874692716932991412913 5155406019537699743559685)
                  ·
                    refine ⟨966638628663318701917441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155406019537699743559685 966638628663318701917441)
                    ·
                      rfl

theorem cell23_5647566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_5647566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647566 prefixEnd_5647566 := by exact prefixLift 5647566
  have htrace : WordTrace (prefixWord ++ tailWord_5647566) baseStart_5647566 baseEnd_5647566 := by
    simpa [prefixWord, tailWord_5647566, baseEnd_5647566] using wordTrace_append hprefix tailTrace_5647566
  have hstable : (prefixWord ++ tailWord_5647566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647566).length < 2 ^ (prefixWord ++ tailWord_5647566).sum := by decide
  have hdescent : baseEnd_5647566 < baseStart_5647566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647575 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 7]
def baseStart_5647575 : Nat := 118140960795 + 5647575 * 2 ^ 59
def prefixEnd_5647575 : Nat := 4983230072969 + 3 ^ 40 * 5647575 * 2
def baseEnd_5647575 : Nat := 966640169105282190179927

theorem tailTrace_5647575 : CollatzResearch.WordTrace tailWord_5647575 prefixEnd_5647575 966640169105282190179927 := by
  unfold tailWord_5647575
  simp only [CollatzResearch.WordTrace]
  refine ⟨205983982514807778865032179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137322655009871852576688119 205983982514807778865032179)
  ·
    refine ⟨308975973772211668297548269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205983982514807778865032179 308975973772211668297548269)
    ·
      refine ⟨115865990164579375611580601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 308975973772211668297548269 115865990164579375611580601)
      ·
        refine ⟨86899492623434531708685451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115865990164579375611580601 86899492623434531708685451)
        ·
          refine ⟨130349238935151797563028177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86899492623434531708685451 130349238935151797563028177)
          ·
            refine ⟨97761929201363848172271133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130349238935151797563028177 97761929201363848172271133)
            ·
              refine ⟨36660723450511443064601675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97761929201363848172271133 36660723450511443064601675)
              ·
                refine ⟨54991085175767164596902513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36660723450511443064601675 54991085175767164596902513)
                ·
                  refine ⟨41243313881825373447676885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54991085175767164596902513 41243313881825373447676885)
                  ·
                    refine ⟨966640169105282190179927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41243313881825373447676885 966640169105282190179927)
                    ·
                      rfl

theorem cell23_5647575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_5647575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647575 prefixEnd_5647575 := by exact prefixLift 5647575
  have htrace : WordTrace (prefixWord ++ tailWord_5647575) baseStart_5647575 baseEnd_5647575 := by
    simpa [prefixWord, tailWord_5647575, baseEnd_5647575] using wordTrace_append hprefix tailTrace_5647575
  have hstable : (prefixWord ++ tailWord_5647575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647575).length < 2 ^ (prefixWord ++ tailWord_5647575).sum := by decide
  have hdescent : baseEnd_5647575 < baseStart_5647575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647652 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 7]
def baseStart_5647652 : Nat := 118140960795 + 5647652 * 2 ^ 59
def prefixEnd_5647652 : Nat := 4983230072969 + 3 ^ 40 * 5647652 * 2
def baseEnd_5647652 : Nat := 322217782814026974364103

theorem tailTrace_5647652 : CollatzResearch.WordTrace tailWord_5647652 prefixEnd_5647652 322217782814026974364103 := by
  unfold tailWord_5647652
  simp only [CollatzResearch.WordTrace]
  refine ⟨102993395467764410507792605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137324527290352547343723473 102993395467764410507792605)
  ·
    refine ⟨38622523300411653940422227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102993395467764410507792605 38622523300411653940422227)
    ·
      refine ⟨57933784950617480910633341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38622523300411653940422227 57933784950617480910633341)
      ·
        refine ⟨21725169356481555341487503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57933784950617480910633341 21725169356481555341487503)
        ·
          refine ⟨32587754034722333012231255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725169356481555341487503 32587754034722333012231255)
          ·
            refine ⟨48881631052083499518346883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32587754034722333012231255 48881631052083499518346883)
            ·
              refine ⟨73322446578125249277520325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48881631052083499518346883 73322446578125249277520325)
              ·
                refine ⟨13747958733398484239535061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73322446578125249277520325 13747958733398484239535061)
                ·
                  refine ⟨322217782814026974364103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13747958733398484239535061 322217782814026974364103)
                  ·
                    rfl

theorem cell23_5647652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_5647652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647652 prefixEnd_5647652 := by exact prefixLift 5647652
  have htrace : WordTrace (prefixWord ++ tailWord_5647652) baseStart_5647652 baseEnd_5647652 := by
    simpa [prefixWord, tailWord_5647652, baseEnd_5647652] using wordTrace_append hprefix tailTrace_5647652
  have hstable : (prefixWord ++ tailWord_5647652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647652).length < 2 ^ (prefixWord ++ tailWord_5647652).sum := by decide
  have hdescent : baseEnd_5647652 < baseStart_5647652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647692 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5647692 : Nat := 118140960795 + 5647692 * 2 ^ 59
def prefixEnd_5647692 : Nat := 4983230072969 + 3 ^ 40 * 5647692 * 2
def baseEnd_5647692 : Nat := 2899980584552422612776743

theorem tailTrace_5647692 : CollatzResearch.WordTrace tailWord_5647692 prefixEnd_5647692 2899980584552422612776743 := by
  unfold tailWord_5647692
  simp only [CollatzResearch.WordTrace]
  refine ⟨102994124927691953923520665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137325499903589271898027553 102994124927691953923520665)
  ·
    refine ⟨77245593695768965442640499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102994124927691953923520665 77245593695768965442640499)
    ·
      refine ⟨115868390543653448163960749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77245593695768965442640499 115868390543653448163960749)
      ·
        refine ⟨43450646453870043061485281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115868390543653448163960749 43450646453870043061485281)
        ·
          refine ⟨32587984840402532296113961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43450646453870043061485281 32587984840402532296113961)
          ·
            refine ⟨24440988630301899222085471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32587984840402532296113961 24440988630301899222085471)
            ·
              refine ⟨36661482945452848833128207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24440988630301899222085471 36661482945452848833128207)
              ·
                refine ⟨54992224418179273249692311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36661482945452848833128207 54992224418179273249692311)
                ·
                  refine ⟨82488336627268909874538467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54992224418179273249692311 82488336627268909874538467)
                  ·
                    refine ⟨123732504940903364811807701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82488336627268909874538467 123732504940903364811807701)
                    ·
                      refine ⟨2899980584552422612776743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123732504940903364811807701 2899980584552422612776743)
                      ·
                        rfl

theorem cell23_5647692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5647692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647692 prefixEnd_5647692 := by exact prefixLift 5647692
  have htrace : WordTrace (prefixWord ++ tailWord_5647692) baseStart_5647692 baseEnd_5647692 := by
    simpa [prefixWord, tailWord_5647692, baseEnd_5647692] using wordTrace_append hprefix tailTrace_5647692
  have hstable : (prefixWord ++ tailWord_5647692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647692).length < 2 ^ (prefixWord ++ tailWord_5647692).sum := by decide
  have hdescent : baseEnd_5647692 < baseStart_5647692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647739 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3]
def baseStart_5647739 : Nat := 118140960795 + 5647739 * 2 ^ 59
def prefixEnd_5647739 : Nat := 4983230072969 + 3 ^ 40 * 5647739 * 2
def baseEnd_5647739 : Nat := 2900004718143183928889027

theorem tailTrace_5647739 : CollatzResearch.WordTrace tailWord_5647739 prefixEnd_5647739 2900004718143183928889027 := by
  unfold tailWord_5647739
  simp only [CollatzResearch.WordTrace]
  refine ⟨205989964086213634874002271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137326642724142423249334847 205989964086213634874002271)
  ·
    refine ⟨308984946129320452311003407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205989964086213634874002271 308984946129320452311003407)
    ·
      refine ⟨463477419193980678466505111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308984946129320452311003407 463477419193980678466505111)
      ·
        refine ⟨695216128790971017699757667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463477419193980678466505111 695216128790971017699757667)
        ·
          refine ⟨1042824193186456526549636501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695216128790971017699757667 1042824193186456526549636501)
          ·
            refine ⟨48882384055615149682014211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1042824193186456526549636501 48882384055615149682014211)
            ·
              refine ⟨73323576083422724523021317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48882384055615149682014211 73323576083422724523021317)
              ·
                refine ⟨13748170515641760848066497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73323576083422724523021317 13748170515641760848066497)
                ·
                  refine ⟨10311127886731320636049873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748170515641760848066497 10311127886731320636049873)
                  ·
                    refine ⟨7733345915048490477037405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10311127886731320636049873 7733345915048490477037405)
                    ·
                      refine ⟨2900004718143183928889027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733345915048490477037405 2900004718143183928889027)
                      ·
                        rfl

theorem cell23_5647739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 3].length) (baseStart_5647739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647739 prefixEnd_5647739 := by exact prefixLift 5647739
  have htrace : WordTrace (prefixWord ++ tailWord_5647739) baseStart_5647739 baseEnd_5647739 := by
    simpa [prefixWord, tailWord_5647739, baseEnd_5647739] using wordTrace_append hprefix tailTrace_5647739
  have hstable : (prefixWord ++ tailWord_5647739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647739).length < 2 ^ (prefixWord ++ tailWord_5647739).sum := by decide
  have hdescent : baseEnd_5647739 < baseStart_5647739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647773 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_5647773 : Nat := 118140960795 + 5647773 * 2 ^ 59
def prefixEnd_5647773 : Nat := 4983230072969 + 3 ^ 40 * 5647773 * 2
def baseEnd_5647773 : Nat := 2900022176485436795863871

theorem tailTrace_5647773 : CollatzResearch.WordTrace tailWord_5647773 prefixEnd_5647773 2900022176485436795863871 := by
  unfold tailWord_5647773
  simp only [CollatzResearch.WordTrace]
  refine ⟨205991204168090458680739973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137327469445393639120493315 205991204168090458680739973)
  ·
    refine ⟨38623350781516961002638745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205991204168090458680739973 38623350781516961002638745)
    ·
      refine ⟨28967513086137720751979059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38623350781516961002638745 28967513086137720751979059)
      ·
        refine ⟨43451269629206581127968589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28967513086137720751979059 43451269629206581127968589)
        ·
          refine ⟨16294226110952467922988221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43451269629206581127968589 16294226110952467922988221)
          ·
            refine ⟨6110334791607175471120583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16294226110952467922988221 6110334791607175471120583)
            ·
              refine ⟨9165502187410763206680875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110334791607175471120583 9165502187410763206680875)
              ·
                refine ⟨13748253281116144810021313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165502187410763206680875 13748253281116144810021313)
                ·
                  refine ⟨10311189960837108607515985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748253281116144810021313 10311189960837108607515985)
                  ·
                    refine ⟨7733392470627831455636989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10311189960837108607515985 7733392470627831455636989)
                    ·
                      refine ⟨2900022176485436795863871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733392470627831455636989 2900022176485436795863871)
                      ·
                        rfl

theorem cell23_5647773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_5647773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647773 prefixEnd_5647773 := by exact prefixLift 5647773
  have htrace : WordTrace (prefixWord ++ tailWord_5647773) baseStart_5647773 baseEnd_5647773 := by
    simpa [prefixWord, tailWord_5647773, baseEnd_5647773] using wordTrace_append hprefix tailTrace_5647773
  have hstable : (prefixWord ++ tailWord_5647773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647773).length < 2 ^ (prefixWord ++ tailWord_5647773).sum := by decide
  have hdescent : baseEnd_5647773 < baseStart_5647773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647802 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_5647802 : Nat := 118140960795 + 5647802 * 2 ^ 59
def prefixEnd_5647802 : Nat := 4983230072969 + 3 ^ 40 * 5647802 * 2
def baseEnd_5647802 : Nat := 966679022474805727467079

theorem tailTrace_5647802 : CollatzResearch.WordTrace tailWord_5647802 prefixEnd_5647802 966679022474805727467079 := by
  unfold tailWord_5647802
  simp only [CollatzResearch.WordTrace]
  refine ⟨51498065471246349158386415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137328174589990264422363773 51498065471246349158386415)
  ·
    refine ⟨77247098206869523737579623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51498065471246349158386415 77247098206869523737579623)
    ·
      refine ⟨115870647310304285606369435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77247098206869523737579623 115870647310304285606369435)
      ·
        refine ⟨173805970965456428409554153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115870647310304285606369435 173805970965456428409554153)
        ·
          refine ⟨130354478224092321307165615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173805970965456428409554153 130354478224092321307165615)
          ·
            refine ⟨195531717336138481960748423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130354478224092321307165615 195531717336138481960748423)
            ·
              refine ⟨293297576004207722941122635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195531717336138481960748423 293297576004207722941122635)
              ·
                refine ⟨439946364006311584411683953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293297576004207722941122635 439946364006311584411683953)
                ·
                  refine ⟨329959773004733688308762965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439946364006311584411683953 329959773004733688308762965)
                  ·
                    refine ⟨966679022474805727467079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 329959773004733688308762965 966679022474805727467079)
                    ·
                      rfl

theorem cell23_5647802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_5647802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647802 prefixEnd_5647802 := by exact prefixLift 5647802
  have htrace : WordTrace (prefixWord ++ tailWord_5647802) baseStart_5647802 baseEnd_5647802 := by
    simpa [prefixWord, tailWord_5647802, baseEnd_5647802] using wordTrace_append hprefix tailTrace_5647802
  have hstable : (prefixWord ++ tailWord_5647802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647802).length < 2 ^ (prefixWord ++ tailWord_5647802).sum := by decide
  have hdescent : baseEnd_5647802 < baseStart_5647802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647819 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 6]
def baseStart_5647819 : Nat := 118140960795 + 5647819 * 2 ^ 59
def prefixEnd_5647819 : Nat := 4983230072969 + 3 ^ 40 * 5647819 * 2
def baseEnd_5647819 : Nat := 966681932198514538629553

theorem tailTrace_5647819 : CollatzResearch.WordTrace tailWord_5647819 prefixEnd_5647819 966681932198514538629553 := by
  unfold tailWord_5647819
  simp only [CollatzResearch.WordTrace]
  refine ⟨205992881925923808536914511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137328587950615872357943007 205992881925923808536914511)
  ·
    refine ⟨308989322888885712805371767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205992881925923808536914511 308989322888885712805371767)
    ·
      refine ⟨463483984333328569208057651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308989322888885712805371767 463483984333328569208057651)
      ·
        refine ⟨695225976499992853812086477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463483984333328569208057651 695225976499992853812086477)
        ·
          refine ⟨260709741187497320179532429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695225976499992853812086477 260709741187497320179532429)
          ·
            refine ⟨97766152945311495067324661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260709741187497320179532429 97766152945311495067324661)
            ·
              refine ⟨9165576838622952662561687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97766152945311495067324661 9165576838622952662561687)
              ·
                refine ⟨13748365257934428993842531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165576838622952662561687 13748365257934428993842531)
                ·
                  refine ⟨20622547886901643490763797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13748365257934428993842531 20622547886901643490763797)
                  ·
                    refine ⟨966681932198514538629553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20622547886901643490763797 966681932198514538629553)
                    ·
                      rfl

theorem cell23_5647819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 6].length) (baseStart_5647819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647819 prefixEnd_5647819 := by exact prefixLift 5647819
  have htrace : WordTrace (prefixWord ++ tailWord_5647819) baseStart_5647819 baseEnd_5647819 := by
    simpa [prefixWord, tailWord_5647819, baseEnd_5647819] using wordTrace_append hprefix tailTrace_5647819
  have hstable : (prefixWord ++ tailWord_5647819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647819).length < 2 ^ (prefixWord ++ tailWord_5647819).sum := by decide
  have hdescent : baseEnd_5647819 < baseStart_5647819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647829 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5647829 : Nat := 118140960795 + 5647829 * 2 ^ 59
def prefixEnd_5647829 : Nat := 4983230072969 + 3 ^ 40 * 5647829 * 2
def baseEnd_5647829 : Nat := 2900050931402088576763613

theorem tailTrace_5647829 : CollatzResearch.WordTrace tailWord_5647829 prefixEnd_5647829 2900050931402088576763613 := by
  unfold tailWord_5647829
  simp only [CollatzResearch.WordTrace]
  refine ⟨205993246655887580244778541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137328831103925053496519027 205993246655887580244778541)
  ·
    refine ⟨77247467495957842591791953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205993246655887580244778541 77247467495957842591791953)
    ·
      refine ⟨57935600621968381943843965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77247467495957842591791953 57935600621968381943843965)
      ·
        refine ⟨21725850233238143228941487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57935600621968381943843965 21725850233238143228941487)
        ·
          refine ⟨32588775349857214843412231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725850233238143228941487 32588775349857214843412231)
          ·
            refine ⟨48883163024785822265118347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32588775349857214843412231 48883163024785822265118347)
            ·
              refine ⟨73324744537178733397677521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48883163024785822265118347 73324744537178733397677521)
              ·
                refine ⟨54993558402884050048258141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73324744537178733397677521 54993558402884050048258141)
                ·
                  refine ⟨20622584401081518768096803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54993558402884050048258141 20622584401081518768096803)
                  ·
                    refine ⟨30933876601622278152145205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20622584401081518768096803 30933876601622278152145205)
                    ·
                      refine ⟨2900050931402088576763613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30933876601622278152145205 2900050931402088576763613)
                      ·
                        rfl

theorem cell23_5647829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5647829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647829 prefixEnd_5647829 := by exact prefixLift 5647829
  have htrace : WordTrace (prefixWord ++ tailWord_5647829) baseStart_5647829 baseEnd_5647829 := by
    simpa [prefixWord, tailWord_5647829, baseEnd_5647829] using wordTrace_append hprefix tailTrace_5647829
  have hstable : (prefixWord ++ tailWord_5647829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647829).length < 2 ^ (prefixWord ++ tailWord_5647829).sum := by decide
  have hdescent : baseEnd_5647829 < baseStart_5647829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647837 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5647837 : Nat := 118140960795 + 5647837 * 2 ^ 59
def prefixEnd_5647837 : Nat := 4983230072969 + 3 ^ 40 * 5647837 * 2
def baseEnd_5647837 : Nat := 2900055039247324545463577

theorem tailTrace_5647837 : CollatzResearch.WordTrace tailWord_5647837 prefixEnd_5647837 2900055039247324545463577 := by
  unfold tailWord_5647837
  simp only [CollatzResearch.WordTrace]
  refine ⟨205993538439858597611069765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137329025626572398407379843 205993538439858597611069765)
  ·
    refine ⟨38623788457473487052075581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205993538439858597611069765 38623788457473487052075581)
    ·
      refine ⟨14483920671552557644528343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38623788457473487052075581 14483920671552557644528343)
      ·
        refine ⟨21725881007328836466792515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14483920671552557644528343 21725881007328836466792515)
        ·
          refine ⟨32588821510993254700188773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725881007328836466792515 32588821510993254700188773)
          ·
            refine ⟨6110404033311235256285395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32588821510993254700188773 6110404033311235256285395)
            ·
              refine ⟨9165606049966852884428093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110404033311235256285395 9165606049966852884428093)
              ·
                refine ⟨3437102268737569831660535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9165606049966852884428093 3437102268737569831660535)
                ·
                  refine ⟨5155653403106354747490803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437102268737569831660535 5155653403106354747490803)
                  ·
                    refine ⟨7733480104659532121236205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155653403106354747490803 7733480104659532121236205)
                    ·
                      refine ⟨2900055039247324545463577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733480104659532121236205 2900055039247324545463577)
                      ·
                        rfl

theorem cell23_5647837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5647837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647837 prefixEnd_5647837 := by exact prefixLift 5647837
  have htrace : WordTrace (prefixWord ++ tailWord_5647837) baseStart_5647837 baseEnd_5647837 := by
    simpa [prefixWord, tailWord_5647837, baseEnd_5647837] using wordTrace_append hprefix tailTrace_5647837
  have hstable : (prefixWord ++ tailWord_5647837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647837).length < 2 ^ (prefixWord ++ tailWord_5647837).sum := by decide
  have hdescent : baseEnd_5647837 < baseStart_5647837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647839 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_5647839 : Nat := 118140960795 + 5647839 * 2 ^ 59
def prefixEnd_5647839 : Nat := 4983230072969 + 3 ^ 40 * 5647839 * 2
def baseEnd_5647839 : Nat := 2900056066208633537638567

theorem tailTrace_5647839 : CollatzResearch.WordTrace tailWord_5647839 prefixEnd_5647839 2900056066208633537638567 := by
  unfold tailWord_5647839
  simp only [CollatzResearch.WordTrace]
  refine ⟨205993611385851351952642571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137329074257234234635095047 205993611385851351952642571)
  ·
    refine ⟨308990417078777027928963857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205993611385851351952642571 308990417078777027928963857)
    ·
      refine ⟨231742812809082770946722893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308990417078777027928963857 231742812809082770946722893)
      ·
        refine ⟨86903554803406039105021085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231742812809082770946722893 86903554803406039105021085)
        ·
          refine ⟨32588833051277264664382907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86903554803406039105021085 32588833051277264664382907)
          ·
            refine ⟨48883249576915896996574361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32588833051277264664382907 48883249576915896996574361)
            ·
              refine ⟨36662437182686922747430771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48883249576915896996574361 36662437182686922747430771)
              ·
                refine ⟨54993655774030384121146157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36662437182686922747430771 54993655774030384121146157)
                ·
                  refine ⟨20622620915261394045429809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54993655774030384121146157 20622620915261394045429809)
                  ·
                    refine ⟨15466965686446045534072357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20622620915261394045429809 15466965686446045534072357)
                    ·
                      refine ⟨2900056066208633537638567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15466965686446045534072357 2900056066208633537638567)
                      ·
                        rfl

theorem cell23_5647839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_5647839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647839 prefixEnd_5647839 := by exact prefixLift 5647839
  have htrace : WordTrace (prefixWord ++ tailWord_5647839) baseStart_5647839 baseEnd_5647839 := by
    simpa [prefixWord, tailWord_5647839, baseEnd_5647839] using wordTrace_append hprefix tailTrace_5647839
  have hstable : (prefixWord ++ tailWord_5647839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647839).length < 2 ^ (prefixWord ++ tailWord_5647839).sum := by decide
  have hdescent : baseEnd_5647839 < baseStart_5647839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647859 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3]
def baseStart_5647859 : Nat := 118140960795 + 5647859 * 2 ^ 59
def prefixEnd_5647859 : Nat := 4983230072969 + 3 ^ 40 * 5647859 * 2
def baseEnd_5647859 : Nat := 2900066335821723459388475

theorem tailTrace_5647859 : CollatzResearch.WordTrace tailWord_5647859 prefixEnd_5647859 2900066335821723459388475 := by
  unfold tailWord_5647859
  simp only [CollatzResearch.WordTrace]
  refine ⟨205994340845778895368370631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137329560563852596912247087 205994340845778895368370631)
  ·
    refine ⟨308991511268668343052555947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205994340845778895368370631 308991511268668343052555947)
    ·
      refine ⟨463487266903002514578833921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308991511268668343052555947 463487266903002514578833921)
      ·
        refine ⟨347615450177251885934125441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463487266903002514578833921 347615450177251885934125441)
        ·
          refine ⟨260711587632938914450594081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347615450177251885934125441 260711587632938914450594081)
          ·
            refine ⟨195533690724704185837945561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260711587632938914450594081 195533690724704185837945561)
            ·
              refine ⟨146650268043528139378459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195533690724704185837945561 146650268043528139378459171)
              ·
                refine ⟨219975402065292209067688757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146650268043528139378459171 219975402065292209067688757)
                ·
                  refine ⟨20622693943621144600095821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219975402065292209067688757 20622693943621144600095821)
                  ·
                    refine ⟨7733510228857929225035933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20622693943621144600095821 7733510228857929225035933)
                    ·
                      refine ⟨2900066335821723459388475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733510228857929225035933 2900066335821723459388475)
                      ·
                        rfl

theorem cell23_5647859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_5647859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647859 prefixEnd_5647859 := by exact prefixLift 5647859
  have htrace : WordTrace (prefixWord ++ tailWord_5647859) baseStart_5647859 baseEnd_5647859 := by
    simpa [prefixWord, tailWord_5647859, baseEnd_5647859] using wordTrace_append hprefix tailTrace_5647859
  have hstable : (prefixWord ++ tailWord_5647859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647859).length < 2 ^ (prefixWord ++ tailWord_5647859).sum := by decide
  have hdescent : baseEnd_5647859 < baseStart_5647859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647903 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 1, 3, 2]
def baseStart_5647903 : Nat := 118140960795 + 5647903 * 2 ^ 59
def prefixEnd_5647903 : Nat := 4983230072969 + 3 ^ 40 * 5647903 * 2
def baseEnd_5647903 : Nat := 2900088928970521287238273

theorem tailTrace_5647903 : CollatzResearch.WordTrace tailWord_5647903 prefixEnd_5647903 2900088928970521287238273 := by
  unfold tailWord_5647903
  simp only [CollatzResearch.WordTrace]
  refine ⟨205995945657619490882972363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137330630438412993921981575 205995945657619490882972363)
  ·
    refine ⟨308993918486429236324458545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205995945657619490882972363 308993918486429236324458545)
    ·
      refine ⟨231745438864821927243343909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 308993918486429236324458545 231745438864821927243343909)
      ·
        refine ⟨43452269787154111358126983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231745438864821927243343909 43452269787154111358126983)
        ·
          refine ⟨65178404680731167037190475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43452269787154111358126983 65178404680731167037190475)
          ·
            refine ⟨97767607021096750555785713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65178404680731167037190475 97767607021096750555785713)
            ·
              refine ⟨73325705265822562916839285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97767607021096750555785713 73325705265822562916839285)
              ·
                refine ⟨6874284868670865273453683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73325705265822562916839285 6874284868670865273453683)
                ·
                  refine ⟨10311427303006297910180525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6874284868670865273453683 10311427303006297910180525)
                  ·
                    refine ⟨3866785238627361716317697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10311427303006297910180525 3866785238627361716317697)
                    ·
                      refine ⟨2900088928970521287238273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866785238627361716317697 2900088928970521287238273)
                      ·
                        rfl

theorem cell23_5647903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_5647903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647903 prefixEnd_5647903 := by exact prefixLift 5647903
  have htrace : WordTrace (prefixWord ++ tailWord_5647903) baseStart_5647903 baseEnd_5647903 := by
    simpa [prefixWord, tailWord_5647903, baseEnd_5647903] using wordTrace_append hprefix tailTrace_5647903
  have hstable : (prefixWord ++ tailWord_5647903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647903).length < 2 ^ (prefixWord ++ tailWord_5647903).sum := by decide
  have hdescent : baseEnd_5647903 < baseStart_5647903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647909 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_5647909 : Nat := 118140960795 + 5647909 * 2 ^ 59
def prefixEnd_5647909 : Nat := 4983230072969 + 3 ^ 40 * 5647909 * 2
def baseEnd_5647909 : Nat := 966697336618149421254415

theorem tailTrace_5647909 : CollatzResearch.WordTrace tailWord_5647909 prefixEnd_5647909 966697336618149421254415 := by
  unfold tailWord_5647909
  simp only [CollatzResearch.WordTrace]
  refine ⟨205996164495597753907690781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137330776330398502605127187 205996164495597753907690781)
  ·
    refine ⟨77248561685849157715384043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205996164495597753907690781 77248561685849157715384043)
    ·
      refine ⟨115872842528773736573076065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77248561685849157715384043 115872842528773736573076065)
      ·
        refine ⟨86904631896580302429807049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115872842528773736573076065 86904631896580302429807049)
        ·
          refine ⟨65178473922435226822355287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86904631896580302429807049 65178473922435226822355287)
          ·
            refine ⟨97767710883652840233532931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65178473922435226822355287 97767710883652840233532931)
            ·
              refine ⟨146651566325479260350299397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97767710883652840233532931 146651566325479260350299397)
              ·
                refine ⟨27497168686027361315681137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146651566325479260350299397 27497168686027361315681137)
                ·
                  refine ⟨20622876514520520986760853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27497168686027361315681137 20622876514520520986760853)
                  ·
                    refine ⟨966697336618149421254415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20622876514520520986760853 966697336618149421254415)
                    ·
                      rfl

theorem cell23_5647909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_5647909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647909 prefixEnd_5647909 := by exact prefixLift 5647909
  have htrace : WordTrace (prefixWord ++ tailWord_5647909) baseStart_5647909 baseEnd_5647909 := by
    simpa [prefixWord, tailWord_5647909, baseEnd_5647909] using wordTrace_append hprefix tailTrace_5647909
  have hstable : (prefixWord ++ tailWord_5647909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647909).length < 2 ^ (prefixWord ++ tailWord_5647909).sum := by decide
  have hdescent : baseEnd_5647909 < baseStart_5647909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647973 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 5]
def baseStart_5647973 : Nat := 118140960795 + 5647973 * 2 ^ 59
def prefixEnd_5647973 : Nat := 4983230072969 + 3 ^ 40 * 5647973 * 2
def baseEnd_5647973 : Nat := 322236096957370668151439

theorem tailTrace_5647973 : CollatzResearch.WordTrace tailWord_5647973 prefixEnd_5647973 322236096957370668151439 := by
  unfold tailWord_5647973
  simp only [CollatzResearch.WordTrace]
  refine ⟨205998498767365892838020573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137332332511577261892013715 205998498767365892838020573)
  ·
    refine ⟨77249437037762209814257715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205998498767365892838020573 77249437037762209814257715)
    ·
      refine ⟨115874155556643314721386573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77249437037762209814257715 115874155556643314721386573)
      ·
        refine ⟨43452808333741243020519965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115874155556643314721386573 43452808333741243020519965)
        ·
          refine ⟨16294803125152966132694987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43452808333741243020519965 16294803125152966132694987)
          ·
            refine ⟨24442204687729449199042481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16294803125152966132694987 24442204687729449199042481)
            ·
              refine ⟨18331653515797086899281861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24442204687729449199042481 18331653515797086899281861)
              ·
                refine ⟨3437185034211953793615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18331653515797086899281861 3437185034211953793615349)
                ·
                  refine ⟨322236096957370668151439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437185034211953793615349 322236096957370668151439)
                  ·
                    rfl

theorem cell23_5647973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_5647973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647973 prefixEnd_5647973 := by exact prefixLift 5647973
  have htrace : WordTrace (prefixWord ++ tailWord_5647973) baseStart_5647973 baseEnd_5647973 := by
    simpa [prefixWord, tailWord_5647973, baseEnd_5647973] using wordTrace_append hprefix tailTrace_5647973
  have hstable : (prefixWord ++ tailWord_5647973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647973).length < 2 ^ (prefixWord ++ tailWord_5647973).sum := by decide
  have hdescent : baseEnd_5647973 < baseStart_5647973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647979 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_5647979 : Nat := 118140960795 + 5647979 * 2 ^ 59
def prefixEnd_5647979 : Nat := 4983230072969 + 3 ^ 40 * 5647979 * 2
def baseEnd_5647979 : Nat := 2900127953500262989887923

theorem tailTrace_5647979 : CollatzResearch.WordTrace tailWord_5647979 prefixEnd_5647979 2900127953500262989887923 := by
  unfold tailWord_5647979
  simp only [CollatzResearch.WordTrace]
  refine ⟨205998717605344155862738991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137332478403562770575159327 205998717605344155862738991)
  ·
    refine ⟨308998076408016233794108487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205998717605344155862738991 308998076408016233794108487)
    ·
      refine ⟨463497114612024350691162731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308998076408016233794108487 463497114612024350691162731)
      ·
        refine ⟨695245671918036526036744097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463497114612024350691162731 695245671918036526036744097)
        ·
          refine ⟨521434253938527394527558073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695245671918036526036744097 521434253938527394527558073)
          ·
            refine ⟨391075690453895545895668555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521434253938527394527558073 391075690453895545895668555)
            ·
              refine ⟨586613535680843318843502833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391075690453895545895668555 586613535680843318843502833)
              ·
                refine ⟨439960151760632489132627125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586613535680843318843502833 439960151760632489132627125)
                ·
                  refine ⟨41246264227559295856183793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 439960151760632489132627125 41246264227559295856183793)
                  ·
                    refine ⟨30934698170669471892137845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41246264227559295856183793 30934698170669471892137845)
                    ·
                      refine ⟨2900127953500262989887923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30934698170669471892137845 2900127953500262989887923)
                      ·
                        rfl

theorem cell23_5647979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_5647979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647979 prefixEnd_5647979 := by exact prefixLift 5647979
  have htrace : WordTrace (prefixWord ++ tailWord_5647979) baseStart_5647979 baseEnd_5647979 := by
    simpa [prefixWord, tailWord_5647979, baseEnd_5647979] using wordTrace_append hprefix tailTrace_5647979
  have hstable : (prefixWord ++ tailWord_5647979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647979).length < 2 ^ (prefixWord ++ tailWord_5647979).sum := by decide
  have hdescent : baseEnd_5647979 < baseStart_5647979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5647986 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5647986 : Nat := 118140960795 + 5647986 * 2 ^ 59
def prefixEnd_5647986 : Nat := 4983230072969 + 3 ^ 40 * 5647986 * 2
def baseEnd_5647986 : Nat := 966710515954948154166797

theorem tailTrace_5647986 : CollatzResearch.WordTrace tailWord_5647986 prefixEnd_5647986 966710515954948154166797 := by
  unfold tailWord_5647986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51499743229079699014560953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137332648610879197372162541 51499743229079699014560953)
  ·
    refine ⟨38624807421809774260920715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51499743229079699014560953 38624807421809774260920715)
    ·
      refine ⟨57937211132714661391381073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38624807421809774260920715 57937211132714661391381073)
      ·
        refine ⟨43452908349535996043535805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57937211132714661391381073 43452908349535996043535805)
        ·
          refine ⟨16294840631075998516325927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43452908349535996043535805 16294840631075998516325927)
          ·
            refine ⟨24442260946613997774488891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16294840631075998516325927 24442260946613997774488891)
            ·
              refine ⟨36663391419920996661733337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24442260946613997774488891 36663391419920996661733337)
              ·
                refine ⟨27497543564940747496300003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36663391419920996661733337 27497543564940747496300003)
                ·
                  refine ⟨41246315347411121244450005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27497543564940747496300003 41246315347411121244450005)
                  ·
                    refine ⟨966710515954948154166797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41246315347411121244450005 966710515954948154166797)
                    ·
                      rfl

theorem cell23_5647986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5647986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5647986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5647986 prefixEnd_5647986 := by exact prefixLift 5647986
  have htrace : WordTrace (prefixWord ++ tailWord_5647986) baseStart_5647986 baseEnd_5647986 := by
    simpa [prefixWord, tailWord_5647986, baseEnd_5647986] using wordTrace_append hprefix tailTrace_5647986
  have hstable : (prefixWord ++ tailWord_5647986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5647986).length < 2 ^ (prefixWord ++ tailWord_5647986).sum := by decide
  have hdescent : baseEnd_5647986 < baseStart_5647986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5647986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648016 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_5648016 : Nat := 118140960795 + 5648016 * 2 ^ 59
def prefixEnd_5648016 : Nat := 4983230072969 + 3 ^ 40 * 5648016 * 2
def baseEnd_5648016 : Nat := 966715650761493115041751

theorem tailTrace_5648016 : CollatzResearch.WordTrace tailWord_5648016 prefixEnd_5648016 966715650761493115041751 := by
  unfold tailWord_5648016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103000033553105055590917951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137333378070806740787890601 103000033553105055590917951)
  ·
    refine ⟨154500050329657583386376927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103000033553105055590917951 154500050329657583386376927)
    ·
      refine ⟨231750075494486375079565391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154500050329657583386376927 231750075494486375079565391)
      ·
        refine ⟨347625113241729562619348087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231750075494486375079565391 347625113241729562619348087)
        ·
          refine ⟨521437669862594343929022131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347625113241729562619348087 521437669862594343929022131)
          ·
            refine ⟨782156504793891515893533197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521437669862594343929022131 782156504793891515893533197)
            ·
              refine ⟨293308689297709318460074949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 782156504793891515893533197 293308689297709318460074949)
              ·
                refine ⟨54995379243320497211264053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293308689297709318460074949 54995379243320497211264053)
                ·
                  refine ⟨5155816804061296613556005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54995379243320497211264053 5155816804061296613556005)
                  ·
                    refine ⟨966715650761493115041751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155816804061296613556005 966715650761493115041751)
                    ·
                      rfl

theorem cell23_5648016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_5648016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648016 prefixEnd_5648016 := by exact prefixLift 5648016
  have htrace : WordTrace (prefixWord ++ tailWord_5648016) baseStart_5648016 baseEnd_5648016 := by
    simpa [prefixWord, tailWord_5648016, baseEnd_5648016] using wordTrace_append hprefix tailTrace_5648016
  have hstable : (prefixWord ++ tailWord_5648016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648016).length < 2 ^ (prefixWord ++ tailWord_5648016).sum := by decide
  have hdescent : baseEnd_5648016 < baseStart_5648016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648020 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5648020 : Nat := 118140960795 + 5648020 * 2 ^ 59
def prefixEnd_5648020 : Nat := 4983230072969 + 3 ^ 40 * 5648020 * 2
def baseEnd_5648020 : Nat := 966716335402365776491745

theorem tailTrace_5648020 : CollatzResearch.WordTrace tailWord_5648020 prefixEnd_5648020 966716335402365776491745 := by
  unfold tailWord_5648020
  simp only [CollatzResearch.WordTrace]
  refine ⟨103000106499097809932490757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137333475332130413243321009 103000106499097809932490757)
  ·
    refine ⟨19312519968580839362342017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103000106499097809932490757 19312519968580839362342017)
    ·
      refine ⟨14484389976435629521756513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19312519968580839362342017 14484389976435629521756513)
      ·
        refine ⟨10863292482326722141317385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14484389976435629521756513 10863292482326722141317385)
        ·
          refine ⟨8147469361745041605988039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10863292482326722141317385 8147469361745041605988039)
          ·
            refine ⟨12221204042617562408982059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8147469361745041605988039 12221204042617562408982059)
            ·
              refine ⟨18331806063926343613473089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12221204042617562408982059 18331806063926343613473089)
              ·
                refine ⟨13748854547944757710104817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18331806063926343613473089 13748854547944757710104817)
                ·
                  refine ⟨10311640910958568282578613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748854547944757710104817 10311640910958568282578613)
                  ·
                    refine ⟨966716335402365776491745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10311640910958568282578613 966716335402365776491745)
                    ·
                      rfl

theorem cell23_5648020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5648020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648020 prefixEnd_5648020 := by exact prefixLift 5648020
  have htrace : WordTrace (prefixWord ++ tailWord_5648020) baseStart_5648020 baseEnd_5648020 := by
    simpa [prefixWord, tailWord_5648020, baseEnd_5648020] using wordTrace_append hprefix tailTrace_5648020
  have hstable : (prefixWord ++ tailWord_5648020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648020).length < 2 ^ (prefixWord ++ tailWord_5648020).sum := by decide
  have hdescent : baseEnd_5648020 < baseStart_5648020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648023 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5648023 : Nat := 118140960795 + 5648023 * 2 ^ 59
def prefixEnd_5648023 : Nat := 4983230072969 + 3 ^ 40 * 5648023 * 2
def baseEnd_5648023 : Nat := 2900150546649060817737721

theorem tailTrace_5648023 : CollatzResearch.WordTrace tailWord_5648023 prefixEnd_5648023 2900150546649060817737721 := by
  unfold tailWord_5648023
  simp only [CollatzResearch.WordTrace]
  refine ⟨206000322417184751377340723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137333548278123167584893815 206000322417184751377340723)
  ·
    refine ⟨309000483625777127066011085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206000322417184751377340723 309000483625777127066011085)
    ·
      refine ⟨115875181359666422649754157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309000483625777127066011085 115875181359666422649754157)
      ·
        refine ⟨43453193009874908493657809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115875181359666422649754157 43453193009874908493657809)
        ·
          refine ⟨32589894757406181370243357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43453193009874908493657809 32589894757406181370243357)
          ·
            refine ⟨12221210534027318013841259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32589894757406181370243357 12221210534027318013841259)
            ·
              refine ⟨18331815801040977020761889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12221210534027318013841259 18331815801040977020761889)
              ·
                refine ⟨13748861850780732765571417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18331815801040977020761889 13748861850780732765571417)
                ·
                  refine ⟨10311646388085549574178563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748861850780732765571417 10311646388085549574178563)
                  ·
                    refine ⟨15467469582128324361267845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10311646388085549574178563 15467469582128324361267845)
                    ·
                      refine ⟨2900150546649060817737721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15467469582128324361267845 2900150546649060817737721)
                      ·
                        rfl

theorem cell23_5648023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5648023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648023 prefixEnd_5648023 := by exact prefixLift 5648023
  have htrace : WordTrace (prefixWord ++ tailWord_5648023) baseStart_5648023 baseEnd_5648023 := by
    simpa [prefixWord, tailWord_5648023, baseEnd_5648023] using wordTrace_append hprefix tailTrace_5648023
  have hstable : (prefixWord ++ tailWord_5648023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648023).length < 2 ^ (prefixWord ++ tailWord_5648023).sum := by decide
  have hdescent : baseEnd_5648023 < baseStart_5648023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648056 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_5648056 : Nat := 118140960795 + 5648056 * 2 ^ 59
def prefixEnd_5648056 : Nat := 4983230072969 + 3 ^ 40 * 5648056 * 2
def baseEnd_5648056 : Nat := 2900167491510659188625069

theorem tailTrace_5648056 : CollatzResearch.WordTrace tailWord_5648056 prefixEnd_5648056 2900167491510659188625069 := by
  unfold tailWord_5648056
  simp only [CollatzResearch.WordTrace]
  refine ⟨103000763013032599006646011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137334350684043465342194681 103000763013032599006646011)
  ·
    refine ⟨154501144519548898509969017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103000763013032599006646011 154501144519548898509969017)
    ·
      refine ⟨115875858389661673882476763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154501144519548898509969017 115875858389661673882476763)
      ·
        refine ⟨173813787584492510823715145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115875858389661673882476763 173813787584492510823715145)
        ·
          refine ⟨130360340688369383117786359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173813787584492510823715145 130360340688369383117786359)
          ·
            refine ⟨195540511032554074676679539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130360340688369383117786359 195540511032554074676679539)
            ·
              refine ⟨293310766548831112015019309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195540511032554074676679539 293310766548831112015019309)
              ·
                refine ⟨109991537455811667005632241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293310766548831112015019309 109991537455811667005632241)
                ·
                  refine ⟨82493653091858750254224181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109991537455811667005632241 82493653091858750254224181)
                  ·
                    refine ⟨7733779977361757836333517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82493653091858750254224181 7733779977361757836333517)
                    ·
                      refine ⟨2900167491510659188625069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733779977361757836333517 2900167491510659188625069)
                      ·
                        rfl

theorem cell23_5648056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_5648056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648056 prefixEnd_5648056 := by exact prefixLift 5648056
  have htrace : WordTrace (prefixWord ++ tailWord_5648056) baseStart_5648056 baseEnd_5648056 := by
    simpa [prefixWord, tailWord_5648056, baseEnd_5648056] using wordTrace_append hprefix tailTrace_5648056
  have hstable : (prefixWord ++ tailWord_5648056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648056).length < 2 ^ (prefixWord ++ tailWord_5648056).sum := by decide
  have hdescent : baseEnd_5648056 < baseStart_5648056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648060 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5648060 : Nat := 118140960795 + 5648060 * 2 ^ 59
def prefixEnd_5648060 : Nat := 4983230072969 + 3 ^ 40 * 5648060 * 2
def baseEnd_5648060 : Nat := 2900169545433277172975051

theorem tailTrace_5648060 : CollatzResearch.WordTrace tailWord_5648060 prefixEnd_5648060 2900169545433277172975051 := by
  unfold tailWord_5648060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103000835959025353348218817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137334447945367137797625089 103000835959025353348218817)
  ·
    refine ⟨77250626969269015011164113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103000835959025353348218817 77250626969269015011164113)
    ·
      refine ⟨57937970226951761258373085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77250626969269015011164113 57937970226951761258373085)
      ·
        refine ⟨21726738835106910471889907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57937970226951761258373085 21726738835106910471889907)
        ·
          refine ⟨32590108252660365707834861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726738835106910471889907 32590108252660365707834861)
          ·
            refine ⟨12221290594747637140438073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32590108252660365707834861 12221290594747637140438073)
            ·
              refine ⟨9165967946060727855328555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12221290594747637140438073 9165967946060727855328555)
              ·
                refine ⟨13748951919091091782992833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165967946060727855328555 13748951919091091782992833)
                ·
                  refine ⟨10311713939318318837244625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748951919091091782992833 10311713939318318837244625)
                  ·
                    refine ⟨7733785454488739127933469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10311713939318318837244625 7733785454488739127933469)
                    ·
                      refine ⟨2900169545433277172975051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733785454488739127933469 2900169545433277172975051)
                      ·
                        rfl

theorem cell23_5648060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5648060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648060 prefixEnd_5648060 := by exact prefixLift 5648060
  have htrace : WordTrace (prefixWord ++ tailWord_5648060) baseStart_5648060 baseEnd_5648060 := by
    simpa [prefixWord, tailWord_5648060, baseEnd_5648060] using wordTrace_append hprefix tailTrace_5648060
  have hstable : (prefixWord ++ tailWord_5648060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648060).length < 2 ^ (prefixWord ++ tailWord_5648060).sum := by decide
  have hdescent : baseEnd_5648060 < baseStart_5648060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648077 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5648077 : Nat := 118140960795 + 5648077 * 2 ^ 59
def prefixEnd_5648077 : Nat := 4983230072969 + 3 ^ 40 * 5648077 * 2
def baseEnd_5648077 : Nat := 2900178274604403606462473

theorem tailTrace_5648077 : CollatzResearch.WordTrace tailWord_5648077 prefixEnd_5648077 2900178274604403606462473 := by
  unfold tailWord_5648077
  simp only [CollatzResearch.WordTrace]
  refine ⟨206002291958989118599806485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137334861305992745733204323 206002291958989118599806485)
  ·
    refine ⟨9656357435577614934365929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206002291958989118599806485 9656357435577614934365929)
    ·
      refine ⟨7242268076683211200774447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9656357435577614934365929 7242268076683211200774447)
      ·
        refine ⟨10863402115024816801161671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242268076683211200774447 10863402115024816801161671)
        ·
          refine ⟨16295103172537225201742507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10863402115024816801161671 16295103172537225201742507)
          ·
            refine ⟨24442654758805837802613761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16295103172537225201742507 24442654758805837802613761)
            ·
              refine ⟨18331991069104378351960321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24442654758805837802613761 18331991069104378351960321)
              ·
                refine ⟨13748993301828283763970241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18331991069104378351960321 13748993301828283763970241)
                ·
                  refine ⟨10311744976371212822977681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748993301828283763970241 10311744976371212822977681)
                  ·
                    refine ⟨7733808732278409617233261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10311744976371212822977681 7733808732278409617233261)
                    ·
                      refine ⟨2900178274604403606462473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7733808732278409617233261 2900178274604403606462473)
                      ·
                        rfl

theorem cell23_5648077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5648077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648077 prefixEnd_5648077 := by exact prefixLift 5648077
  have htrace : WordTrace (prefixWord ++ tailWord_5648077) baseStart_5648077 baseEnd_5648077 := by
    simpa [prefixWord, tailWord_5648077, baseEnd_5648077] using wordTrace_append hprefix tailTrace_5648077
  have hstable : (prefixWord ++ tailWord_5648077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648077).length < 2 ^ (prefixWord ++ tailWord_5648077).sum := by decide
  have hdescent : baseEnd_5648077 < baseStart_5648077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648083 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 8, 3, 2]
def baseStart_5648083 : Nat := 118140960795 + 5648083 * 2 ^ 59
def prefixEnd_5648083 : Nat := 4983230072969 + 3 ^ 40 * 5648083 * 2
def baseEnd_5648083 : Nat := 2900181355488330582987445

theorem tailTrace_5648083 : CollatzResearch.WordTrace tailWord_5648083 prefixEnd_5648083 2900181355488330582987445 := by
  unfold tailWord_5648083
  simp only [CollatzResearch.WordTrace]
  refine ⟨206002510796967381624524903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137335007197978254416349935 206002510796967381624524903)
  ·
    refine ⟨309003766195451072436787355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206002510796967381624524903 309003766195451072436787355)
    ·
      refine ⟨463505649293176608655181033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309003766195451072436787355 463505649293176608655181033)
      ·
        refine ⟨347629236969882456491385775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463505649293176608655181033 347629236969882456491385775)
        ·
          refine ⟨521443855454823684737078663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347629236969882456491385775 521443855454823684737078663)
          ·
            refine ⟨782165783182235527105617995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521443855454823684737078663 782165783182235527105617995)
            ·
              refine ⟨1173248674773353290658426993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782165783182235527105617995 1173248674773353290658426993)
              ·
                refine ⟨879936506080014967993820245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173248674773353290658426993 879936506080014967993820245)
                ·
                  refine ⟨10311755930625175406177581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 879936506080014967993820245 10311755930625175406177581)
                  ·
                    refine ⟨3866908473984440777316593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10311755930625175406177581 3866908473984440777316593)
                    ·
                      refine ⟨2900181355488330582987445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866908473984440777316593 2900181355488330582987445)
                      ·
                        rfl

theorem cell23_5648083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3, 2].length) (baseStart_5648083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648083 prefixEnd_5648083 := by exact prefixLift 5648083
  have htrace : WordTrace (prefixWord ++ tailWord_5648083) baseStart_5648083 baseEnd_5648083 := by
    simpa [prefixWord, tailWord_5648083, baseEnd_5648083] using wordTrace_append hprefix tailTrace_5648083
  have hstable : (prefixWord ++ tailWord_5648083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648083).length < 2 ^ (prefixWord ++ tailWord_5648083).sum := by decide
  have hdescent : baseEnd_5648083 < baseStart_5648083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648084 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_5648084 : Nat := 118140960795 + 5648084 * 2 ^ 59
def prefixEnd_5648084 : Nat := 4983230072969 + 3 ^ 40 * 5648084 * 2
def baseEnd_5648084 : Nat := 966727289656328359691647

theorem tailTrace_5648084 : CollatzResearch.WordTrace tailWord_5648084 prefixEnd_5648084 966727289656328359691647 := by
  unfold tailWord_5648084
  simp only [CollatzResearch.WordTrace]
  refine ⟨103001273634981879397655653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137335031513309172530207537 103001273634981879397655653)
  ·
    refine ⟨19312738806559102387060435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103001273634981879397655653 19312738806559102387060435)
    ·
      refine ⟨28969108209838653580590653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19312738806559102387060435 28969108209838653580590653)
      ·
        refine ⟨10863415578689495092721495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28969108209838653580590653 10863415578689495092721495)
        ·
          refine ⟨16295123368034242639082243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10863415578689495092721495 16295123368034242639082243)
          ·
            refine ⟨24442685052051363958623365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16295123368034242639082243 24442685052051363958623365)
            ·
              refine ⟨4583003447259630742241881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24442685052051363958623365 4583003447259630742241881)
              ·
                refine ⟨3437252585444723056681411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583003447259630742241881 3437252585444723056681411)
                ·
                  refine ⟨5155878878167084585022117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437252585444723056681411 5155878878167084585022117)
                  ·
                    refine ⟨966727289656328359691647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155878878167084585022117 966727289656328359691647)
                    ·
                      rfl

theorem cell23_5648084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_5648084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648084 prefixEnd_5648084 := by exact prefixLift 5648084
  have htrace : WordTrace (prefixWord ++ tailWord_5648084) baseStart_5648084 baseEnd_5648084 := by
    simpa [prefixWord, tailWord_5648084, baseEnd_5648084] using wordTrace_append hprefix tailTrace_5648084
  have hstable : (prefixWord ++ tailWord_5648084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648084).length < 2 ^ (prefixWord ++ tailWord_5648084).sum := by decide
  have hdescent : baseEnd_5648084 < baseStart_5648084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648113 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_5648113 : Nat := 118140960795 + 5648113 * 2 ^ 59
def prefixEnd_5648113 : Nat := 4983230072969 + 3 ^ 40 * 5648113 * 2
def baseEnd_5648113 : Nat := 2900196759907965465612307

theorem tailTrace_5648113 : CollatzResearch.WordTrace tailWord_5648113 prefixEnd_5648113 2900196759907965465612307 := by
  unfold tailWord_5648113
  simp only [CollatzResearch.WordTrace]
  refine ⟨206003604986858696748116993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137335736657905797832077995 206003604986858696748116993)
  ·
    refine ⟨154502703740144022561087745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206003604986858696748116993 154502703740144022561087745)
    ·
      refine ⟨115877027805108016920815809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154502703740144022561087745 115877027805108016920815809)
      ·
        refine ⟨86907770853831012690611857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115877027805108016920815809 86907770853831012690611857)
        ·
          refine ⟨65180828140373259517958893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86907770853831012690611857 65180828140373259517958893)
          ·
            refine ⟨24442810552639972319234585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65180828140373259517958893 24442810552639972319234585)
            ·
              refine ⟨18332107914479979239425939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24442810552639972319234585 18332107914479979239425939)
              ·
                refine ⟨27498161871719968859138909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18332107914479979239425939 27498161871719968859138909)
                ·
                  refine ⟨10311810701894988322177091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27498161871719968859138909 10311810701894988322177091)
                  ·
                    refine ⟨15467716052842482483265637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10311810701894988322177091 15467716052842482483265637)
                    ·
                      refine ⟨2900196759907965465612307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15467716052842482483265637 2900196759907965465612307)
                      ·
                        rfl

theorem cell23_5648113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_5648113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648113 prefixEnd_5648113 := by exact prefixLift 5648113
  have htrace : WordTrace (prefixWord ++ tailWord_5648113) baseStart_5648113 baseEnd_5648113 := by
    simpa [prefixWord, tailWord_5648113, baseEnd_5648113] using wordTrace_append hprefix tailTrace_5648113
  have hstable : (prefixWord ++ tailWord_5648113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648113).length < 2 ^ (prefixWord ++ tailWord_5648113).sum := by decide
  have hdescent : baseEnd_5648113 < baseStart_5648113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648136 : List Nat := [2, 1, 3, 2, 2, 1, 12]
def baseStart_5648136 : Nat := 118140960795 + 5648136 * 2 ^ 59
def prefixEnd_5648136 : Nat := 4983230072969 + 3 ^ 40 * 5648136 * 2
def baseEnd_5648136 : Nat := 35805044073617516983021

theorem tailTrace_5648136 : CollatzResearch.WordTrace tailWord_5648136 prefixEnd_5648136 35805044073617516983021 := by
  unfold tailWord_5648136
  simp only [CollatzResearch.WordTrace]
  refine ⟨103002221932887685838102131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137336295910516914450802841 103002221932887685838102131)
  ·
    refine ⟨154503332899331528757153197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103002221932887685838102131 154503332899331528757153197)
    ·
      refine ⟨57938749837249323283932449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154503332899331528757153197 57938749837249323283932449)
      ·
        refine ⟨43454062377936992462949337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57938749837249323283932449 43454062377936992462949337)
        ·
          refine ⟨32590546783452744347212003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43454062377936992462949337 32590546783452744347212003)
          ·
            refine ⟨48885820175179116520818005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32590546783452744347212003 48885820175179116520818005)
            ·
              refine ⟨35805044073617516983021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48885820175179116520818005 35805044073617516983021)
              ·
                rfl

theorem cell23_5648136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 12].length) (baseStart_5648136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648136 prefixEnd_5648136 := by exact prefixLift 5648136
  have htrace : WordTrace (prefixWord ++ tailWord_5648136) baseStart_5648136 baseEnd_5648136 := by
    simpa [prefixWord, tailWord_5648136, baseEnd_5648136] using wordTrace_append hprefix tailTrace_5648136
  have hstable : (prefixWord ++ tailWord_5648136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648136).length < 2 ^ (prefixWord ++ tailWord_5648136).sum := by decide
  have hdescent : baseEnd_5648136 < baseStart_5648136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648140 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_5648140 : Nat := 118140960795 + 5648140 * 2 ^ 59
def prefixEnd_5648140 : Nat := 4983230072969 + 3 ^ 40 * 5648140 * 2
def baseEnd_5648140 : Nat := 966736874628545619991561

theorem tailTrace_5648140 : CollatzResearch.WordTrace tailWord_5648140 prefixEnd_5648140 966736874628545619991561 := by
  unfold tailWord_5648140
  simp only [CollatzResearch.WordTrace]
  refine ⟨103002294878880440179674937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137336393171840586906233249 103002294878880440179674937)
  ·
    refine ⟨77251721159160330134756203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103002294878880440179674937 77251721159160330134756203)
    ·
      refine ⟨115877581738740495202134305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77251721159160330134756203 115877581738740495202134305)
      ·
        refine ⟨86908186304055371401600729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115877581738740495202134305 86908186304055371401600729)
        ·
          refine ⟨65181139728041528551200547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86908186304055371401600729 65181139728041528551200547)
          ·
            refine ⟨97771709592062292826800821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65181139728041528551200547 97771709592062292826800821)
            ·
              refine ⟨9166097774255839952512577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97771709592062292826800821 9166097774255839952512577)
              ·
                refine ⟨6874573330691879964384433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9166097774255839952512577 6874573330691879964384433)
                ·
                  refine ⟨5155929998018909973288325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874573330691879964384433 5155929998018909973288325)
                  ·
                    refine ⟨966736874628545619991561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155929998018909973288325 966736874628545619991561)
                    ·
                      rfl

theorem cell23_5648140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_5648140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648140 prefixEnd_5648140 := by exact prefixLift 5648140
  have htrace : WordTrace (prefixWord ++ tailWord_5648140) baseStart_5648140 baseEnd_5648140 := by
    simpa [prefixWord, tailWord_5648140, baseEnd_5648140] using wordTrace_append hprefix tailTrace_5648140
  have hstable : (prefixWord ++ tailWord_5648140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648140).length < 2 ^ (prefixWord ++ tailWord_5648140).sum := by decide
  have hdescent : baseEnd_5648140 < baseStart_5648140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
