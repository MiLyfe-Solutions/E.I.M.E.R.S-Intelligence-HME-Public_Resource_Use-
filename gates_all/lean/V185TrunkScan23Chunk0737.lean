import V185TrunkScan23Chunk0736

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4357934 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_4357934 : Nat := 118140960795 + 4357934 * 2 ^ 59
def prefixEnd_4357934 : Nat := 4983230072969 + 3 ^ 40 * 4357934 * 2
def baseEnd_4357934 : Nat := 248634978063428644098137

theorem tailTrace_4357934 : CollatzResearch.WordTrace tailWord_4357934 prefixEnd_4357934 248634978063428644098137 := by
  unfold tailWord_4357934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868363874244608589685107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105964607329304579144987237 19868363874244608589685107)
  ·
    refine ⟨29802545811366912884527661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19868363874244608589685107 29802545811366912884527661)
    ·
      refine ⟨11175954679262592331697873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29802545811366912884527661 11175954679262592331697873)
      ·
        refine ⟨8381966009446944248773405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11175954679262592331697873 8381966009446944248773405)
        ·
          refine ⟨3143237253542604093290027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8381966009446944248773405 3143237253542604093290027)
          ·
            refine ⟨4714855880313906139935041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143237253542604093290027 4714855880313906139935041)
            ·
              refine ⟨3536141910235429604951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4714855880313906139935041 3536141910235429604951281)
              ·
                refine ⟨2652106432676572203713461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536141910235429604951281 2652106432676572203713461)
                ·
                  refine ⟨248634978063428644098137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652106432676572203713461 248634978063428644098137)
                  ·
                    rfl

theorem cell23_4357934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_4357934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357934 prefixEnd_4357934 := by exact prefixLift 4357934
  have htrace : WordTrace (prefixWord ++ tailWord_4357934) baseStart_4357934 baseEnd_4357934 := by
    simpa [prefixWord, tailWord_4357934, baseEnd_4357934] using wordTrace_append hprefix tailTrace_4357934
  have hstable : (prefixWord ++ tailWord_4357934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357934).length < 2 ^ (prefixWord ++ tailWord_4357934).sum := by decide
  have hdescent : baseEnd_4357934 < baseStart_4357934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357950 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_4357950 : Nat := 118140960795 + 4357950 * 2 ^ 59
def prefixEnd_4357950 : Nat := 4983230072969 + 3 ^ 40 * 4357950 * 2
def baseEnd_4357950 : Nat := 2237723018261329734283159

theorem tailTrace_4357950 : CollatzResearch.WordTrace tailWord_4357950 prefixEnd_4357950 2237723018261329734283159 := by
  unfold tailWord_4357950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868436820237362931257913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105964996374599268966708869 19868436820237362931257913)
  ·
    refine ⟨14901327615178022198443435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19868436820237362931257913 14901327615178022198443435)
    ·
      refine ⟨22351991422767033297665153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14901327615178022198443435 22351991422767033297665153)
      ·
        refine ⟨16763993567075274973248865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22351991422767033297665153 16763993567075274973248865)
        ·
          refine ⟨12572995175306456229936649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16763993567075274973248865 12572995175306456229936649)
          ·
            refine ⟨9429746381479842172452487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12572995175306456229936649 9429746381479842172452487)
            ·
              refine ⟨14144619572219763258678731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9429746381479842172452487 14144619572219763258678731)
              ·
                refine ⟨21216929358329644888018097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14144619572219763258678731 21216929358329644888018097)
                ·
                  refine ⟨15912697018747233666013573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21216929358329644888018097 15912697018747233666013573)
                  ·
                    refine ⟨2983630691015106312377545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15912697018747233666013573 2983630691015106312377545)
                    ·
                      refine ⟨2237723018261329734283159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983630691015106312377545 2237723018261329734283159)
                      ·
                        rfl

theorem cell23_4357950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_4357950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357950 prefixEnd_4357950 := by exact prefixLift 4357950
  have htrace : WordTrace (prefixWord ++ tailWord_4357950) baseStart_4357950 baseEnd_4357950 := by
    simpa [prefixWord, tailWord_4357950, baseEnd_4357950] using wordTrace_append hprefix tailTrace_4357950
  have hstable : (prefixWord ++ tailWord_4357950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357950).length < 2 ^ (prefixWord ++ tailWord_4357950).sum := by decide
  have hdescent : baseEnd_4357950 < baseStart_4357950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357970 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_4357970 : Nat := 118140960795 + 4357970 * 2 ^ 59
def prefixEnd_4357970 : Nat := 4983230072969 + 3 ^ 40 * 4357970 * 2
def baseEnd_4357970 : Nat := 2237733287874419656033067

theorem tailTrace_4357970 : CollatzResearch.WordTrace tailWord_4357970 prefixEnd_4357970 2237733287874419656033067 := by
  unfold tailWord_4357970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39737056005456611716447841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105965482681217631243860909 39737056005456611716447841)
  ·
    refine ⟨29802792004092458787335881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39737056005456611716447841 29802792004092458787335881)
    ·
      refine ⟨22352094003069344090501911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29802792004092458787335881 22352094003069344090501911)
      ·
        refine ⟨33528141004604016135752867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22352094003069344090501911 33528141004604016135752867)
        ·
          refine ⟨50292211506906024203629301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33528141004604016135752867 50292211506906024203629301)
          ·
            refine ⟨4714894828772439769090247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50292211506906024203629301 4714894828772439769090247)
            ·
              refine ⟨7072342243158659653635371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714894828772439769090247 7072342243158659653635371)
              ·
                refine ⟨10608513364737989480453057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072342243158659653635371 10608513364737989480453057)
                ·
                  refine ⟨7956385023553492110339793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10608513364737989480453057 7956385023553492110339793)
                  ·
                    refine ⟨5967288767665119082754845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7956385023553492110339793 5967288767665119082754845)
                    ·
                      refine ⟨2237733287874419656033067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967288767665119082754845 2237733287874419656033067)
                      ·
                        rfl

theorem cell23_4357970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_4357970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357970 prefixEnd_4357970 := by exact prefixLift 4357970
  have htrace : WordTrace (prefixWord ++ tailWord_4357970) baseStart_4357970 baseEnd_4357970 := by
    simpa [prefixWord, tailWord_4357970, baseEnd_4357970] using wordTrace_append hprefix tailTrace_4357970
  have hstable : (prefixWord ++ tailWord_4357970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357970).length < 2 ^ (prefixWord ++ tailWord_4357970).sum := by decide
  have hdescent : baseEnd_4357970 < baseStart_4357970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357993 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 2, 3, 2]
def baseStart_4357993 : Nat := 118140960795 + 4357993 * 2 ^ 59
def prefixEnd_4357993 : Nat := 4983230072969 + 3 ^ 40 * 4357993 * 2
def baseEnd_4357993 : Nat := 2237745097929473066045461

theorem tailTrace_4357993 : CollatzResearch.WordTrace tailWord_4357993 prefixEnd_4357993 2237745097929473066045461 := by
  unfold tailWord_4357993
  simp only [CollatzResearch.WordTrace]
  refine ⟨158949062900743121793878633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105966041933828747862585755 158949062900743121793878633)
  ·
    refine ⟨119211797175557341345408975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158949062900743121793878633 119211797175557341345408975)
    ·
      refine ⟨178817695763336012018113463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119211797175557341345408975 178817695763336012018113463)
      ·
        refine ⟨268226543645004018027170195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178817695763336012018113463 268226543645004018027170195)
        ·
          refine ⟨402339815467506027040755293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268226543645004018027170195 402339815467506027040755293)
          ·
            refine ⟨150877430800314760140283235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402339815467506027040755293 150877430800314760140283235)
            ·
              refine ⟨226316146200472140210424853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150877430800314760140283235 226316146200472140210424853)
              ·
                refine ⟨10608569353147131572363665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 226316146200472140210424853 10608569353147131572363665)
                ·
                  refine ⟨7956427014860348679272749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10608569353147131572363665 7956427014860348679272749)
                  ·
                    refine ⟨2983660130572630754727281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7956427014860348679272749 2983660130572630754727281)
                    ·
                      refine ⟨2237745097929473066045461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983660130572630754727281 2237745097929473066045461)
                      ·
                        rfl

theorem cell23_4357993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 3, 2].length) (baseStart_4357993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357993 prefixEnd_4357993 := by exact prefixLift 4357993
  have htrace : WordTrace (prefixWord ++ tailWord_4357993) baseStart_4357993 baseEnd_4357993 := by
    simpa [prefixWord, tailWord_4357993, baseEnd_4357993] using wordTrace_append hprefix tailTrace_4357993
  have hstable : (prefixWord ++ tailWord_4357993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357993).length < 2 ^ (prefixWord ++ tailWord_4357993).sum := by decide
  have hdescent : baseEnd_4357993 < baseStart_4357993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4357999 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 10]
def baseStart_4357999 : Nat := 118140960795 + 4357999 * 2 ^ 59
def prefixEnd_4357999 : Nat := 4983230072969 + 3 ^ 40 * 4357999 * 2
def baseEnd_4357999 : Nat := 745916059604466680856811

theorem tailTrace_4357999 : CollatzResearch.WordTrace tailWord_4357999 prefixEnd_4357999 745916059604466680856811 := by
  unfold tailWord_4357999
  simp only [CollatzResearch.WordTrace]
  refine ⟨158949281738721384818597051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105966187825814256545731367 158949281738721384818597051)
  ·
    refine ⟨238423922608082077227895577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158949281738721384818597051 238423922608082077227895577)
    ·
      refine ⟨178817941956061557920921683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238423922608082077227895577 178817941956061557920921683)
      ·
        refine ⟨268226912934092336881382525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178817941956061557920921683 268226912934092336881382525)
        ·
          refine ⟨100585092350284626330518447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268226912934092336881382525 100585092350284626330518447)
          ·
            refine ⟨150877638525426939495777671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100585092350284626330518447 150877638525426939495777671)
            ·
              refine ⟨226316457788140409243666507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150877638525426939495777671 226316457788140409243666507)
              ·
                refine ⟨339474686682210613865499761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226316457788140409243666507 339474686682210613865499761)
                ·
                  refine ⟨254606015011657960399124821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339474686682210613865499761 254606015011657960399124821)
                  ·
                    refine ⟨745916059604466680856811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 254606015011657960399124821 745916059604466680856811)
                    ·
                      rfl

theorem cell23_4357999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_4357999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4357999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4357999 prefixEnd_4357999 := by exact prefixLift 4357999
  have htrace : WordTrace (prefixWord ++ tailWord_4357999) baseStart_4357999 baseEnd_4357999 := by
    simpa [prefixWord, tailWord_4357999, baseEnd_4357999] using wordTrace_append hprefix tailTrace_4357999
  have hstable : (prefixWord ++ tailWord_4357999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4357999).length < 2 ^ (prefixWord ++ tailWord_4357999).sum := by decide
  have hdescent : baseEnd_4357999 < baseStart_4357999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4357999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358034 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4358034 : Nat := 118140960795 + 4358034 * 2 ^ 59
def prefixEnd_4358034 : Nat := 4983230072969 + 3 ^ 40 * 4358034 * 2
def baseEnd_4358034 : Nat := 2237766150636307405632773

theorem tailTrace_4358034 : CollatzResearch.WordTrace tailWord_4358034 prefixEnd_4358034 2237766150636307405632773 := by
  unfold tailWord_4358034
  simp only [CollatzResearch.WordTrace]
  refine ⟨39737639573398646449030289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105967038862396390530747437 39737639573398646449030289)
  ·
    refine ⟨29803229680048984836772717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39737639573398646449030289 29803229680048984836772717)
    ·
      refine ⟨11176211130018369313789769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29803229680048984836772717 11176211130018369313789769)
      ·
        refine ⟨8382158347513776985342327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11176211130018369313789769 8382158347513776985342327)
        ·
          refine ⟨12573237521270665478013491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8382158347513776985342327 12573237521270665478013491)
          ·
            refine ⟨18859856281905998217020237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12573237521270665478013491 18859856281905998217020237)
            ·
              refine ⟨7072446105714749331382589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18859856281905998217020237 7072446105714749331382589)
              ·
                refine ⟨2652167289643030999268471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7072446105714749331382589 2652167289643030999268471)
                ·
                  refine ⟨3978250934464546498902707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652167289643030999268471 3978250934464546498902707)
                  ·
                    refine ⟨5967376401696819748354061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3978250934464546498902707 5967376401696819748354061)
                    ·
                      refine ⟨2237766150636307405632773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967376401696819748354061 2237766150636307405632773)
                      ·
                        rfl

theorem cell23_4358034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4358034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358034 prefixEnd_4358034 := by exact prefixLift 4358034
  have htrace : WordTrace (prefixWord ++ tailWord_4358034) baseStart_4358034 baseEnd_4358034 := by
    simpa [prefixWord, tailWord_4358034, baseEnd_4358034] using wordTrace_append hprefix tailTrace_4358034
  have hstable : (prefixWord ++ tailWord_4358034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358034).length < 2 ^ (prefixWord ++ tailWord_4358034).sum := by decide
  have hdescent : baseEnd_4358034 < baseStart_4358034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358073 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4358073 : Nat := 118140960795 + 4358073 * 2 ^ 59
def prefixEnd_4358073 : Nat := 4983230072969 + 3 ^ 40 * 4358073 * 2
def baseEnd_4358073 : Nat := 2237786176381832753045093

theorem tailTrace_4358073 : CollatzResearch.WordTrace tailWord_4358073 prefixEnd_4358073 2237786176381832753045093 := by
  unfold tailWord_4358073
  simp only [CollatzResearch.WordTrace]
  refine ⟨158951980740453295456790873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105967987160302196971193915 158951980740453295456790873)
  ·
    refine ⟨119213985555339971592593155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158951980740453295456790873 119213985555339971592593155)
    ·
      refine ⟨178820978333009957388889733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119213985555339971592593155 178820978333009957388889733)
      ·
        refine ⟨33528933437439367010416825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178820978333009957388889733 33528933437439367010416825)
        ·
          refine ⟨25146700078079525257812619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33528933437439367010416825 25146700078079525257812619)
          ·
            refine ⟨37720050117119287886718929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25146700078079525257812619 37720050117119287886718929)
            ·
              refine ⟨28290037587839465915039197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37720050117119287886718929 28290037587839465915039197)
              ·
                refine ⟨10608764095439799718139699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28290037587839465915039197 10608764095439799718139699)
                ·
                  refine ⟨15913146143159699577209549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10608764095439799718139699 15913146143159699577209549)
                  ·
                    refine ⟨5967429803684887341453581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15913146143159699577209549 5967429803684887341453581)
                    ·
                      refine ⟨2237786176381832753045093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967429803684887341453581 2237786176381832753045093)
                      ·
                        rfl

theorem cell23_4358073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4358073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358073 prefixEnd_4358073 := by exact prefixLift 4358073
  have htrace : WordTrace (prefixWord ++ tailWord_4358073) baseStart_4358073 baseEnd_4358073 := by
    simpa [prefixWord, tailWord_4358073, baseEnd_4358073] using wordTrace_append hprefix tailTrace_4358073
  have hstable : (prefixWord ++ tailWord_4358073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358073).length < 2 ^ (prefixWord ++ tailWord_4358073).sum := by decide
  have hdescent : baseEnd_4358073 < baseStart_4358073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358077 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_4358077 : Nat := 118140960795 + 4358077 * 2 ^ 59
def prefixEnd_4358077 : Nat := 4983230072969 + 3 ^ 40 * 4358077 * 2
def baseEnd_4358077 : Nat := 2237788230304450737395075

theorem tailTrace_4358077 : CollatzResearch.WordTrace tailWord_4358077 prefixEnd_4358077 2237788230304450737395075 := by
  unfold tailWord_4358077
  simp only [CollatzResearch.WordTrace]
  refine ⟨158952126632438804139936485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105968084421625869426624323 158952126632438804139936485)
  ·
    refine ⟨29803523743582275776238091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 158952126632438804139936485 29803523743582275776238091)
    ·
      refine ⟨44705285615373413664357137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29803523743582275776238091 44705285615373413664357137)
      ·
        refine ⟨33528964211530060248267853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44705285615373413664357137 33528964211530060248267853)
        ·
          refine ⟨12573361579323772593100445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33528964211530060248267853 12573361579323772593100445)
          ·
            refine ⟨4715010592246414722412667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12573361579323772593100445 4715010592246414722412667)
            ·
              refine ⟨7072515888369622083619001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715010592246414722412667 7072515888369622083619001)
              ·
                refine ⟨5304386916277216562714251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7072515888369622083619001 5304386916277216562714251)
                ·
                  refine ⟨7956580374415824844071377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5304386916277216562714251 7956580374415824844071377)
                  ·
                    refine ⟨5967435280811868633053533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7956580374415824844071377 5967435280811868633053533)
                    ·
                      refine ⟨2237788230304450737395075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967435280811868633053533 2237788230304450737395075)
                      ·
                        rfl

theorem cell23_4358077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_4358077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358077 prefixEnd_4358077 := by exact prefixLift 4358077
  have htrace : WordTrace (prefixWord ++ tailWord_4358077) baseStart_4358077 baseEnd_4358077 := by
    simpa [prefixWord, tailWord_4358077, baseEnd_4358077] using wordTrace_append hprefix tailTrace_4358077
  have hstable : (prefixWord ++ tailWord_4358077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358077).length < 2 ^ (prefixWord ++ tailWord_4358077).sum := by decide
  have hdescent : baseEnd_4358077 < baseStart_4358077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358136 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 9]
def baseStart_4358136 : Nat := 118140960795 + 4358136 * 2 ^ 59
def prefixEnd_4358136 : Nat := 4983230072969 + 3 ^ 40 * 4358136 * 2
def baseEnd_4358136 : Nat := 248646502851451778506367

theorem tailTrace_4358136 : CollatzResearch.WordTrace tailWord_4358136 prefixEnd_4358136 248646502851451778506367 := by
  unfold tailWord_4358136
  simp only [CollatzResearch.WordTrace]
  refine ⟨79477139269612528608167131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105969519026150038144222841 79477139269612528608167131)
  ·
    refine ⟨119215708904418792912250697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79477139269612528608167131 119215708904418792912250697)
    ·
      refine ⟨89411781678314094684188023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119215708904418792912250697 89411781678314094684188023)
      ·
        refine ⟨134117672517471142026282035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89411781678314094684188023 134117672517471142026282035)
        ·
          refine ⟨201176508776206713039423053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134117672517471142026282035 201176508776206713039423053)
          ·
            refine ⟨75441190791077517389783645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201176508776206713039423053 75441190791077517389783645)
            ·
              refine ⟨28290446546654069021168867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75441190791077517389783645 28290446546654069021168867)
              ·
                refine ⟨42435669819981103531753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28290446546654069021168867 42435669819981103531753301)
                ·
                  refine ⟨248646502851451778506367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42435669819981103531753301 248646502851451778506367)
                  ·
                    rfl

theorem cell23_4358136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_4358136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358136 prefixEnd_4358136 := by exact prefixLift 4358136
  have htrace : WordTrace (prefixWord ++ tailWord_4358136) baseStart_4358136 baseEnd_4358136 := by
    simpa [prefixWord, tailWord_4358136, baseEnd_4358136] using wordTrace_append hprefix tailTrace_4358136
  have hstable : (prefixWord ++ tailWord_4358136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358136).length < 2 ^ (prefixWord ++ tailWord_4358136).sum := by decide
  have hdescent : baseEnd_4358136 < baseStart_4358136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358163 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3]
def baseStart_4358163 : Nat := 118140960795 + 4358163 * 2 ^ 59
def prefixEnd_4358163 : Nat := 4983230072969 + 3 ^ 40 * 4358163 * 2
def baseEnd_4358163 : Nat := 2237832389640737400919679

theorem tailTrace_4358163 : CollatzResearch.WordTrace tailWord_4358163 prefixEnd_4358163 2237832389640737400919679 := by
  unfold tailWord_4358163
  simp only [CollatzResearch.WordTrace]
  refine ⟨158955263310127240827567143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105970175540084827218378095 158955263310127240827567143)
  ·
    refine ⟨238432894965190861241350715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158955263310127240827567143 238432894965190861241350715)
    ·
      refine ⟨357649342447786291862026073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238432894965190861241350715 357649342447786291862026073)
      ·
        refine ⟨268237006835839718896519555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357649342447786291862026073 268237006835839718896519555)
        ·
          refine ⟨402355510253759578344779333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268237006835839718896519555 402355510253759578344779333)
          ·
            refine ⟨75441658172579920939646125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 402355510253759578344779333 75441658172579920939646125)
            ·
              refine ⟨28290621814717470352367297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75441658172579920939646125 28290621814717470352367297)
              ·
                refine ⟨21217966361038102764275473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28290621814717470352367297 21217966361038102764275473)
                ·
                  refine ⟨15913474770778577073206605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21217966361038102764275473 15913474770778577073206605)
                  ·
                    refine ⟨5967553039041966402452477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15913474770778577073206605 5967553039041966402452477)
                    ·
                      refine ⟨2237832389640737400919679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967553039041966402452477 2237832389640737400919679)
                      ·
                        rfl

theorem cell23_4358163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_4358163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358163 prefixEnd_4358163 := by exact prefixLift 4358163
  have htrace : WordTrace (prefixWord ++ tailWord_4358163) baseStart_4358163 baseEnd_4358163 := by
    simpa [prefixWord, tailWord_4358163, baseEnd_4358163] using wordTrace_append hprefix tailTrace_4358163
  have hstable : (prefixWord ++ tailWord_4358163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358163).length < 2 ^ (prefixWord ++ tailWord_4358163).sum := by decide
  have hdescent : baseEnd_4358163 < baseStart_4358163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358170 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_4358170 : Nat := 118140960795 + 4358170 * 2 ^ 59
def prefixEnd_4358170 : Nat := 4983230072969 + 3 ^ 40 * 4358170 * 2
def baseEnd_4358170 : Nat := 248648442667257652614683

theorem tailTrace_4358170 : CollatzResearch.WordTrace tailWord_4358170 prefixEnd_4358170 248648442667257652614683 := by
  unfold tailWord_4358170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39738879655275470255767991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105970345747401254015381309 39738879655275470255767991)
  ·
    refine ⟨59608319482913205383651987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39738879655275470255767991 59608319482913205383651987)
    ·
      refine ⟨89412479224369808075477981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59608319482913205383651987 89412479224369808075477981)
      ·
        refine ⟨33529679709138678028304243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89412479224369808075477981 33529679709138678028304243)
        ·
          refine ⟨50294519563708017042456365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33529679709138678028304243 50294519563708017042456365)
          ·
            refine ⟨18860444836390506390921137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50294519563708017042456365 18860444836390506390921137)
            ·
              refine ⟨14145333627292879793190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18860444836390506390921137 14145333627292879793190853)
              ·
                refine ⟨2652250055117414961223285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14145333627292879793190853 2652250055117414961223285)
                ·
                  refine ⟨248648442667257652614683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652250055117414961223285 248648442667257652614683)
                  ·
                    rfl

theorem cell23_4358170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_4358170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358170 prefixEnd_4358170 := by exact prefixLift 4358170
  have htrace : WordTrace (prefixWord ++ tailWord_4358170) baseStart_4358170 baseEnd_4358170 := by
    simpa [prefixWord, tailWord_4358170, baseEnd_4358170] using wordTrace_append hprefix tailTrace_4358170
  have hstable : (prefixWord ++ tailWord_4358170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358170).length < 2 ^ (prefixWord ++ tailWord_4358170).sum := by decide
  have hdescent : baseEnd_4358170 < baseStart_4358170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358220 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4358220 : Nat := 118140960795 + 4358220 * 2 ^ 59
def prefixEnd_4358220 : Nat := 4983230072969 + 3 ^ 40 * 4358220 * 2
def baseEnd_4358220 : Nat := 2237861658038043677906917

theorem tailTrace_4358220 : CollatzResearch.WordTrace tailWord_4358220 prefixEnd_4358220 2237861658038043677906917 := by
  unfold tailWord_4358220
  simp only [CollatzResearch.WordTrace]
  refine ⟨79478671135460369781196057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105971561513947159708261409 79478671135460369781196057)
  ·
    refine ⟨59609003351595277335897043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79478671135460369781196057 59609003351595277335897043)
    ·
      refine ⟨89413505027392916003845565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59609003351595277335897043 89413505027392916003845565)
      ·
        refine ⟨33530064385272343501442087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89413505027392916003845565 33530064385272343501442087)
        ·
          refine ⟨50295096577908515252163131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33530064385272343501442087 50295096577908515252163131)
          ·
            refine ⟨75442644866862772878244697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50295096577908515252163131 75442644866862772878244697)
            ·
              refine ⟨56581983650147079658683523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75442644866862772878244697 56581983650147079658683523)
              ·
                refine ⟨84872975475220619488025285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56581983650147079658683523 84872975475220619488025285)
                ·
                  refine ⟨15913682901603866154004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84872975475220619488025285 15913682901603866154004741)
                  ·
                    refine ⟨2983815544050724903875889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15913682901603866154004741 2983815544050724903875889)
                    ·
                      refine ⟨2237861658038043677906917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983815544050724903875889 2237861658038043677906917)
                      ·
                        rfl

theorem cell23_4358220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4358220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358220 prefixEnd_4358220 := by exact prefixLift 4358220
  have htrace : WordTrace (prefixWord ++ tailWord_4358220) baseStart_4358220 baseEnd_4358220 := by
    simpa [prefixWord, tailWord_4358220, baseEnd_4358220] using wordTrace_append hprefix tailTrace_4358220
  have hstable : (prefixWord ++ tailWord_4358220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358220).length < 2 ^ (prefixWord ++ tailWord_4358220).sum := by decide
  have hdescent : baseEnd_4358220 < baseStart_4358220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358290 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_4358290 : Nat := 118140960795 + 4358290 * 2 ^ 59
def prefixEnd_4358290 : Nat := 4983230072969 + 3 ^ 40 * 4358290 * 2
def baseEnd_4358290 : Nat := 745965867227952801343865

theorem tailTrace_4358290 : CollatzResearch.WordTrace tailWord_4358290 prefixEnd_4358290 745965867227952801343865 := by
  unfold tailWord_4358290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39739973845166785379360081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105973263587111427678293549 39739973845166785379360081)
  ·
    refine ⟨29804980383875089034520061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39739973845166785379360081 29804980383875089034520061)
    ·
      refine ⟨11176867643953158387945023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29804980383875089034520061 11176867643953158387945023)
      ·
        refine ⟨16765301465929737581917535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11176867643953158387945023 16765301465929737581917535)
        ·
          refine ⟨25147952198894606372876303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16765301465929737581917535 25147952198894606372876303)
          ·
            refine ⟨37721928298341909559314455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25147952198894606372876303 37721928298341909559314455)
            ·
              refine ⟨56582892447512864338971683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37721928298341909559314455 56582892447512864338971683)
              ·
                refine ⟨84874338671269296508457525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56582892447512864338971683 84874338671269296508457525)
                ·
                  refine ⟨7956969250431496547667893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84874338671269296508457525 7956969250431496547667893)
                  ·
                    refine ⟨745965867227952801343865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7956969250431496547667893 745965867227952801343865)
                    ·
                      rfl

theorem cell23_4358290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_4358290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358290 prefixEnd_4358290 := by exact prefixLift 4358290
  have htrace : WordTrace (prefixWord ++ tailWord_4358290) baseStart_4358290 baseEnd_4358290 := by
    simpa [prefixWord, tailWord_4358290, baseEnd_4358290] using wordTrace_append hprefix tailTrace_4358290
  have hstable : (prefixWord ++ tailWord_4358290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358290).length < 2 ^ (prefixWord ++ tailWord_4358290).sum := by decide
  have hdescent : baseEnd_4358290 < baseStart_4358290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358323 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_4358323 : Nat := 118140960795 + 4358323 * 2 ^ 59
def prefixEnd_4358323 : Nat := 4983230072969 + 3 ^ 40 * 4358323 * 2
def baseEnd_4358323 : Nat := 2237914546545456774918943

theorem tailTrace_4358323 : CollatzResearch.WordTrace tailWord_4358323 prefixEnd_4358323 2237914546545456774918943 := by
  unfold tailWord_4358323
  simp only [CollatzResearch.WordTrace]
  refine ⟨158961098989547588153391623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105974065993031725435594415 158961098989547588153391623)
  ·
    refine ⟨238441648484321382230087435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158961098989547588153391623 238441648484321382230087435)
    ·
      refine ⟨357662472726482073345131153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238441648484321382230087435 357662472726482073345131153)
      ·
        refine ⟨268246854544861555008848365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357662472726482073345131153 268246854544861555008848365)
        ·
          refine ⟨100592570454323083128318137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268246854544861555008848365 100592570454323083128318137)
          ·
            refine ⟨75444427840742312346238603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100592570454323083128318137 75444427840742312346238603)
            ·
              refine ⟨113166641761113468519357905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75444427840742312346238603 113166641761113468519357905)
              ·
                refine ⟨84874981320835101389518429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113166641761113468519357905 84874981320835101389518429)
                ·
                  refine ⟨31828117995313163021069411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84874981320835101389518429 31828117995313163021069411)
                  ·
                    refine ⟨47742176992969744531604117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31828117995313163021069411 47742176992969744531604117)
                    ·
                      refine ⟨2237914546545456774918943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47742176992969744531604117 2237914546545456774918943)
                      ·
                        rfl

theorem cell23_4358323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_4358323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358323 prefixEnd_4358323 := by exact prefixLift 4358323
  have htrace : WordTrace (prefixWord ++ tailWord_4358323) baseStart_4358323 baseEnd_4358323 := by
    simpa [prefixWord, tailWord_4358323, baseEnd_4358323] using wordTrace_append hprefix tailTrace_4358323
  have hstable : (prefixWord ++ tailWord_4358323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358323).length < 2 ^ (prefixWord ++ tailWord_4358323).sum := by decide
  have hdescent : baseEnd_4358323 < baseStart_4358323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358327 : List Nat := [1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_4358327 : Nat := 118140960795 + 4358327 * 2 ^ 59
def prefixEnd_4358327 : Nat := 4983230072969 + 3 ^ 40 * 4358327 * 2
def baseEnd_4358327 : Nat := 2237916600468074759268925

theorem tailTrace_4358327 : CollatzResearch.WordTrace tailWord_4358327 prefixEnd_4358327 2237916600468074759268925 := by
  unfold tailWord_4358327
  simp only [CollatzResearch.WordTrace]
  refine ⟨158961244881533096836537235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105974163254355397891024823 158961244881533096836537235)
  ·
    refine ⟨238441867322299645254805853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158961244881533096836537235 238441867322299645254805853)
    ·
      refine ⟨89415700245862366970552195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238441867322299645254805853 89415700245862366970552195)
      ·
        refine ⟨134123550368793550455828293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89415700245862366970552195 134123550368793550455828293)
        ·
          refine ⟨25148165694148790710467805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134123550368793550455828293 25148165694148790710467805)
          ·
            refine ⟨9430562135305796516425427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25148165694148790710467805 9430562135305796516425427)
            ·
              refine ⟨14145843202958694774638141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430562135305796516425427 14145843202958694774638141)
              ·
                refine ⟨5304691201109510540489303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14145843202958694774638141 5304691201109510540489303)
                ·
                  refine ⟨7957036801664265810733955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5304691201109510540489303 7957036801664265810733955)
                  ·
                    refine ⟨11935555202496398716100933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7957036801664265810733955 11935555202496398716100933)
                    ·
                      refine ⟨2237916600468074759268925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11935555202496398716100933 2237916600468074759268925)
                      ·
                        rfl

theorem cell23_4358327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_4358327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358327 prefixEnd_4358327 := by exact prefixLift 4358327
  have htrace : WordTrace (prefixWord ++ tailWord_4358327) baseStart_4358327 baseEnd_4358327 := by
    simpa [prefixWord, tailWord_4358327, baseEnd_4358327] using wordTrace_append hprefix tailTrace_4358327
  have hstable : (prefixWord ++ tailWord_4358327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358327).length < 2 ^ (prefixWord ++ tailWord_4358327).sum := by decide
  have hdescent : baseEnd_4358327 < baseStart_4358327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358338 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4358338 : Nat := 118140960795 + 4358338 * 2 ^ 59
def prefixEnd_4358338 : Nat := 4983230072969 + 3 ^ 40 * 4358338 * 2
def baseEnd_4358338 : Nat := 2237922248755274216231375

theorem tailTrace_4358338 : CollatzResearch.WordTrace tailWord_4358338 prefixEnd_4358338 2237922248755274216231375 := by
  unfold tailWord_4358338
  simp only [CollatzResearch.WordTrace]
  refine ⟨39740411521123311428796917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105974430722995497143458445 39740411521123311428796917)
  ·
    refine ⟨3725663580105310446449711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39740411521123311428796917 3725663580105310446449711)
    ·
      refine ⟨5588495370157965669674567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3725663580105310446449711 5588495370157965669674567)
      ·
        refine ⟨8382743055236948504511851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588495370157965669674567 8382743055236948504511851)
        ·
          refine ⟨12574114582855422756767777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8382743055236948504511851 12574114582855422756767777)
          ·
            refine ⟨9430585937141567067575833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12574114582855422756767777 9430585937141567067575833)
            ·
              refine ⟨7072939452856175300681875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430585937141567067575833 7072939452856175300681875)
              ·
                refine ⟨10609409179284262951022813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072939452856175300681875 10609409179284262951022813)
                ·
                  refine ⟨3978528442231598606633555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10609409179284262951022813 3978528442231598606633555)
                  ·
                    refine ⟨5967792663347397909950333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3978528442231598606633555 5967792663347397909950333)
                    ·
                      refine ⟨2237922248755274216231375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5967792663347397909950333 2237922248755274216231375)
                      ·
                        rfl

theorem cell23_4358338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4358338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358338 prefixEnd_4358338 := by exact prefixLift 4358338
  have htrace : WordTrace (prefixWord ++ tailWord_4358338) baseStart_4358338 baseEnd_4358338 := by
    simpa [prefixWord, tailWord_4358338, baseEnd_4358338] using wordTrace_append hprefix tailTrace_4358338
  have hstable : (prefixWord ++ tailWord_4358338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358338).length < 2 ^ (prefixWord ++ tailWord_4358338).sum := by decide
  have hdescent : baseEnd_4358338 < baseStart_4358338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358343 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_4358343 : Nat := 118140960795 + 4358343 * 2 ^ 59
def prefixEnd_4358343 : Nat := 4983230072969 + 3 ^ 40 * 4358343 * 2
def baseEnd_4358343 : Nat := 2237924816158546696668851

theorem tailTrace_4358343 : CollatzResearch.WordTrace tailWord_4358343 prefixEnd_4358343 2237924816158546696668851 := by
  unfold tailWord_4358343
  simp only [CollatzResearch.WordTrace]
  refine ⟨158961828449475131569119683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105974552299650087712746455 158961828449475131569119683)
  ·
    refine ⟨238442742674212697353679525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158961828449475131569119683 238442742674212697353679525)
    ·
      refine ⟨44708014251414880753814911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238442742674212697353679525 44708014251414880753814911)
      ·
        refine ⟨67062021377122321130722367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44708014251414880753814911 67062021377122321130722367)
        ·
          refine ⟨100593032065683481696083551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67062021377122321130722367 100593032065683481696083551)
          ·
            refine ⟨150889548098525222544125327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100593032065683481696083551 150889548098525222544125327)
            ·
              refine ⟨226334322147787833816187991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150889548098525222544125327 226334322147787833816187991)
              ·
                refine ⟨339501483221681750724281987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226334322147787833816187991 339501483221681750724281987)
                ·
                  refine ⟨509252224832522626086422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339501483221681750724281987 509252224832522626086422981)
                  ·
                    refine ⟨95484792156097992391204309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 509252224832522626086422981 95484792156097992391204309)
                    ·
                      refine ⟨2237924816158546696668851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95484792156097992391204309 2237924816158546696668851)
                      ·
                        rfl

theorem cell23_4358343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_4358343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358343 prefixEnd_4358343 := by exact prefixLift 4358343
  have htrace : WordTrace (prefixWord ++ tailWord_4358343) baseStart_4358343 baseEnd_4358343 := by
    simpa [prefixWord, tailWord_4358343, baseEnd_4358343] using wordTrace_append hprefix tailTrace_4358343
  have hstable : (prefixWord ++ tailWord_4358343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358343).length < 2 ^ (prefixWord ++ tailWord_4358343).sum := by decide
  have hdescent : baseEnd_4358343 < baseStart_4358343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358357 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4358357 : Nat := 118140960795 + 4358357 * 2 ^ 59
def prefixEnd_4358357 : Nat := 4983230072969 + 3 ^ 40 * 4358357 * 2
def baseEnd_4358357 : Nat := 2237932004887709641893787

theorem tailTrace_4358357 : CollatzResearch.WordTrace tailWord_4358357 prefixEnd_4358357 2237932004887709641893787 := by
  unfold tailWord_4358357
  simp only [CollatzResearch.WordTrace]
  refine ⟨158962339071424411960129325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105974892714282941306752883 158962339071424411960129325)
  ·
    refine ⟨59610877151784154485048497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158962339071424411960129325 59610877151784154485048497)
    ·
      refine ⟨44708157863838115863786373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59610877151784154485048497 44708157863838115863786373)
      ·
        refine ⟨8382779599469646724459945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44708157863838115863786373 8382779599469646724459945)
        ·
          refine ⟨6287084699602235043344959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8382779599469646724459945 6287084699602235043344959)
          ·
            refine ⟨9430627049403352565017439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287084699602235043344959 9430627049403352565017439)
            ·
              refine ⟨14145940574105028847526159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430627049403352565017439 14145940574105028847526159)
              ·
                refine ⟨21218910861157543271289239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14145940574105028847526159 21218910861157543271289239)
                ·
                  refine ⟨31828366291736314906933859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21218910861157543271289239 31828366291736314906933859)
                  ·
                    refine ⟨47742549437604472360400789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31828366291736314906933859 47742549437604472360400789)
                    ·
                      refine ⟨2237932004887709641893787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47742549437604472360400789 2237932004887709641893787)
                      ·
                        rfl

theorem cell23_4358357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4358357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358357 prefixEnd_4358357 := by exact prefixLift 4358357
  have htrace : WordTrace (prefixWord ++ tailWord_4358357) baseStart_4358357 baseEnd_4358357 := by
    simpa [prefixWord, tailWord_4358357, baseEnd_4358357] using wordTrace_append hprefix tailTrace_4358357
  have hstable : (prefixWord ++ tailWord_4358357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358357).length < 2 ^ (prefixWord ++ tailWord_4358357).sum := by decide
  have hdescent : baseEnd_4358357 < baseStart_4358357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358363 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 7]
def baseStart_4358363 : Nat := 118140960795 + 4358363 * 2 ^ 59
def prefixEnd_4358363 : Nat := 4983230072969 + 3 ^ 40 * 4358363 * 2
def baseEnd_4358363 : Nat := 745978361923878872806253

theorem tailTrace_4358363 : CollatzResearch.WordTrace tailWord_4358363 prefixEnd_4358363 745978361923878872806253 := by
  unfold tailWord_4358363
  simp only [CollatzResearch.WordTrace]
  refine ⟨158962557909402674984847743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105975038606268449989898495 158962557909402674984847743)
  ·
    refine ⟨238443836864104012477271615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158962557909402674984847743 238443836864104012477271615)
    ·
      refine ⟨357665755296156018715907423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238443836864104012477271615 357665755296156018715907423)
      ·
        refine ⟨536498632944234028073861135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357665755296156018715907423 536498632944234028073861135)
        ·
          refine ⟨804747949416351042110791703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536498632944234028073861135 804747949416351042110791703)
          ·
            refine ⟨1207121924124526563166187555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804747949416351042110791703 1207121924124526563166187555)
            ·
              refine ⟨1810682886186789844749281333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207121924124526563166187555 1810682886186789844749281333)
              ·
                refine ⟨169751520580011547945245125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1810682886186789844749281333 169751520580011547945245125)
                ·
                  refine ⟨31828410108752165239733461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169751520580011547945245125 31828410108752165239733461)
                  ·
                    refine ⟨745978361923878872806253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31828410108752165239733461 745978361923878872806253)
                    ·
                      rfl

theorem cell23_4358363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_4358363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358363 prefixEnd_4358363 := by exact prefixLift 4358363
  have htrace : WordTrace (prefixWord ++ tailWord_4358363) baseStart_4358363 baseEnd_4358363 := by
    simpa [prefixWord, tailWord_4358363, baseEnd_4358363] using wordTrace_append hprefix tailTrace_4358363
  have hstable : (prefixWord ++ tailWord_4358363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358363).length < 2 ^ (prefixWord ++ tailWord_4358363).sum := by decide
  have hdescent : baseEnd_4358363 < baseStart_4358363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358410 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_4358410 : Nat := 118140960795 + 4358410 * 2 ^ 59
def prefixEnd_4358410 : Nat := 4983230072969 + 3 ^ 40 * 4358410 * 2
def baseEnd_4358410 : Nat := 745986406454132644843681

theorem tailTrace_4358410 : CollatzResearch.WordTrace tailWord_4358410 prefixEnd_4358410 745986406454132644843681 := by
  unfold tailWord_4358410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39741068035058100502952171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105976181426821601341205789 39741068035058100502952171)
  ·
    refine ⟨59611602052587150754428257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39741068035058100502952171 59611602052587150754428257)
    ·
      refine ⟨44708701539440363065821193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59611602052587150754428257 44708701539440363065821193)
      ·
        refine ⟨33531526154580272299365895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44708701539440363065821193 33531526154580272299365895)
        ·
          refine ⟨50297289231870408449048843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33531526154580272299365895 50297289231870408449048843)
          ·
            refine ⟨75445933847805612673573265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50297289231870408449048843 75445933847805612673573265)
            ·
              refine ⟨56584450385854209505179949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75445933847805612673573265 56584450385854209505179949)
              ·
                refine ⟨21219168894695328564442481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56584450385854209505179949 21219168894695328564442481)
                ·
                  refine ⟨15914376671021496423331861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21219168894695328564442481 15914376671021496423331861)
                  ·
                    refine ⟨745986406454132644843681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15914376671021496423331861 745986406454132644843681)
                    ·
                      rfl

theorem cell23_4358410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_4358410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358410 prefixEnd_4358410 := by exact prefixLift 4358410
  have htrace : WordTrace (prefixWord ++ tailWord_4358410) baseStart_4358410 baseEnd_4358410 := by
    simpa [prefixWord, tailWord_4358410, baseEnd_4358410] using wordTrace_append hprefix tailTrace_4358410
  have hstable : (prefixWord ++ tailWord_4358410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358410).length < 2 ^ (prefixWord ++ tailWord_4358410).sum := by decide
  have hdescent : baseEnd_4358410 < baseStart_4358410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358434 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_4358434 : Nat := 118140960795 + 4358434 * 2 ^ 59
def prefixEnd_4358434 : Nat := 4983230072969 + 3 ^ 40 * 4358434 * 2
def baseEnd_4358434 : Nat := 2237971542898105840630933

theorem tailTrace_4358434 : CollatzResearch.WordTrace tailWord_4358434 prefixEnd_4358434 2237971542898105840630933 := by
  unfold tailWord_4358434
  simp only [CollatzResearch.WordTrace]
  refine ⟨39741286873036363527670589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105976764994763636073788237 39741286873036363527670589)
  ·
    refine ⟨14902982577388636322876471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39741286873036363527670589 14902982577388636322876471)
    ·
      refine ⟨22354473866082954484314707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14902982577388636322876471 22354473866082954484314707)
      ·
        refine ⟨33531710799124431726472061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22354473866082954484314707 33531710799124431726472061)
        ·
          refine ⟨12574391549671661897427023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33531710799124431726472061 12574391549671661897427023)
          ·
            refine ⟨18861587324507492846140535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12574391549671661897427023 18861587324507492846140535)
            ·
              refine ⟨28292380986761239269210803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18861587324507492846140535 28292380986761239269210803)
              ·
                refine ⟨42438571480141858903816205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28292380986761239269210803 42438571480141858903816205)
                ·
                  refine ⟨15914464305053197088931077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42438571480141858903816205 15914464305053197088931077)
                  ·
                    refine ⟨2983962057197474454174577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15914464305053197088931077 2983962057197474454174577)
                    ·
                      refine ⟨2237971542898105840630933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983962057197474454174577 2237971542898105840630933)
                      ·
                        rfl

theorem cell23_4358434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_4358434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358434 prefixEnd_4358434 := by exact prefixLift 4358434
  have htrace : WordTrace (prefixWord ++ tailWord_4358434) baseStart_4358434 baseEnd_4358434 := by
    simpa [prefixWord, tailWord_4358434, baseEnd_4358434] using wordTrace_append hprefix tailTrace_4358434
  have hstable : (prefixWord ++ tailWord_4358434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358434).length < 2 ^ (prefixWord ++ tailWord_4358434).sum := by decide
  have hdescent : baseEnd_4358434 < baseStart_4358434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358451 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 2, 2, 2]
def baseStart_4358451 : Nat := 118140960795 + 4358451 * 2 ^ 59
def prefixEnd_4358451 : Nat := 4983230072969 + 3 ^ 40 * 4358451 * 2
def baseEnd_4358451 : Nat := 2237980272069232274118355

theorem tailTrace_4358451 : CollatzResearch.WordTrace tailWord_4358451 prefixEnd_4358451 2237980272069232274118355 := by
  unfold tailWord_4358451
  simp only [CollatzResearch.WordTrace]
  refine ⟨158965767533083866014051207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105977178355389244009367471 158965767533083866014051207)
  ·
    refine ⟨238448651299625799021076811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158965767533083866014051207 238448651299625799021076811)
    ·
      refine ⟨357672976949438698531615217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238448651299625799021076811 357672976949438698531615217)
      ·
        refine ⟨268254732712079023898711413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357672976949438698531615217 268254732712079023898711413)
        ·
          refine ⟨25148881191757408490504195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268254732712079023898711413 25148881191757408490504195)
          ·
            refine ⟨37723321787636112735756293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25148881191757408490504195 37723321787636112735756293)
            ·
              refine ⟨7073122835181771137954305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37723321787636112735756293 7073122835181771137954305)
              ·
                refine ⟨5304842126386328353465729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7073122835181771137954305 5304842126386328353465729)
                ·
                  refine ⟨3978631594789746265099297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5304842126386328353465729 3978631594789746265099297)
                  ·
                    refine ⟨2983973696092309698824473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3978631594789746265099297 2983973696092309698824473)
                    ·
                      refine ⟨2237980272069232274118355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983973696092309698824473 2237980272069232274118355)
                      ·
                        rfl

theorem cell23_4358451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 2, 2].length) (baseStart_4358451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358451 prefixEnd_4358451 := by exact prefixLift 4358451
  have htrace : WordTrace (prefixWord ++ tailWord_4358451) baseStart_4358451 baseEnd_4358451 := by
    simpa [prefixWord, tailWord_4358451, baseEnd_4358451] using wordTrace_append hprefix tailTrace_4358451
  have hstable : (prefixWord ++ tailWord_4358451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358451).length < 2 ^ (prefixWord ++ tailWord_4358451).sum := by decide
  have hdescent : baseEnd_4358451 < baseStart_4358451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358468 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4358468 : Nat := 118140960795 + 4358468 * 2 ^ 59
def prefixEnd_4358468 : Nat := 4983230072969 + 3 ^ 40 * 4358468 * 2
def baseEnd_4358468 : Nat := 2237989001240358707605777

theorem tailTrace_4358468 : CollatzResearch.WordTrace tailWord_4358468 prefixEnd_4358468 2237989001240358707605777 := by
  unfold tailWord_4358468
  simp only [CollatzResearch.WordTrace]
  refine ⟨79483193787011138958710029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105977591716014851944946705 79483193787011138958710029)
  ·
    refine ⟨29806197670129177109516261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79483193787011138958710029 29806197670129177109516261)
    ·
      refine ⟨5588662063149220708034299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29806197670129177109516261 5588662063149220708034299)
      ·
        refine ⟨8382993094723831062051449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588662063149220708034299 8382993094723831062051449)
        ·
          refine ⟨6287244821042873296538587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8382993094723831062051449 6287244821042873296538587)
          ·
            refine ⟨9430867231564309944807881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287244821042873296538587 9430867231564309944807881)
            ·
              refine ⟨7073150423673232458605911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430867231564309944807881 7073150423673232458605911)
              ·
                refine ⟨10609725635509848687908867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073150423673232458605911 10609725635509848687908867)
                ·
                  refine ⟨15914588453264773031863301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10609725635509848687908867 15914588453264773031863301)
                  ·
                    refine ⟨2983985334987144943474369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15914588453264773031863301 2983985334987144943474369)
                    ·
                      refine ⟨2237989001240358707605777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2983985334987144943474369 2237989001240358707605777)
                      ·
                        rfl

theorem cell23_4358468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4358468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358468 prefixEnd_4358468 := by exact prefixLift 4358468
  have htrace : WordTrace (prefixWord ++ tailWord_4358468) baseStart_4358468 baseEnd_4358468 := by
    simpa [prefixWord, tailWord_4358468, baseEnd_4358468] using wordTrace_append hprefix tailTrace_4358468
  have hstable : (prefixWord ++ tailWord_4358468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358468).length < 2 ^ (prefixWord ++ tailWord_4358468).sum := by decide
  have hdescent : baseEnd_4358468 < baseStart_4358468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358507 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 6, 2]
def baseStart_4358507 : Nat := 118140960795 + 4358507 * 2 ^ 59
def prefixEnd_4358507 : Nat := 4983230072969 + 3 ^ 40 * 4358507 * 2
def baseEnd_4358507 : Nat := 2238009026985884055018097

theorem tailTrace_4358507 : CollatzResearch.WordTrace tailWord_4358507 prefixEnd_4358507 2238009026985884055018097 := by
  unfold tailWord_4358507
  simp only [CollatzResearch.WordTrace]
  refine ⟨158967810020880987578089775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105978540013920658385393183 158967810020880987578089775)
  ·
    refine ⟨238451715031321481367134663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158967810020880987578089775 238451715031321481367134663)
    ·
      refine ⟨357677572546982222050701995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238451715031321481367134663 357677572546982222050701995)
      ·
        refine ⟨536516358820473333076052993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357677572546982222050701995 536516358820473333076052993)
        ·
          refine ⟨402387269115354999807039745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536516358820473333076052993 402387269115354999807039745)
          ·
            refine ⟨301790451836516249855279809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402387269115354999807039745 301790451836516249855279809)
            ·
              refine ⟨226342838877387187391459857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301790451836516249855279809 226342838877387187391459857)
              ·
                refine ⟨169757129158040390543594893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226342838877387187391459857 169757129158040390543594893)
                ·
                  refine ⟨63658923434265146453848085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169757129158040390543594893 63658923434265146453848085)
                  ·
                    refine ⟨2984012035981178740024129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63658923434265146453848085 2984012035981178740024129)
                    ·
                      refine ⟨2238009026985884055018097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984012035981178740024129 2238009026985884055018097)
                      ·
                        rfl

theorem cell23_4358507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6, 2].length) (baseStart_4358507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358507 prefixEnd_4358507 := by exact prefixLift 4358507
  have htrace : WordTrace (prefixWord ++ tailWord_4358507) baseStart_4358507 baseEnd_4358507 := by
    simpa [prefixWord, tailWord_4358507, baseEnd_4358507] using wordTrace_append hprefix tailTrace_4358507
  have hstable : (prefixWord ++ tailWord_4358507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358507).length < 2 ^ (prefixWord ++ tailWord_4358507).sum := by decide
  have hdescent : baseEnd_4358507 < baseStart_4358507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358527 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_4358527 : Nat := 118140960795 + 4358527 * 2 ^ 59
def prefixEnd_4358527 : Nat := 4983230072969 + 3 ^ 40 * 4358527 * 2
def baseEnd_4358527 : Nat := 2238019296598973976768005

theorem tailTrace_4358527 : CollatzResearch.WordTrace tailWord_4358527 prefixEnd_4358527 2238019296598973976768005 := by
  unfold tailWord_4358527
  simp only [CollatzResearch.WordTrace]
  refine ⟨158968539480808530993817835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105979026320539020662545223 158968539480808530993817835)
  ·
    refine ⟨238452809221212796490726753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158968539480808530993817835 238452809221212796490726753)
    ·
      refine ⟨178839606915909597368045065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238452809221212796490726753 178839606915909597368045065)
      ·
        refine ⟨134129705186932198026033799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178839606915909597368045065 134129705186932198026033799)
        ·
          refine ⟨201194557780398297039050699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134129705186932198026033799 201194557780398297039050699)
          ·
            refine ⟨301791836670597445558576049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201194557780398297039050699 301791836670597445558576049)
            ·
              refine ⟨226343877502948084168932037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301791836670597445558576049 226343877502948084168932037)
              ·
                refine ⟨42439477031802765781674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226343877502948084168932037 42439477031802765781674757)
                ·
                  refine ⟨7957401943463018584064017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42439477031802765781674757 7957401943463018584064017)
                  ·
                    refine ⟨5968051457597263938048013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7957401943463018584064017 5968051457597263938048013)
                    ·
                      refine ⟨2238019296598973976768005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968051457597263938048013 2238019296598973976768005)
                      ·
                        rfl

theorem cell23_4358527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_4358527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358527 prefixEnd_4358527 := by exact prefixLift 4358527
  have htrace : WordTrace (prefixWord ++ tailWord_4358527) baseStart_4358527 baseEnd_4358527 := by
    simpa [prefixWord, tailWord_4358527, baseEnd_4358527] using wordTrace_append hprefix tailTrace_4358527
  have hstable : (prefixWord ++ tailWord_4358527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358527).length < 2 ^ (prefixWord ++ tailWord_4358527).sum := by decide
  have hdescent : baseEnd_4358527 < baseStart_4358527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358551 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 1, 4]
def baseStart_4358551 : Nat := 118140960795 + 4358551 * 2 ^ 59
def prefixEnd_4358551 : Nat := 4983230072969 + 3 ^ 40 * 4358551 * 2
def baseEnd_4358551 : Nat := 746010540044893960955965

theorem tailTrace_4358551 : CollatzResearch.WordTrace tailWord_4358551 prefixEnd_4358551 746010540044893960955965 := by
  unfold tailWord_4358551
  simp only [CollatzResearch.WordTrace]
  refine ⟨158969414832721583092691507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105979609888481055395127671 158969414832721583092691507)
  ·
    refine ⟨238454122249082374639037261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158969414832721583092691507 238454122249082374639037261)
    ·
      refine ⟨89420295843405890489638973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238454122249082374639037261 89420295843405890489638973)
      ·
        refine ⟨33532610941277208933614615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89420295843405890489638973 33532610941277208933614615)
        ·
          refine ⟨50298916411915813400421923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33532610941277208933614615 50298916411915813400421923)
          ·
            refine ⟨75448374617873720100632885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50298916411915813400421923 75448374617873720100632885)
            ·
              refine ⟨7073285120425661259434333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75448374617873720100632885 7073285120425661259434333)
              ·
                refine ⟨2652481920159622972287875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7073285120425661259434333 2652481920159622972287875)
                ·
                  refine ⟨3978722880239434458431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652481920159622972287875 3978722880239434458431813)
                  ·
                    refine ⟨746010540044893960955965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3978722880239434458431813 746010540044893960955965)
                    ·
                      rfl

theorem cell23_4358551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_4358551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358551 prefixEnd_4358551 := by exact prefixLift 4358551
  have htrace : WordTrace (prefixWord ++ tailWord_4358551) baseStart_4358551 baseEnd_4358551 := by
    simpa [prefixWord, tailWord_4358551, baseEnd_4358551] using wordTrace_append hprefix tailTrace_4358551
  have hstable : (prefixWord ++ tailWord_4358551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358551).length < 2 ^ (prefixWord ++ tailWord_4358551).sum := by decide
  have hdescent : baseEnd_4358551 < baseStart_4358551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358568 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4358568 : Nat := 118140960795 + 4358568 * 2 ^ 59
def prefixEnd_4358568 : Nat := 4983230072969 + 3 ^ 40 * 4358568 * 2
def baseEnd_4358568 : Nat := 746013449768602772118439

theorem tailTrace_4358568 : CollatzResearch.WordTrace tailWord_4358568 prefixEnd_4358568 746013449768602772118439 := by
  unfold tailWord_4358568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79485017436829997498030179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105980023249106663330706905 79485017436829997498030179)
  ·
    refine ⟨119227526155244996247045269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79485017436829997498030179 119227526155244996247045269)
    ·
      refine ⟨5588790288527109199080247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119227526155244996247045269 5588790288527109199080247)
      ·
        refine ⟨8383185432790663798620371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588790288527109199080247 8383185432790663798620371)
        ·
          refine ⟨12574778149185995697930557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8383185432790663798620371 12574778149185995697930557)
          ·
            refine ⟨4715541805944748386723959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12574778149185995697930557 4715541805944748386723959)
            ·
              refine ⟨7073312708917122580085939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715541805944748386723959 7073312708917122580085939)
              ·
                refine ⟨10609969063375683870128909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073312708917122580085939 10609969063375683870128909)
                ·
                  refine ⟨3978738398765881451298341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10609969063375683870128909 3978738398765881451298341)
                  ·
                    refine ⟨746013449768602772118439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3978738398765881451298341 746013449768602772118439)
                    ·
                      rfl

theorem cell23_4358568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4358568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358568 prefixEnd_4358568 := by exact prefixLift 4358568
  have htrace : WordTrace (prefixWord ++ tailWord_4358568) baseStart_4358568 baseEnd_4358568 := by
    simpa [prefixWord, tailWord_4358568, baseEnd_4358568] using wordTrace_append hprefix tailTrace_4358568
  have hstable : (prefixWord ++ tailWord_4358568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358568).length < 2 ^ (prefixWord ++ tailWord_4358568).sum := by decide
  have hdescent : baseEnd_4358568 < baseStart_4358568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358584 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_4358584 : Nat := 118140960795 + 4358584 * 2 ^ 59
def prefixEnd_4358584 : Nat := 4983230072969 + 3 ^ 40 * 4358584 * 2
def baseEnd_4358584 : Nat := 2238048564996280253755243

theorem tailTrace_4358584 : CollatzResearch.WordTrace tailWord_4358584 prefixEnd_4358584 2238048564996280253755243 := by
  unfold tailWord_4358584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79485309220801014864321403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105980412294401353152428537 79485309220801014864321403)
  ·
    refine ⟨119227963831201522296482105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79485309220801014864321403 119227963831201522296482105)
    ·
      refine ⟨89420972873401141722361579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119227963831201522296482105 89420972873401141722361579)
      ·
        refine ⟨134131459310101712583542369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89420972873401141722361579 134131459310101712583542369)
        ·
          refine ⟨100598594482576284437656777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134131459310101712583542369 100598594482576284437656777)
          ·
            refine ⟨75448945861932213328242583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100598594482576284437656777 75448945861932213328242583)
            ·
              refine ⟨113173418792898319992363875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75448945861932213328242583 113173418792898319992363875)
              ·
                refine ⟨169760128189347479988545813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113173418792898319992363875 169760128189347479988545813)
                ·
                  refine ⟨7957506008875663124463085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169760128189347479988545813 7957506008875663124463085)
                  ·
                    refine ⟨2984064753328373671673657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7957506008875663124463085 2984064753328373671673657)
                    ·
                      refine ⟨2238048564996280253755243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984064753328373671673657 2238048564996280253755243)
                      ·
                        rfl

theorem cell23_4358584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_4358584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358584 prefixEnd_4358584 := by exact prefixLift 4358584
  have htrace : WordTrace (prefixWord ++ tailWord_4358584) baseStart_4358584 baseEnd_4358584 := by
    simpa [prefixWord, tailWord_4358584, baseEnd_4358584] using wordTrace_append hprefix tailTrace_4358584
  have hstable : (prefixWord ++ tailWord_4358584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358584).length < 2 ^ (prefixWord ++ tailWord_4358584).sum := by decide
  have hdescent : baseEnd_4358584 < baseStart_4358584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358662 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4358662 : Nat := 118140960795 + 4358662 * 2 ^ 59
def prefixEnd_4358662 : Nat := 4983230072969 + 3 ^ 40 * 4358662 * 2
def baseEnd_4358662 : Nat := 746029538829110316193295

theorem tailTrace_4358662 : CollatzResearch.WordTrace tailWord_4358662 prefixEnd_4358662 746029538829110316193295 := by
  unfold tailWord_4358662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967920729228732782811945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105982308890212966033321493 4967920729228732782811945)
  ·
    refine ⟨3725940546921549587108959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4967920729228732782811945 3725940546921549587108959)
    ·
      refine ⟨5588910820382324380663439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3725940546921549587108959 5588910820382324380663439)
      ·
        refine ⟨8383366230573486570995159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5588910820382324380663439 8383366230573486570995159)
        ·
          refine ⟨12575049345860229856492739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8383366230573486570995159 12575049345860229856492739)
          ·
            refine ⟨18862574018790344784739109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12575049345860229856492739 18862574018790344784739109)
            ·
              refine ⟨3536732628523189647138583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18862574018790344784739109 3536732628523189647138583)
              ·
                refine ⟨5305098942784784470707875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536732628523189647138583 5305098942784784470707875)
                ·
                  refine ⟨7957648414177176706061813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305098942784784470707875 7957648414177176706061813)
                  ·
                    refine ⟨746029538829110316193295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7957648414177176706061813 746029538829110316193295)
                    ·
                      rfl

theorem cell23_4358662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4358662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358662 prefixEnd_4358662 := by exact prefixLift 4358662
  have htrace : WordTrace (prefixWord ++ tailWord_4358662) baseStart_4358662 baseEnd_4358662 := by
    simpa [prefixWord, tailWord_4358662, baseEnd_4358662] using wordTrace_append hprefix tailTrace_4358662
  have hstable : (prefixWord ++ tailWord_4358662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358662).length < 2 ^ (prefixWord ++ tailWord_4358662).sum := by decide
  have hdescent : baseEnd_4358662 < baseStart_4358662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358668 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4358668 : Nat := 118140960795 + 4358668 * 2 ^ 59
def prefixEnd_4358668 : Nat := 4983230072969 + 3 ^ 40 * 4358668 * 2
def baseEnd_4358668 : Nat := 2238091697371257925104857

theorem tailTrace_4358668 : CollatzResearch.WordTrace tailWord_4358668 prefixEnd_4358668 2238091697371257925104857 := by
  unfold tailWord_4358668
  simp only [CollatzResearch.WordTrace]
  refine ⟨79486841086648856037350329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105982454782198474716467105 79486841086648856037350329)
  ·
    refine ⟨59615130814986642028012747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79486841086648856037350329 59615130814986642028012747)
    ·
      refine ⟨89422696222479963042019121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59615130814986642028012747 89422696222479963042019121)
      ·
        refine ⟨67067022166859972281514341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89422696222479963042019121 67067022166859972281514341)
        ·
          refine ⟨12575066656286244802783939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67067022166859972281514341 12575066656286244802783939)
          ·
            refine ⟨18862599984429367204175909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12575066656286244802783939 18862599984429367204175909)
            ·
              refine ⟨3536737497080506350782983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18862599984429367204175909 3536737497080506350782983)
              ·
                refine ⟨5305106245620759526174475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536737497080506350782983 5305106245620759526174475)
                ·
                  refine ⟨7957659368431139289261713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305106245620759526174475 7957659368431139289261713)
                  ·
                    refine ⟨5968244526323354466946285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7957659368431139289261713 5968244526323354466946285)
                    ·
                      refine ⟨2238091697371257925104857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968244526323354466946285 2238091697371257925104857)
                      ·
                        rfl

theorem cell23_4358668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4358668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358668 prefixEnd_4358668 := by exact prefixLift 4358668
  have htrace : WordTrace (prefixWord ++ tailWord_4358668) baseStart_4358668 baseEnd_4358668 := by
    simpa [prefixWord, tailWord_4358668, baseEnd_4358668] using wordTrace_append hprefix tailTrace_4358668
  have hstable : (prefixWord ++ tailWord_4358668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358668).length < 2 ^ (prefixWord ++ tailWord_4358668).sum := by decide
  have hdescent : baseEnd_4358668 < baseStart_4358668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358695 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4358695 : Nat := 118140960795 + 4358695 * 2 ^ 59
def prefixEnd_4358695 : Nat := 4983230072969 + 3 ^ 40 * 4358695 * 2
def baseEnd_4358695 : Nat := 2238105561348929319467233

theorem tailTrace_4358695 : CollatzResearch.WordTrace tailWord_4358695 prefixEnd_4358695 2238105561348929319467233 := by
  unfold tailWord_4358695
  simp only [CollatzResearch.WordTrace]
  refine ⟨158974666944199895685933539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105983111296133263790622359 158974666944199895685933539)
  ·
    refine ⟨238462000416299843528900309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158974666944199895685933539 238462000416299843528900309)
    ·
      refine ⟨5588953134757027582708601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 238462000416299843528900309 5588953134757027582708601)
      ·
        refine ⟨4191714851067770687031451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5588953134757027582708601 4191714851067770687031451)
        ·
          refine ⟨6287572276601656030547177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191714851067770687031451 6287572276601656030547177)
          ·
            refine ⟨4715679207451242022910383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6287572276601656030547177 4715679207451242022910383)
            ·
              refine ⟨7073518811176863034365575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715679207451242022910383 7073518811176863034365575)
              ·
                refine ⟨10610278216765294551548363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073518811176863034365575 10610278216765294551548363)
                ·
                  refine ⟨15915417325147941827322545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10610278216765294551548363 15915417325147941827322545)
                  ·
                    refine ⟨11936562993860956370491909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15915417325147941827322545 11936562993860956370491909)
                    ·
                      refine ⟨2238105561348929319467233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11936562993860956370491909 2238105561348929319467233)
                      ·
                        rfl

theorem cell23_4358695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4358695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358695 prefixEnd_4358695 := by exact prefixLift 4358695
  have htrace : WordTrace (prefixWord ++ tailWord_4358695) baseStart_4358695 baseEnd_4358695 := by
    simpa [prefixWord, tailWord_4358695, baseEnd_4358695] using wordTrace_append hprefix tailTrace_4358695
  have hstable : (prefixWord ++ tailWord_4358695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358695).length < 2 ^ (prefixWord ++ tailWord_4358695).sum := by decide
  have hdescent : baseEnd_4358695 < baseStart_4358695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358698 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4358698 : Nat := 118140960795 + 4358698 * 2 ^ 59
def prefixEnd_4358698 : Nat := 4983230072969 + 3 ^ 40 * 4358698 * 2
def baseEnd_4358698 : Nat := 2238107101790892807729719

theorem tailTrace_4358698 : CollatzResearch.WordTrace tailWord_4358698 prefixEnd_4358698 2238107101790892807729719 := by
  unfold tailWord_4358698
  simp only [CollatzResearch.WordTrace]
  refine ⟨39743694090797256799573187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105983184242126018132195165 39743694090797256799573187)
  ·
    refine ⟨59615541136195885199359781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39743694090797256799573187 59615541136195885199359781)
    ·
      refine ⟨11177913963036728474879959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59615541136195885199359781 11177913963036728474879959)
      ·
        refine ⟨16766870944555092712319939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177913963036728474879959 16766870944555092712319939)
        ·
          refine ⟨25150306416832639068479909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16766870944555092712319939 25150306416832639068479909)
          ·
            refine ⟨4715682453156119825339983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25150306416832639068479909 4715682453156119825339983)
            ·
              refine ⟨7073523679734179738009975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715682453156119825339983 7073523679734179738009975)
              ·
                refine ⟨10610285519601269607014963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073523679734179738009975 10610285519601269607014963)
                ·
                  refine ⟨15915428279401904410522445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10610285519601269607014963 15915428279401904410522445)
                  ·
                    refine ⟨5968285604775714153945917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15915428279401904410522445 5968285604775714153945917)
                    ·
                      refine ⟨2238107101790892807729719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968285604775714153945917 2238107101790892807729719)
                      ·
                        rfl

theorem cell23_4358698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4358698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358698 prefixEnd_4358698 := by exact prefixLift 4358698
  have htrace : WordTrace (prefixWord ++ tailWord_4358698) baseStart_4358698 baseEnd_4358698 := by
    simpa [prefixWord, tailWord_4358698, baseEnd_4358698] using wordTrace_append hprefix tailTrace_4358698
  have hstable : (prefixWord ++ tailWord_4358698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358698).length < 2 ^ (prefixWord ++ tailWord_4358698).sum := by decide
  have hdescent : baseEnd_4358698 < baseStart_4358698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358734 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_4358734 : Nat := 118140960795 + 4358734 * 2 ^ 59
def prefixEnd_4358734 : Nat := 4983230072969 + 3 ^ 40 * 4358734 * 2
def baseEnd_4358734 : Nat := 2238125587094454666879553

theorem tailTrace_4358734 : CollatzResearch.WordTrace tailWord_4358734 prefixEnd_4358734 2238125587094454666879553 := by
  unfold tailWord_4358734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19872011173882325668325407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105984059594039070231068837 19872011173882325668325407)
  ·
    refine ⟨29808016760823488502488111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19872011173882325668325407 29808016760823488502488111)
    ·
      refine ⟨44712025141235232753732167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29808016760823488502488111 44712025141235232753732167)
      ·
        refine ⟨67068037711852849130598251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44712025141235232753732167 67068037711852849130598251)
        ·
          refine ⟨100602056567779273695897377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67068037711852849130598251 100602056567779273695897377)
          ·
            refine ⟨75451542425834455271923033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100602056567779273695897377 75451542425834455271923033)
            ·
              refine ⟨56588656819375841453942275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75451542425834455271923033 56588656819375841453942275)
              ·
                refine ⟨84882985229063762180913413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56588656819375841453942275 84882985229063762180913413)
                ·
                  refine ⟨15915559730449455408921265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84882985229063762180913413 15915559730449455408921265)
                  ·
                    refine ⟨11936669797837091556690949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15915559730449455408921265 11936669797837091556690949)
                    ·
                      refine ⟨2238125587094454666879553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11936669797837091556690949 2238125587094454666879553)
                      ·
                        rfl

theorem cell23_4358734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_4358734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358734 prefixEnd_4358734 := by exact prefixLift 4358734
  have htrace : WordTrace (prefixWord ++ tailWord_4358734) baseStart_4358734 baseEnd_4358734 := by
    simpa [prefixWord, tailWord_4358734, baseEnd_4358734] using wordTrace_append hprefix tailTrace_4358734
  have hstable : (prefixWord ++ tailWord_4358734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358734).length < 2 ^ (prefixWord ++ tailWord_4358734).sum := by decide
  have hdescent : baseEnd_4358734 < baseStart_4358734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358738 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_4358738 : Nat := 118140960795 + 4358738 * 2 ^ 59
def prefixEnd_4358738 : Nat := 4983230072969 + 3 ^ 40 * 4358738 * 2
def baseEnd_4358738 : Nat := 2238127641017072651229535

theorem tailTrace_4358738 : CollatzResearch.WordTrace tailWord_4358738 prefixEnd_4358738 2238127641017072651229535 := by
  unfold tailWord_4358738
  simp only [CollatzResearch.WordTrace]
  refine ⟨39744058820761028507437217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105984156855362742686499245 39744058820761028507437217)
  ·
    refine ⟨29808044115570771380577913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39744058820761028507437217 29808044115570771380577913)
    ·
      refine ⟨22356033086678078535433435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29808044115570771380577913 22356033086678078535433435)
      ·
        refine ⟨33534049630017117803150153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22356033086678078535433435 33534049630017117803150153)
        ·
          refine ⟨25150537222512838352362615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33534049630017117803150153 25150537222512838352362615)
          ·
            refine ⟨37725805833769257528543923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25150537222512838352362615 37725805833769257528543923)
            ·
              refine ⟨56588708750653886292815885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37725805833769257528543923 56588708750653886292815885)
              ·
                refine ⟨21220765781495207359805957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56588708750653886292815885 21220765781495207359805957)
                ·
                  refine ⟨3978893584030351379963617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21220765781495207359805957 3978893584030351379963617)
                  ·
                    refine ⟨2984170188022763534972713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3978893584030351379963617 2984170188022763534972713)
                    ·
                      refine ⟨2238127641017072651229535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984170188022763534972713 2238127641017072651229535)
                      ·
                        rfl

theorem cell23_4358738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_4358738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358738 prefixEnd_4358738 := by exact prefixLift 4358738
  have htrace : WordTrace (prefixWord ++ tailWord_4358738) baseStart_4358738 baseEnd_4358738 := by
    simpa [prefixWord, tailWord_4358738, baseEnd_4358738] using wordTrace_append hprefix tailTrace_4358738
  have hstable : (prefixWord ++ tailWord_4358738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358738).length < 2 ^ (prefixWord ++ tailWord_4358738).sum := by decide
  have hdescent : baseEnd_4358738 < baseStart_4358738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358744 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 7]
def baseStart_4358744 : Nat := 118140960795 + 4358744 * 2 ^ 59
def prefixEnd_4358744 : Nat := 4983230072969 + 3 ^ 40 * 4358744 * 2
def baseEnd_4358744 : Nat := 248681191322333291972723

theorem tailTrace_4358744 : CollatzResearch.WordTrace tailWord_4358744 prefixEnd_4358744 248681191322333291972723 := by
  unfold tailWord_4358744
  simp only [CollatzResearch.WordTrace]
  refine ⟨79488227060511188527233643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105984302747348251369644857 79488227060511188527233643)
  ·
    refine ⟨119232340590766782790850465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79488227060511188527233643 119232340590766782790850465)
    ·
      refine ⟨89424255443075087093137849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119232340590766782790850465 89424255443075087093137849)
      ·
        refine ⟨67068191582306315319853387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89424255443075087093137849 67068191582306315319853387)
        ·
          refine ⟨100602287373459472979780081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67068191582306315319853387 100602287373459472979780081)
          ·
            refine ⟨75451715530094604734835061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100602287373459472979780081 75451715530094604734835061)
            ·
              refine ⟨7073598330946369193890787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75451715530094604734835061 7073598330946369193890787)
              ·
                refine ⟨10610397496419553790836181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073598330946369193890787 10610397496419553790836181)
                ·
                  refine ⟨248681191322333291972723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10610397496419553790836181 248681191322333291972723)
                  ·
                    rfl

theorem cell23_4358744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_4358744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358744 prefixEnd_4358744 := by exact prefixLift 4358744
  have htrace : WordTrace (prefixWord ++ tailWord_4358744) baseStart_4358744 baseEnd_4358744 := by
    simpa [prefixWord, tailWord_4358744, baseEnd_4358744] using wordTrace_append hprefix tailTrace_4358744
  have hstable : (prefixWord ++ tailWord_4358744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358744).length < 2 ^ (prefixWord ++ tailWord_4358744).sum := by decide
  have hdescent : baseEnd_4358744 < baseStart_4358744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358784 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_4358784 : Nat := 118140960795 + 4358784 * 2 ^ 59
def prefixEnd_4358784 : Nat := 4983230072969 + 3 ^ 40 * 4358784 * 2
def baseEnd_4358784 : Nat := 2238151261127179471254323

theorem tailTrace_4358784 : CollatzResearch.WordTrace tailWord_4358784 prefixEnd_4358784 2238151261127179471254323 := by
  unfold tailWord_4358784
  simp only [CollatzResearch.WordTrace]
  refine ⟨79488956520438731942961703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105985275360584975923948937 79488956520438731942961703)
  ·
    refine ⟨119233434780658097914442555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79488956520438731942961703 119233434780658097914442555)
    ·
      refine ⟨178850152170987146871663833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119233434780658097914442555 178850152170987146871663833)
      ·
        refine ⟨134137614128240360153747875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178850152170987146871663833 134137614128240360153747875)
        ·
          refine ⟨201206421192360540230621813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134137614128240360153747875 201206421192360540230621813)
          ·
            refine ⟨18863101986783800646620795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201206421192360540230621813 18863101986783800646620795)
            ·
              refine ⟨28294652980175700969931193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18863101986783800646620795 28294652980175700969931193)
              ·
                refine ⟨21220989735131775727448395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28294652980175700969931193 21220989735131775727448395)
                ·
                  refine ⟨31831484602697663591172593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21220989735131775727448395 31831484602697663591172593)
                  ·
                    refine ⟨23873613452023247693379445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31831484602697663591172593 23873613452023247693379445)
                    ·
                      refine ⟨2238151261127179471254323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23873613452023247693379445 2238151261127179471254323)
                      ·
                        rfl

theorem cell23_4358784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_4358784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358784 prefixEnd_4358784 := by exact prefixLift 4358784
  have htrace : WordTrace (prefixWord ++ tailWord_4358784) baseStart_4358784 baseEnd_4358784 := by
    simpa [prefixWord, tailWord_4358784, baseEnd_4358784] using wordTrace_append hprefix tailTrace_4358784
  have hstable : (prefixWord ++ tailWord_4358784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358784).length < 2 ^ (prefixWord ++ tailWord_4358784).sum := by decide
  have hdescent : baseEnd_4358784 < baseStart_4358784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358831 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_4358831 : Nat := 118140960795 + 4358831 * 2 ^ 59
def prefixEnd_4358831 : Nat := 4983230072969 + 3 ^ 40 * 4358831 * 2
def baseEnd_4358831 : Nat := 2238175394717940787366607

theorem tailTrace_4358831 : CollatzResearch.WordTrace tailWord_4358831 prefixEnd_4358831 2238175394717940787366607 := by
  unfold tailWord_4358831
  simp only [CollatzResearch.WordTrace]
  refine ⟨158979627271707190912884347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105986418181138127275256231 158979627271707190912884347)
  ·
    refine ⟨238469440907560786369326521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158979627271707190912884347 238469440907560786369326521)
    ·
      refine ⟨178852080680670589776994891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238469440907560786369326521 178852080680670589776994891)
      ·
        refine ⟨268278121021005884665492337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178852080680670589776994891 268278121021005884665492337)
        ·
          refine ⟨201208590765754413499119253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268278121021005884665492337 201208590765754413499119253)
          ·
            refine ⟨9431652692144738132771215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201208590765754413499119253 9431652692144738132771215)
            ·
              refine ⟨14147479038217107199156823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9431652692144738132771215 14147479038217107199156823)
              ·
                refine ⟨21221218557325660798735235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14147479038217107199156823 21221218557325660798735235)
                ·
                  refine ⟨31831827835988491198102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21221218557325660798735235 31831827835988491198102853)
                  ·
                    refine ⟨5968467719247842099644285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31831827835988491198102853 5968467719247842099644285)
                    ·
                      refine ⟨2238175394717940787366607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968467719247842099644285 2238175394717940787366607)
                      ·
                        rfl

theorem cell23_4358831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_4358831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358831 prefixEnd_4358831 := by exact prefixLift 4358831
  have htrace : WordTrace (prefixWord ++ tailWord_4358831) baseStart_4358831 baseEnd_4358831 := by
    simpa [prefixWord, tailWord_4358831, baseEnd_4358831] using wordTrace_append hprefix tailTrace_4358831
  have hstable : (prefixWord ++ tailWord_4358831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358831).length < 2 ^ (prefixWord ++ tailWord_4358831).sum := by decide
  have hdescent : baseEnd_4358831 < baseStart_4358831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358834 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_4358834 : Nat := 118140960795 + 4358834 * 2 ^ 59
def prefixEnd_4358834 : Nat := 4983230072969 + 3 ^ 40 * 4358834 * 2
def baseEnd_4358834 : Nat := 248686326128878252847677

theorem tailTrace_4358834 : CollatzResearch.WordTrace tailWord_4358834 prefixEnd_4358834 248686326128878252847677 := by
  unfold tailWord_4358834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39744934172674080606310889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105986491127130881616829037 39744934172674080606310889)
  ·
    refine ⟨29808700629505560454733167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39744934172674080606310889 29808700629505560454733167)
    ·
      refine ⟨44713050944258340682099751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29808700629505560454733167 44713050944258340682099751)
      ·
        refine ⟨67069576416387511023149627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44713050944258340682099751 67069576416387511023149627)
        ·
          refine ⟨100604364624581266534724441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67069576416387511023149627 100604364624581266534724441)
          ·
            refine ⟨75453273468435949901043331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100604364624581266534724441 75453273468435949901043331)
            ·
              refine ⟨113179910202653924851564997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75453273468435949901043331 113179910202653924851564997)
              ·
                refine ⟨21221233162997610909668437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113179910202653924851564997 21221233162997610909668437)
                ·
                  refine ⟨248686326128878252847677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21221233162997610909668437 248686326128878252847677)
                  ·
                    rfl

theorem cell23_4358834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_4358834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358834 prefixEnd_4358834 := by exact prefixLift 4358834
  have htrace : WordTrace (prefixWord ++ tailWord_4358834) baseStart_4358834 baseEnd_4358834 := by
    simpa [prefixWord, tailWord_4358834, baseEnd_4358834] using wordTrace_append hprefix tailTrace_4358834
  have hstable : (prefixWord ++ tailWord_4358834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358834).length < 2 ^ (prefixWord ++ tailWord_4358834).sum := by decide
  have hdescent : baseEnd_4358834 < baseStart_4358834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358898 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_4358898 : Nat := 118140960795 + 4358898 * 2 ^ 59
def prefixEnd_4358898 : Nat := 4983230072969 + 3 ^ 40 * 4358898 * 2
def baseEnd_4358898 : Nat := 746069932640597341742933

theorem tailTrace_4358898 : CollatzResearch.WordTrace tailWord_4358898 prefixEnd_4358898 746069932640597341742933 := by
  unfold tailWord_4358898
  simp only [CollatzResearch.WordTrace]
  refine ⟨39745517740616115338893337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105988047308309640903715565 39745517740616115338893337)
  ·
    refine ⟨29809138305462086504170003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39745517740616115338893337 29809138305462086504170003)
    ·
      refine ⟨44713707458193129756255005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29809138305462086504170003 44713707458193129756255005)
      ·
        refine ⟨16767640296822423658595627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44713707458193129756255005 16767640296822423658595627)
        ·
          refine ⟨25151460445233635487893441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16767640296822423658595627 25151460445233635487893441)
          ·
            refine ⟨18863595333925226615920081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25151460445233635487893441 18863595333925226615920081)
            ·
              refine ⟨14147696500443919961940061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18863595333925226615920081 14147696500443919961940061)
              ·
                refine ⟨5305386187666469985727523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14147696500443919961940061 5305386187666469985727523)
                ·
                  refine ⟨7958079281499704978591285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305386187666469985727523 7958079281499704978591285)
                  ·
                    refine ⟨746069932640597341742933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7958079281499704978591285 746069932640597341742933)
                    ·
                      rfl

theorem cell23_4358898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_4358898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358898 prefixEnd_4358898 := by exact prefixLift 4358898
  have htrace : WordTrace (prefixWord ++ tailWord_4358898) baseStart_4358898 baseEnd_4358898 := by
    simpa [prefixWord, tailWord_4358898, baseEnd_4358898] using wordTrace_append hprefix tailTrace_4358898
  have hstable : (prefixWord ++ tailWord_4358898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358898).length < 2 ^ (prefixWord ++ tailWord_4358898).sum := by decide
  have hdescent : baseEnd_4358898 < baseStart_4358898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358921 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_4358921 : Nat := 118140960795 + 4358921 * 2 ^ 59
def prefixEnd_4358921 : Nat := 4983230072969 + 3 ^ 40 * 4358921 * 2
def baseEnd_4358921 : Nat := 2238221607976845435241193

theorem tailTrace_4358921 : CollatzResearch.WordTrace tailWord_4358921 prefixEnd_4358921 2238221607976845435241193 := by
  unfold tailWord_4358921
  simp only [CollatzResearch.WordTrace]
  refine ⟨158982909841381136283660617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105988606560920757522440411 158982909841381136283660617)
  ·
    refine ⟨119237182381035852212745463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158982909841381136283660617 119237182381035852212745463)
    ·
      refine ⟨178855773571553778319118195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119237182381035852212745463 178855773571553778319118195)
      ·
        refine ⟨268283660357330667478677293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178855773571553778319118195 268283660357330667478677293)
        ·
          refine ⟨100606372633999000304503985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268283660357330667478677293 100606372633999000304503985)
          ·
            refine ⟨75454779475499250228377989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100606372633999000304503985 75454779475499250228377989)
            ·
              refine ⟨14147771151656109417820873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75454779475499250228377989 14147771151656109417820873)
              ·
                refine ⟨10610828363742082063365655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14147771151656109417820873 10610828363742082063365655)
                ·
                  refine ⟨15916242545613123095048483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10610828363742082063365655 15916242545613123095048483)
                  ·
                    refine ⟨23874363818419684642572725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15916242545613123095048483 23874363818419684642572725)
                    ·
                      refine ⟨2238221607976845435241193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23874363818419684642572725 2238221607976845435241193)
                      ·
                        rfl

theorem cell23_4358921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_4358921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358921 prefixEnd_4358921 := by exact prefixLift 4358921
  have htrace : WordTrace (prefixWord ++ tailWord_4358921) baseStart_4358921 baseEnd_4358921 := by
    simpa [prefixWord, tailWord_4358921, baseEnd_4358921] using wordTrace_append hprefix tailTrace_4358921
  have hstable : (prefixWord ++ tailWord_4358921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358921).length < 2 ^ (prefixWord ++ tailWord_4358921).sum := by decide
  have hdescent : baseEnd_4358921 < baseStart_4358921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358931 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_4358931 : Nat := 118140960795 + 4358931 * 2 ^ 59
def prefixEnd_4358931 : Nat := 4983230072969 + 3 ^ 40 * 4358931 * 2
def baseEnd_4358931 : Nat := 2238226742783390396116147

theorem tailTrace_4358931 : CollatzResearch.WordTrace tailWord_4358931 prefixEnd_4358931 2238226742783390396116147 := by
  unfold tailWord_4358931
  simp only [CollatzResearch.WordTrace]
  refine ⟨158983274571344907991524647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105988849714229938661016431 158983274571344907991524647)
  ·
    refine ⟨238474911857017361987286971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158983274571344907991524647 238474911857017361987286971)
    ·
      refine ⟨357712367785526042980930457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238474911857017361987286971 357712367785526042980930457)
      ·
        refine ⟨268284275839144532235697843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357712367785526042980930457 268284275839144532235697843)
        ·
          refine ⟨402426413758716798353546765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268284275839144532235697843 402426413758716798353546765)
          ·
            refine ⟨150909905159518799382580037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402426413758716798353546765 150909905159518799382580037)
            ·
              refine ⟨28295607217409774884233757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150909905159518799382580037 28295607217409774884233757)
              ·
                refine ⟨10610852706528665581587659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28295607217409774884233757 10610852706528665581587659)
                ·
                  refine ⟨15916279059792998372381489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10610852706528665581587659 15916279059792998372381489)
                  ·
                    refine ⟨11937209294844748779286117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15916279059792998372381489 11937209294844748779286117)
                    ·
                      refine ⟨2238226742783390396116147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11937209294844748779286117 2238226742783390396116147)
                      ·
                        rfl

theorem cell23_4358931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_4358931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358931 prefixEnd_4358931 := by exact prefixLift 4358931
  have htrace : WordTrace (prefixWord ++ tailWord_4358931) baseStart_4358931 baseEnd_4358931 := by
    simpa [prefixWord, tailWord_4358931, baseEnd_4358931] using wordTrace_append hprefix tailTrace_4358931
  have hstable : (prefixWord ++ tailWord_4358931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358931).length < 2 ^ (prefixWord ++ tailWord_4358931).sum := by decide
  have hdescent : baseEnd_4358931 < baseStart_4358931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358938 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_4358938 : Nat := 118140960795 + 4358938 * 2 ^ 59
def prefixEnd_4358938 : Nat := 4983230072969 + 3 ^ 40 * 4358938 * 2
def baseEnd_4358938 : Nat := 2238230337147971868728615

theorem tailTrace_4358938 : CollatzResearch.WordTrace tailWord_4358938 prefixEnd_4358938 2238230337147971868728615 := by
  unfold tailWord_4358938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39745882470579887046757367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105989019921546365458019645 39745882470579887046757367)
  ·
    refine ⟨59618823705869830570136051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39745882470579887046757367 59618823705869830570136051)
    ·
      refine ⟨89428235558804745855204077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59618823705869830570136051 89428235558804745855204077)
      ·
        refine ⟨33535588334551779695701529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89428235558804745855204077 33535588334551779695701529)
        ·
          refine ⟨25151691250913834771776147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33535588334551779695701529 25151691250913834771776147)
          ·
            refine ⟨37727536876370752157664221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25151691250913834771776147 37727536876370752157664221)
            ·
              refine ⟨14147826328639032059124083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37727536876370752157664221 14147826328639032059124083)
              ·
                refine ⟨21221739492958548088686125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14147826328639032059124083 21221739492958548088686125)
                ·
                  refine ⟨7958152309859455533257297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21221739492958548088686125 7958152309859455533257297)
                  ·
                    refine ⟨5968614232394591649942973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7958152309859455533257297 5968614232394591649942973)
                    ·
                      refine ⟨2238230337147971868728615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968614232394591649942973 2238230337147971868728615)
                      ·
                        rfl

theorem cell23_4358938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_4358938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358938 prefixEnd_4358938 := by exact prefixLift 4358938
  have htrace : WordTrace (prefixWord ++ tailWord_4358938) baseStart_4358938 baseEnd_4358938 := by
    simpa [prefixWord, tailWord_4358938, baseEnd_4358938] using wordTrace_append hprefix tailTrace_4358938
  have hstable : (prefixWord ++ tailWord_4358938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358938).length < 2 ^ (prefixWord ++ tailWord_4358938).sum := by decide
  have hdescent : baseEnd_4358938 < baseStart_4358938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4358985 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 3]
def baseStart_4358985 : Nat := 118140960795 + 4358985 * 2 ^ 59
def prefixEnd_4358985 : Nat := 4983230072969 + 3 ^ 40 * 4358985 * 2
def baseEnd_4358985 : Nat := 2238254470738733184840899

theorem tailTrace_4358985 : CollatzResearch.WordTrace tailWord_4358985 prefixEnd_4358985 2238254470738733184840899 := by
  unfold tailWord_4358985
  simp only [CollatzResearch.WordTrace]
  refine ⟨158985244113149275213990409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105990162742099516809326939 158985244113149275213990409)
  ·
    refine ⟨119238933084861956410492807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158985244113149275213990409 119238933084861956410492807)
    ·
      refine ⟨178858399627292934615739211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119238933084861956410492807 178858399627292934615739211)
      ·
        refine ⟨268287599440939401923608817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178858399627292934615739211 268287599440939401923608817)
        ·
          refine ⟨201215699580704551442706613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268287599440939401923608817 201215699580704551442706613)
          ·
            refine ⟨18863971835691051697753745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201215699580704551442706613 18863971835691051697753745)
            ·
              refine ⟨14147978876768288773315309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18863971835691051697753745 14147978876768288773315309)
              ·
                refine ⟨5305492078788108289993241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14147978876768288773315309 5305492078788108289993241)
                ·
                  refine ⟨3979119059091081217494931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5305492078788108289993241 3979119059091081217494931)
                  ·
                    refine ⟨5968678588636621826242397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979119059091081217494931 5968678588636621826242397)
                    ·
                      refine ⟨2238254470738733184840899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968678588636621826242397 2238254470738733184840899)
                      ·
                        rfl

theorem cell23_4358985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_4358985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4358985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4358985 prefixEnd_4358985 := by exact prefixLift 4358985
  have htrace : WordTrace (prefixWord ++ tailWord_4358985) baseStart_4358985 baseEnd_4358985 := by
    simpa [prefixWord, tailWord_4358985, baseEnd_4358985] using wordTrace_append hprefix tailTrace_4358985
  have hstable : (prefixWord ++ tailWord_4358985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4358985).length < 2 ^ (prefixWord ++ tailWord_4358985).sum := by decide
  have hdescent : baseEnd_4358985 < baseStart_4358985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4358985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359012 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_4359012 : Nat := 118140960795 + 4359012 * 2 ^ 59
def prefixEnd_4359012 : Nat := 4983230072969 + 3 ^ 40 * 4359012 * 2
def baseEnd_4359012 : Nat := 2238268334716404579203275

theorem tailTrace_4359012 : CollatzResearch.WordTrace tailWord_4359012 prefixEnd_4359012 2238268334716404579203275 := by
  unfold tailWord_4359012
  simp only [CollatzResearch.WordTrace]
  refine ⟨79493114442025729412611645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105990819256034305883482193 79493114442025729412611645)
  ·
    refine ⟨29809917915759648529729367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79493114442025729412611645 29809917915759648529729367)
    ·
      refine ⟨44714876873639472794594051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29809917915759648529729367 44714876873639472794594051)
      ·
        refine ⟨67072315310459209191891077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44714876873639472794594051 67072315310459209191891077)
        ·
          refine ⟨12576059120711101723479577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67072315310459209191891077 12576059120711101723479577)
          ·
            refine ⟨9432044340533326292609683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12576059120711101723479577 9432044340533326292609683)
            ·
              refine ⟨14148066510799989438914525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432044340533326292609683 14148066510799989438914525)
              ·
                refine ⟨5305524941549996039592947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14148066510799989438914525 5305524941549996039592947)
                ·
                  refine ⟨7958287412324994059389421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305524941549996039592947 7958287412324994059389421)
                  ·
                    refine ⟨2984357779621872772271033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7958287412324994059389421 2984357779621872772271033)
                    ·
                      refine ⟨2238268334716404579203275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984357779621872772271033 2238268334716404579203275)
                      ·
                        rfl

theorem cell23_4359012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_4359012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359012 prefixEnd_4359012 := by exact prefixLift 4359012
  have htrace : WordTrace (prefixWord ++ tailWord_4359012) baseStart_4359012 baseEnd_4359012 := by
    simpa [prefixWord, tailWord_4359012, baseEnd_4359012] using wordTrace_append hprefix tailTrace_4359012
  have hstable : (prefixWord ++ tailWord_4359012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359012).length < 2 ^ (prefixWord ++ tailWord_4359012).sum := by decide
  have hdescent : baseEnd_4359012 < baseStart_4359012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359048 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 7]
def baseStart_4359048 : Nat := 118140960795 + 4359048 * 2 ^ 59
def prefixEnd_4359048 : Nat := 4983230072969 + 3 ^ 40 * 4359048 * 2
def baseEnd_4359048 : Nat := 248698535557774048705901

theorem tailTrace_4359048 : CollatzResearch.WordTrace tailWord_4359048 prefixEnd_4359048 248698535557774048705901 := by
  unfold tailWord_4359048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79493770955960518486766899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105991694607947357982355865 79493770955960518486766899)
  ·
    refine ⟨119240656433940777730150349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79493770955960518486766899 119240656433940777730150349)
    ·
      refine ⟨44715246162727791648806381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119240656433940777730150349 44715246162727791648806381)
      ·
        refine ⟨16768217311022921868302393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44715246162727791648806381 16768217311022921868302393)
        ·
          refine ⟨12576162983267191401226795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16768217311022921868302393 12576162983267191401226795)
          ·
            refine ⟨18864244474900787101840193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576162983267191401226795 18864244474900787101840193)
            ·
              refine ⟨14148183356175590326380145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18864244474900787101840193 14148183356175590326380145)
              ·
                refine ⟨10611137517131692744785109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14148183356175590326380145 10611137517131692744785109)
                ·
                  refine ⟨248698535557774048705901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10611137517131692744785109 248698535557774048705901)
                  ·
                    rfl

theorem cell23_4359048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_4359048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359048 prefixEnd_4359048 := by exact prefixLift 4359048
  have htrace : WordTrace (prefixWord ++ tailWord_4359048) baseStart_4359048 baseEnd_4359048 := by
    simpa [prefixWord, tailWord_4359048, baseEnd_4359048] using wordTrace_append hprefix tailTrace_4359048
  have hstable : (prefixWord ++ tailWord_4359048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359048).length < 2 ^ (prefixWord ++ tailWord_4359048).sum := by decide
  have hdescent : baseEnd_4359048 < baseStart_4359048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359062 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4359062 : Nat := 118140960795 + 4359062 * 2 ^ 59
def prefixEnd_4359062 : Nat := 4983230072969 + 3 ^ 40 * 4359062 * 2
def baseEnd_4359062 : Nat := 2238294008749129383578045

theorem tailTrace_4359062 : CollatzResearch.WordTrace tailWord_4359062 prefixEnd_4359062 2238294008749129383578045 := by
  unfold tailWord_4359062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936753283366894835283965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105992035022580211576362293 9936753283366894835283965)
  ·
    refine ⟨3726282481262585563231487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9936753283366894835283965 3726282481262585563231487)
    ·
      refine ⟨5589423721893878344847231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726282481262585563231487 5589423721893878344847231)
      ·
        refine ⟨8384135582840817517270847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589423721893878344847231 8384135582840817517270847)
        ·
          refine ⟨12576203374261226275906271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384135582840817517270847 12576203374261226275906271)
          ·
            refine ⟨18864305061391839413859407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576203374261226275906271 18864305061391839413859407)
            ·
              refine ⟨28296457592087759120789111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18864305061391839413859407 28296457592087759120789111)
              ·
                refine ⟨42444686388131638681183667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28296457592087759120789111 42444686388131638681183667)
                ·
                  refine ⟨63667029582197458021775501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42444686388131638681183667 63667029582197458021775501)
                  ·
                    refine ⟨23875136093324046758165813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63667029582197458021775501 23875136093324046758165813)
                    ·
                      refine ⟨2238294008749129383578045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23875136093324046758165813 2238294008749129383578045)
                      ·
                        rfl

theorem cell23_4359062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4359062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359062 prefixEnd_4359062 := by exact prefixLift 4359062
  have htrace : WordTrace (prefixWord ++ tailWord_4359062) baseStart_4359062 baseEnd_4359062 := by
    simpa [prefixWord, tailWord_4359062, baseEnd_4359062] using wordTrace_append hprefix tailTrace_4359062
  have hstable : (prefixWord ++ tailWord_4359062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359062).length < 2 ^ (prefixWord ++ tailWord_4359062).sum := by decide
  have hdescent : baseEnd_4359062 < baseStart_4359062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359091 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 8]
def baseStart_4359091 : Nat := 118140960795 + 4359091 * 2 ^ 59
def prefixEnd_4359091 : Nat := 4983230072969 + 3 ^ 40 * 4359091 * 2
def baseEnd_4359091 : Nat := 746102966562703256705137

theorem tailTrace_4359091 : CollatzResearch.WordTrace tailWord_4359091 prefixEnd_4359091 746102966562703256705137 := by
  unfold tailWord_4359091
  simp only [CollatzResearch.WordTrace]
  refine ⟨158989110250765255317349127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105992740167176836878232751 158989110250765255317349127)
  ·
    refine ⟨238483665376147882976023691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158989110250765255317349127 238483665376147882976023691)
    ·
      refine ⟨357725498064221824464035537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238483665376147882976023691 357725498064221824464035537)
      ·
        refine ⟨268294123548166368348026653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357725498064221824464035537 268294123548166368348026653)
        ·
          refine ⟨100610296330562388130509995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268294123548166368348026653 100610296330562388130509995)
          ·
            refine ⟨150915444495843582195764993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100610296330562388130509995 150915444495843582195764993)
            ·
              refine ⟨113186583371882686646823745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150915444495843582195764993 113186583371882686646823745)
              ·
                refine ⟨84889937528912014985117809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113186583371882686646823745 84889937528912014985117809)
                ·
                  refine ⟨63667453146684011238838357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84889937528912014985117809 63667453146684011238838357)
                  ·
                    refine ⟨746102966562703256705137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63667453146684011238838357 746102966562703256705137)
                    ·
                      rfl

theorem cell23_4359091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_4359091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359091 prefixEnd_4359091 := by exact prefixLift 4359091
  have htrace : WordTrace (prefixWord ++ tailWord_4359091) baseStart_4359091 baseEnd_4359091 := by
    simpa [prefixWord, tailWord_4359091, baseEnd_4359091] using wordTrace_append hprefix tailTrace_4359091
  have hstable : (prefixWord ++ tailWord_4359091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359091).length < 2 ^ (prefixWord ++ tailWord_4359091).sum := by decide
  have hdescent : baseEnd_4359091 < baseStart_4359091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359098 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_4359098 : Nat := 118140960795 + 4359098 * 2 ^ 59
def prefixEnd_4359098 : Nat := 4983230072969 + 3 ^ 40 * 4359098 * 2
def baseEnd_4359098 : Nat := 2238312494052691242727879

theorem tailTrace_4359098 : CollatzResearch.WordTrace tailWord_4359098 prefixEnd_4359098 2238312494052691242727879 := by
  unfold tailWord_4359098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39747341390434973878213487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105992910374493263675235965 39747341390434973878213487)
  ·
    refine ⟨59621012085652460817320231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39747341390434973878213487 59621012085652460817320231)
    ·
      refine ⟨89431518128478691225980347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59621012085652460817320231 89431518128478691225980347)
      ·
        refine ⟨134147277192718036838970521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89431518128478691225980347 134147277192718036838970521)
        ·
          refine ⟨100610457894538527629227891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134147277192718036838970521 100610457894538527629227891)
          ·
            refine ⟨150915686841807791443841837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100610457894538527629227891 150915686841807791443841837)
            ·
              refine ⟨56593382565677921791440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150915686841807791443841837 56593382565677921791440689)
              ·
                refine ⟨42445036924258441343580517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56593382565677921791440689 42445036924258441343580517)
                ·
                  refine ⟨7958444423298457751921347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42445036924258441343580517 7958444423298457751921347)
                  ·
                    refine ⟨11937666634947686627882021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7958444423298457751921347 11937666634947686627882021)
                    ·
                      refine ⟨2238312494052691242727879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11937666634947686627882021 2238312494052691242727879)
                      ·
                        rfl

theorem cell23_4359098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_4359098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359098 prefixEnd_4359098 := by exact prefixLift 4359098
  have htrace : WordTrace (prefixWord ++ tailWord_4359098) baseStart_4359098 baseEnd_4359098 := by
    simpa [prefixWord, tailWord_4359098, baseEnd_4359098] using wordTrace_append hprefix tailTrace_4359098
  have hstable : (prefixWord ++ tailWord_4359098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359098).length < 2 ^ (prefixWord ++ tailWord_4359098).sum := by decide
  have hdescent : baseEnd_4359098 < baseStart_4359098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359115 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4]
def baseStart_4359115 : Nat := 118140960795 + 4359115 * 2 ^ 59
def prefixEnd_4359115 : Nat := 4983230072969 + 3 ^ 40 * 4359115 * 2
def baseEnd_4359115 : Nat := 2238321223223817676215301

theorem tailTrace_4359115 : CollatzResearch.WordTrace tailWord_4359115 prefixEnd_4359115 2238321223223817676215301 := by
  unfold tailWord_4359115
  simp only [CollatzResearch.WordTrace]
  refine ⟨158989985602678307416222799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105993323735118871610815199 158989985602678307416222799)
  ·
    refine ⟨238484978404017461124334199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158989985602678307416222799 238484978404017461124334199)
    ·
      refine ⟨357727467606026191686501299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238484978404017461124334199 357727467606026191686501299)
      ·
        refine ⟨536591201409039287529751949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357727467606026191686501299 536591201409039287529751949)
        ·
          refine ⟨201221700528389732823656981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536591201409039287529751949 201221700528389732823656981)
          ·
            refine ⟨9432267212268268726108921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201221700528389732823656981 9432267212268268726108921)
            ·
              refine ⟨7074200409201201544581691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9432267212268268726108921 7074200409201201544581691)
              ·
                refine ⟨10611300613801802316872537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074200409201201544581691 10611300613801802316872537)
                ·
                  refine ⟨7958475460351351737654403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10611300613801802316872537 7958475460351351737654403)
                  ·
                    refine ⟨11937713190527027606481605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7958475460351351737654403 11937713190527027606481605)
                    ·
                      refine ⟨2238321223223817676215301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11937713190527027606481605 2238321223223817676215301)
                      ·
                        rfl

theorem cell23_4359115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].length) (baseStart_4359115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359115 prefixEnd_4359115 := by exact prefixLift 4359115
  have htrace : WordTrace (prefixWord ++ tailWord_4359115) baseStart_4359115 baseEnd_4359115 := by
    simpa [prefixWord, tailWord_4359115, baseEnd_4359115] using wordTrace_append hprefix tailTrace_4359115
  have hstable : (prefixWord ++ tailWord_4359115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359115).length < 2 ^ (prefixWord ++ tailWord_4359115).sum := by decide
  have hdescent : baseEnd_4359115 < baseStart_4359115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359148 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_4359148 : Nat := 118140960795 + 4359148 * 2 ^ 59
def prefixEnd_4359148 : Nat := 4983230072969 + 3 ^ 40 * 4359148 * 2
def baseEnd_4359148 : Nat := 2238338168085416047102649

theorem tailTrace_4359148 : CollatzResearch.WordTrace tailWord_4359148 prefixEnd_4359148 2238338168085416047102649 := by
  unfold tailWord_4359148
  simp only [CollatzResearch.WordTrace]
  refine ⟨79495594605779377026087049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105994126141039169368116065 79495594605779377026087049)
  ·
    refine ⟨59621695954334532769565287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79495594605779377026087049 59621695954334532769565287)
    ·
      refine ⟨89432543931501799154347931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59621695954334532769565287 89432543931501799154347931)
      ·
        refine ⟨134148815897252698731521897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89432543931501799154347931 134148815897252698731521897)
        ·
          refine ⟨100611611922939524048641423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134148815897252698731521897 100611611922939524048641423)
          ·
            refine ⟨150917417884409286072962135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100611611922939524048641423 150917417884409286072962135)
            ·
              refine ⟨226376126826613929109443203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150917417884409286072962135 226376126826613929109443203)
              ·
                refine ⟨339564190239920893664164805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226376126826613929109443203 339564190239920893664164805)
                ·
                  refine ⟨63668285669985167562030901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339564190239920893664164805 63668285669985167562030901)
                  ·
                    refine ⟨5968901781561109458940397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63668285669985167562030901 5968901781561109458940397)
                    ·
                      refine ⟨2238338168085416047102649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968901781561109458940397 2238338168085416047102649)
                      ·
                        rfl

theorem cell23_4359148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_4359148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359148 prefixEnd_4359148 := by exact prefixLift 4359148
  have htrace : WordTrace (prefixWord ++ tailWord_4359148) baseStart_4359148 baseEnd_4359148 := by
    simpa [prefixWord, tailWord_4359148, baseEnd_4359148] using wordTrace_append hprefix tailTrace_4359148
  have hstable : (prefixWord ++ tailWord_4359148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359148).length < 2 ^ (prefixWord ++ tailWord_4359148).sum := by decide
  have hdescent : baseEnd_4359148 < baseStart_4359148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359166 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4359166 : Nat := 118140960795 + 4359166 * 2 ^ 59
def prefixEnd_4359166 : Nat := 4983230072969 + 3 ^ 40 * 4359166 * 2
def baseEnd_4359166 : Nat := 2238347410737196976677567

theorem tailTrace_4359166 : CollatzResearch.WordTrace tailWord_4359166 prefixEnd_4359166 2238347410737196976677567 := by
  unfold tailWord_4359166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19873980715686692890791169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105994563816995695417552901 19873980715686692890791169)
  ·
    refine ⟨14905485536765019668093377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19873980715686692890791169 14905485536765019668093377)
    ·
      refine ⟨11179114152573764751070033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14905485536765019668093377 11179114152573764751070033)
      ·
        refine ⟨8384335614430323563302525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179114152573764751070033 8384335614430323563302525)
        ·
          refine ⟨3144125855411371336238447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8384335614430323563302525 3144125855411371336238447)
          ·
            refine ⟨4716188783117057004357671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144125855411371336238447 4716188783117057004357671)
            ·
              refine ⟨7074283174675585506536507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716188783117057004357671 7074283174675585506536507)
              ·
                refine ⟨10611424762013378259804761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074283174675585506536507 10611424762013378259804761)
                ·
                  refine ⟨7958568571510033694853571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10611424762013378259804761 7958568571510033694853571)
                  ·
                    refine ⟨11937852857265050542280357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7958568571510033694853571 11937852857265050542280357)
                    ·
                      refine ⟨2238347410737196976677567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11937852857265050542280357 2238347410737196976677567)
                      ·
                        rfl

theorem cell23_4359166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4359166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359166 prefixEnd_4359166 := by exact prefixLift 4359166
  have htrace : WordTrace (prefixWord ++ tailWord_4359166) baseStart_4359166 baseEnd_4359166 := by
    simpa [prefixWord, tailWord_4359166, baseEnd_4359166] using wordTrace_append hprefix tailTrace_4359166
  have hstable : (prefixWord ++ tailWord_4359166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359166).length < 2 ^ (prefixWord ++ tailWord_4359166).sum := by decide
  have hdescent : baseEnd_4359166 < baseStart_4359166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359199 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 1, 1, 3]
def baseStart_4359199 : Nat := 118140960795 + 4359199 * 2 ^ 59
def prefixEnd_4359199 : Nat := 4983230072969 + 3 ^ 40 * 4359199 * 2
def baseEnd_4359199 : Nat := 2238364355598795347564915

theorem tailTrace_4359199 : CollatzResearch.WordTrace tailWord_4359199 prefixEnd_4359199 2238364355598795347564915 := by
  unfold tailWord_4359199
  simp only [CollatzResearch.WordTrace]
  refine ⟨158993049334373989762280651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105995366222915993174853767 158993049334373989762280651)
  ·
    refine ⟨238489574001560984643420977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158993049334373989762280651 238489574001560984643420977)
    ·
      refine ⟨178867180501170738482565733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238489574001560984643420977 178867180501170738482565733)
      ·
        refine ⟨33537596343969513465481075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178867180501170738482565733 33537596343969513465481075)
        ·
          refine ⟨50306394515954270198221613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33537596343969513465481075 50306394515954270198221613)
          ·
            refine ⟨18864897943482851324333105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50306394515954270198221613 18864897943482851324333105)
            ·
              refine ⟨14148673457612138493249829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18864897943482851324333105 14148673457612138493249829)
              ·
                refine ⟨2652876273302275967484343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14148673457612138493249829 2652876273302275967484343)
                ·
                  refine ⟨3979314409953413951226515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652876273302275967484343 3979314409953413951226515)
                  ·
                    refine ⟨5968971614930120926839773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979314409953413951226515 5968971614930120926839773)
                    ·
                      refine ⟨2238364355598795347564915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5968971614930120926839773 2238364355598795347564915)
                      ·
                        rfl

theorem cell23_4359199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_4359199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359199 prefixEnd_4359199 := by exact prefixLift 4359199
  have htrace : WordTrace (prefixWord ++ tailWord_4359199) baseStart_4359199 baseEnd_4359199 := by
    simpa [prefixWord, tailWord_4359199, baseEnd_4359199] using wordTrace_append hprefix tailTrace_4359199
  have hstable : (prefixWord ++ tailWord_4359199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359199).length < 2 ^ (prefixWord ++ tailWord_4359199).sum := by decide
  have hdescent : baseEnd_4359199 < baseStart_4359199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359233 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4359233 : Nat := 118140960795 + 4359233 * 2 ^ 59
def prefixEnd_4359233 : Nat := 4983230072969 + 3 ^ 40 * 4359233 * 2
def baseEnd_4359233 : Nat := 2238381813941048214539759

theorem tailTrace_4359233 : CollatzResearch.WordTrace tailWord_4359233 prefixEnd_4359233 2238381813941048214539759 := by
  unfold tailWord_4359233
  simp only [CollatzResearch.WordTrace]
  refine ⟨158994289416250813569018353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105996192944167209046012235 158994289416250813569018353)
  ·
    refine ⟨119245717062188110176763765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158994289416250813569018353 119245717062188110176763765)
    ·
      refine ⟨11179285974580135329071603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119245717062188110176763765 11179285974580135329071603)
      ·
        refine ⟨16768928961870202993607405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179285974580135329071603 16768928961870202993607405)
        ·
          refine ⟨6288348360701326122602777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16768928961870202993607405 6288348360701326122602777)
          ·
            refine ⟨4716261270525994591952083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288348360701326122602777 4716261270525994591952083)
            ·
              refine ⟨7074391905788991887928125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716261270525994591952083 7074391905788991887928125)
              ·
                refine ⟨2652896964670871957973047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7074391905788991887928125 2652896964670871957973047)
                ·
                  refine ⟨3979345447006307936959571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2652896964670871957973047 3979345447006307936959571)
                  ·
                    refine ⟨5969018170509461905439357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979345447006307936959571 5969018170509461905439357)
                    ·
                      refine ⟨2238381813941048214539759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969018170509461905439357 2238381813941048214539759)
                      ·
                        rfl

theorem cell23_4359233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4359233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359233 prefixEnd_4359233 := by exact prefixLift 4359233
  have htrace : WordTrace (prefixWord ++ tailWord_4359233) baseStart_4359233 baseEnd_4359233 := by
    simpa [prefixWord, tailWord_4359233, baseEnd_4359233] using wordTrace_append hprefix tailTrace_4359233
  have hstable : (prefixWord ++ tailWord_4359233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359233).length < 2 ^ (prefixWord ++ tailWord_4359233).sum := by decide
  have hdescent : baseEnd_4359233 < baseStart_4359233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359242 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_4359242 : Nat := 118140960795 + 4359242 * 2 ^ 59
def prefixEnd_4359242 : Nat := 4983230072969 + 3 ^ 40 * 4359242 * 2
def baseEnd_4359242 : Nat := 2238386435266938679327217

theorem tailTrace_4359242 : CollatzResearch.WordTrace tailWord_4359242 prefixEnd_4359242 2238386435266938679327217 := by
  unfold tailWord_4359242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39748654418304552026523995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105996411782145472070730653 39748654418304552026523995)
  ·
    refine ⟨59622981627456828039785993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39748654418304552026523995 59622981627456828039785993)
    ·
      refine ⟨44717236220592621029839495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59622981627456828039785993 44717236220592621029839495)
      ·
        refine ⟨67075854330888931544759243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44717236220592621029839495 67075854330888931544759243)
        ·
          refine ⟨100613781496333397317138865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67075854330888931544759243 100613781496333397317138865)
          ·
            refine ⟨75460336122250047987854149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100613781496333397317138865 75460336122250047987854149)
            ·
              refine ⟨14148813022921883997722653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75460336122250047987854149 14148813022921883997722653)
              ·
                refine ⟨5305804883595706499145995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14148813022921883997722653 5305804883595706499145995)
                ·
                  refine ⟨7958707325393559748718993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305804883595706499145995 7958707325393559748718993)
                  ·
                    refine ⟨5969030494045169811539245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7958707325393559748718993 5969030494045169811539245)
                    ·
                      refine ⟨2238386435266938679327217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969030494045169811539245 2238386435266938679327217)
                      ·
                        rfl

theorem cell23_4359242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_4359242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359242 prefixEnd_4359242 := by exact prefixLift 4359242
  have htrace : WordTrace (prefixWord ++ tailWord_4359242) baseStart_4359242 baseEnd_4359242 := by
    simpa [prefixWord, tailWord_4359242, baseEnd_4359242] using wordTrace_append hprefix tailTrace_4359242
  have hstable : (prefixWord ++ tailWord_4359242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359242).length < 2 ^ (prefixWord ++ tailWord_4359242).sum := by decide
  have hdescent : baseEnd_4359242 < baseStart_4359242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359245 : List Nat := [1, 6, 1, 1, 1, 2, 11]
def baseStart_4359245 : Nat := 118140960795 + 4359245 * 2 ^ 59
def prefixEnd_4359245 : Nat := 4983230072969 + 3 ^ 40 * 4359245 * 2
def baseEnd_4359245 : Nat := 27634419453196323056663

theorem tailTrace_4359245 : CollatzResearch.WordTrace tailWord_4359245 prefixEnd_4359245 27634419453196323056663 := by
  unfold tailWord_4359245
  simp only [CollatzResearch.WordTrace]
  refine ⟨158994727092207339618455189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105996484728138226412303459 158994727092207339618455189)
  ·
    refine ⟨7452877832447219044615087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 158994727092207339618455189 7452877832447219044615087)
    ·
      refine ⟨11179316748670828566922631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7452877832447219044615087 11179316748670828566922631)
      ·
        refine ⟨16768975123006242850383947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179316748670828566922631 16768975123006242850383947)
        ·
          refine ⟨25153462684509364275575921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16768975123006242850383947 25153462684509364275575921)
          ·
            refine ⟨18865097013382023206681941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25153462684509364275575921 18865097013382023206681941)
            ·
              refine ⟨27634419453196323056663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18865097013382023206681941 27634419453196323056663)
              ·
                rfl

theorem cell23_4359245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 11].length) (baseStart_4359245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359245 prefixEnd_4359245 := by exact prefixLift 4359245
  have htrace : WordTrace (prefixWord ++ tailWord_4359245) baseStart_4359245 baseEnd_4359245 := by
    simpa [prefixWord, tailWord_4359245, baseEnd_4359245] using wordTrace_append hprefix tailTrace_4359245
  have hstable : (prefixWord ++ tailWord_4359245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359245).length < 2 ^ (prefixWord ++ tailWord_4359245).sum := by decide
  have hdescent : baseEnd_4359245 < baseStart_4359245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359266 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4359266 : Nat := 118140960795 + 4359266 * 2 ^ 59
def prefixEnd_4359266 : Nat := 4983230072969 + 3 ^ 40 * 4359266 * 2
def baseEnd_4359266 : Nat := 746132919600882195142369

theorem tailTrace_4359266 : CollatzResearch.WordTrace tailWord_4359266 prefixEnd_4359266 746132919600882195142369 := by
  unfold tailWord_4359266
  simp only [CollatzResearch.WordTrace]
  refine ⟨39748873256282815051242413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105996995350087506803313101 39748873256282815051242413)
  ·
    refine ⟨14905827471106055644215905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39748873256282815051242413 14905827471106055644215905)
    ·
      refine ⟨11179370603329541733161929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14905827471106055644215905 11179370603329541733161929)
      ·
        refine ⟨8384527952497156299871447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179370603329541733161929 8384527952497156299871447)
        ·
          refine ⟨12576791928745734449807171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384527952497156299871447 12576791928745734449807171)
          ·
            refine ⟨18865187893118601674710757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12576791928745734449807171 18865187893118601674710757)
            ·
              refine ⟨3537222729959737814008267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18865187893118601674710757 3537222729959737814008267)
              ·
                refine ⟨5305834094939606721012401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537222729959737814008267 5305834094939606721012401)
                ·
                  refine ⟨3979375571204705040759301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5305834094939606721012401 3979375571204705040759301)
                  ·
                    refine ⟨746132919600882195142369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979375571204705040759301 746132919600882195142369)
                    ·
                      rfl

theorem cell23_4359266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4359266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359266 prefixEnd_4359266 := by exact prefixLift 4359266
  have htrace : WordTrace (prefixWord ++ tailWord_4359266) baseStart_4359266 baseEnd_4359266 := by
    simpa [prefixWord, tailWord_4359266, baseEnd_4359266] using wordTrace_append hprefix tailTrace_4359266
  have hstable : (prefixWord ++ tailWord_4359266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359266).length < 2 ^ (prefixWord ++ tailWord_4359266).sum := by decide
  have hdescent : baseEnd_4359266 < baseStart_4359266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359315 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3]
def baseStart_4359315 : Nat := 118140960795 + 4359315 * 2 ^ 59
def prefixEnd_4359315 : Nat := 4983230072969 + 3 ^ 40 * 4359315 * 2
def baseEnd_4359315 : Nat := 2238423919354716893714381

theorem tailTrace_4359315 : CollatzResearch.WordTrace tailWord_4359315 prefixEnd_4359315 2238423919354716893714381 := by
  unfold tailWord_4359315
  simp only [CollatzResearch.WordTrace]
  refine ⟨158997280201953741573503399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105998186801302494382335599 158997280201953741573503399)
  ·
    refine ⟨238495920302930612360255099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158997280201953741573503399 238495920302930612360255099)
    ·
      refine ⟨357743880454395918540382649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238495920302930612360255099 357743880454395918540382649)
      ·
        refine ⟨268307910340796938905286987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357743880454395918540382649 268307910340796938905286987)
        ·
          refine ⟨402461865511195408357930481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268307910340796938905286987 402461865511195408357930481)
          ·
            refine ⟨301846399133396556268447861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402461865511195408357930481 301846399133396556268447861)
            ·
              refine ⟨28298099918755927150166987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 301846399133396556268447861 28298099918755927150166987)
              ·
                refine ⟨42447149878133890725250481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28298099918755927150166987 42447149878133890725250481)
                ·
                  refine ⟨31835362408600418043937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42447149878133890725250481 31835362408600418043937861)
                  ·
                    refine ⟨5969130451612578383238349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31835362408600418043937861 5969130451612578383238349)
                    ·
                      refine ⟨2238423919354716893714381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969130451612578383238349 2238423919354716893714381)
                      ·
                        rfl

theorem cell23_4359315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_4359315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359315 prefixEnd_4359315 := by exact prefixLift 4359315
  have htrace : WordTrace (prefixWord ++ tailWord_4359315) baseStart_4359315 baseEnd_4359315 := by
    simpa [prefixWord, tailWord_4359315, baseEnd_4359315] using wordTrace_append hprefix tailTrace_4359315
  have hstable : (prefixWord ++ tailWord_4359315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359315).length < 2 ^ (prefixWord ++ tailWord_4359315).sum := by decide
  have hdescent : baseEnd_4359315 < baseStart_4359315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359322 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_4359322 : Nat := 118140960795 + 4359322 * 2 ^ 59
def prefixEnd_4359322 : Nat := 4983230072969 + 3 ^ 40 * 4359322 * 2
def baseEnd_4359322 : Nat := 746142504573099455442283

theorem tailTrace_4359322 : CollatzResearch.WordTrace tailWord_4359322 prefixEnd_4359322 746142504573099455442283 := by
  unfold tailWord_4359322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39749383878232095442252055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105998357008618921179338813 39749383878232095442252055)
  ·
    refine ⟨59624075817348143163378083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39749383878232095442252055 59624075817348143163378083)
    ·
      refine ⟨89436113726022214745067125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59624075817348143163378083 89436113726022214745067125)
      ·
        refine ⟨8384635661814582632350043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89436113726022214745067125 8384635661814582632350043)
        ·
          refine ⟨12576953492721873948525065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384635661814582632350043 12576953492721873948525065)
          ·
            refine ⟨9432715119541405461393799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12576953492721873948525065 9432715119541405461393799)
            ·
              refine ⟨14149072679312108192090699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432715119541405461393799 14149072679312108192090699)
              ·
                refine ⟨21223609018968162288136049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14149072679312108192090699 21223609018968162288136049)
                ·
                  refine ⟨15917706764226121716102037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21223609018968162288136049 15917706764226121716102037)
                  ·
                    refine ⟨746142504573099455442283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15917706764226121716102037 746142504573099455442283)
                    ·
                      rfl

theorem cell23_4359322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_4359322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359322 prefixEnd_4359322 := by exact prefixLift 4359322
  have htrace : WordTrace (prefixWord ++ tailWord_4359322) baseStart_4359322 baseEnd_4359322 := by
    simpa [prefixWord, tailWord_4359322, baseEnd_4359322] using wordTrace_append hprefix tailTrace_4359322
  have hstable : (prefixWord ++ tailWord_4359322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359322).length < 2 ^ (prefixWord ++ tailWord_4359322).sum := by decide
  have hdescent : baseEnd_4359322 < baseStart_4359322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359329 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4359329 : Nat := 118140960795 + 4359329 * 2 ^ 59
def prefixEnd_4359329 : Nat := 4983230072969 + 3 ^ 40 * 4359329 * 2
def baseEnd_4359329 : Nat := 2238431108083879838939317

theorem tailTrace_4359329 : CollatzResearch.WordTrace tailWord_4359329 prefixEnd_4359329 2238431108083879838939317 := by
  unfold tailWord_4359329
  simp only [CollatzResearch.WordTrace]
  refine ⟨158997790823903021964513041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105998527215935347976342027 158997790823903021964513041)
  ·
    refine ⟨119248343117927266473384781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158997790823903021964513041 119248343117927266473384781)
    ·
      refine ⟨44718128669222724927519293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119248343117927266473384781 44718128669222724927519293)
      ·
        refine ⟨16769298250958521847819735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44718128669222724927519293 16769298250958521847819735)
        ·
          refine ⟨25153947376437782771729603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16769298250958521847819735 25153947376437782771729603)
          ·
            refine ⟨37730921064656674157594405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25153947376437782771729603 37730921064656674157594405)
            ·
              refine ⟨7074547699623126404548951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37730921064656674157594405 7074547699623126404548951)
              ·
                refine ⟨10611821549434689606823427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074547699623126404548951 10611821549434689606823427)
                ·
                  refine ⟨15917732324152034410235141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10611821549434689606823427 15917732324152034410235141)
                  ·
                    refine ⟨2984574810778506451919089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15917732324152034410235141 2984574810778506451919089)
                    ·
                      refine ⟨2238431108083879838939317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984574810778506451919089 2238431108083879838939317)
                      ·
                        rfl

theorem cell23_4359329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4359329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359329 prefixEnd_4359329 := by exact prefixLift 4359329
  have htrace : WordTrace (prefixWord ++ tailWord_4359329) baseStart_4359329 baseEnd_4359329 := by
    simpa [prefixWord, tailWord_4359329, baseEnd_4359329] using wordTrace_append hprefix tailTrace_4359329
  have hstable : (prefixWord ++ tailWord_4359329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359329).length < 2 ^ (prefixWord ++ tailWord_4359329).sum := by decide
  have hdescent : baseEnd_4359329 < baseStart_4359329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359350 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4359350 : Nat := 118140960795 + 4359350 * 2 ^ 59
def prefixEnd_4359350 : Nat := 4983230072969 + 3 ^ 40 * 4359350 * 2
def baseEnd_4359350 : Nat := 2238441891177624256776721

theorem tailTrace_4359350 : CollatzResearch.WordTrace tailWord_4359350 prefixEnd_4359350 2238441891177624256776721 := by
  unfold tailWord_4359350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937409797301683909439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105999037837884628367351669 9937409797301683909439219)
  ·
    refine ⟨14906114695952525864158829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9937409797301683909439219 14906114695952525864158829)
    ·
      refine ⟨5589793010982197199059561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14906114695952525864158829 5589793010982197199059561)
      ·
        refine ⟨4192344758236647899294671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5589793010982197199059561 4192344758236647899294671)
        ·
          refine ⟨6288517137354971848942007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192344758236647899294671 6288517137354971848942007)
          ·
            refine ⟨9432775706032457773413011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288517137354971848942007 9432775706032457773413011)
            ·
              refine ⟨14149163559048686660119517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9432775706032457773413011 14149163559048686660119517)
              ·
                refine ⟨5305936334643257497544819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14149163559048686660119517 5305936334643257497544819)
                ·
                  refine ⟨7958904501964886246317229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305936334643257497544819 7958904501964886246317229)
                  ·
                    refine ⟨2984589188236832342368961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7958904501964886246317229 2984589188236832342368961)
                    ·
                      refine ⟨2238441891177624256776721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984589188236832342368961 2238441891177624256776721)
                      ·
                        rfl

theorem cell23_4359350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4359350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359350 prefixEnd_4359350 := by exact prefixLift 4359350
  have htrace : WordTrace (prefixWord ++ tailWord_4359350) baseStart_4359350 baseEnd_4359350 := by
    simpa [prefixWord, tailWord_4359350, baseEnd_4359350] using wordTrace_append hprefix tailTrace_4359350
  have hstable : (prefixWord ++ tailWord_4359350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359350).length < 2 ^ (prefixWord ++ tailWord_4359350).sum := by decide
  have hdescent : baseEnd_4359350 < baseStart_4359350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359365 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_4359365 : Nat := 118140960795 + 4359365 * 2 ^ 59
def prefixEnd_4359365 : Nat := 4983230072969 + 3 ^ 40 * 4359365 * 2
def baseEnd_4359365 : Nat := 746149864462480566029717

theorem tailTrace_4359365 : CollatzResearch.WordTrace tailWord_4359365 prefixEnd_4359365 746149864462480566029717 := by
  unfold tailWord_4359365
  simp only [CollatzResearch.WordTrace]
  refine ⟨158999103851772600112823549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105999402567848400075215699 158999103851772600112823549)
  ·
    refine ⟨59624663944414725042308831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 158999103851772600112823549 59624663944414725042308831)
    ·
      refine ⟨89436995916622087563463247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59624663944414725042308831 89436995916622087563463247)
      ·
        refine ⟨134155493874933131345194871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89436995916622087563463247 134155493874933131345194871)
        ·
          refine ⟨201233240812399697017792307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134155493874933131345194871 201233240812399697017792307)
          ·
            refine ⟨301849861218599545526688461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201233240812399697017792307 301849861218599545526688461)
            ·
              refine ⟨113193697956974829572508173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301849861218599545526688461 113193697956974829572508173)
              ·
                refine ⟨42447636733865561089690565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113193697956974829572508173 42447636733865561089690565)
                ·
                  refine ⟨7958931887599792704316981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42447636733865561089690565 7958931887599792704316981)
                  ·
                    refine ⟨746149864462480566029717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7958931887599792704316981 746149864462480566029717)
                    ·
                      rfl

theorem cell23_4359365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_4359365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359365 prefixEnd_4359365 := by exact prefixLift 4359365
  have htrace : WordTrace (prefixWord ++ tailWord_4359365) baseStart_4359365 baseEnd_4359365 := by
    simpa [prefixWord, tailWord_4359365, baseEnd_4359365] using wordTrace_append hprefix tailTrace_4359365
  have hstable : (prefixWord ++ tailWord_4359365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359365).length < 2 ^ (prefixWord ++ tailWord_4359365).sum := by decide
  have hdescent : baseEnd_4359365 < baseStart_4359365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359380 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4359380 : Nat := 118140960795 + 4359380 * 2 ^ 59
def prefixEnd_4359380 : Nat := 4983230072969 + 3 ^ 40 * 4359380 * 2
def baseEnd_4359380 : Nat := 2238457295597259139401583

theorem tailTrace_4359380 : CollatzResearch.WordTrace tailWord_4359380 prefixEnd_4359380 2238457295597259139401583 := by
  unfold tailWord_4359380
  simp only [CollatzResearch.WordTrace]
  refine ⟨79499825473359128837309797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105999767297812171783079729 79499825473359128837309797)
  ·
    refine ⟨14906217276254836656995587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79499825473359128837309797 14906217276254836656995587)
    ·
      refine ⟨22359325914382254985493381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14906217276254836656995587 22359325914382254985493381)
      ·
        refine ⟨4192373608946672809780009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22359325914382254985493381 4192373608946672809780009)
        ·
          refine ⟨3144280206710004607335007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4192373608946672809780009 3144280206710004607335007)
          ·
            refine ⟨4716420310065006911002511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144280206710004607335007 4716420310065006911002511)
            ·
              refine ⟨7074630465097510366503767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716420310065006911002511 7074630465097510366503767)
              ·
                refine ⟨10611945697646265549755651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074630465097510366503767 10611945697646265549755651)
                ·
                  refine ⟨15917918546469398324633477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10611945697646265549755651 15917918546469398324633477)
                  ·
                    refine ⟨2984609727463012185868777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15917918546469398324633477 2984609727463012185868777)
                    ·
                      refine ⟨2238457295597259139401583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984609727463012185868777 2238457295597259139401583)
                      ·
                        rfl

theorem cell23_4359380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4359380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359380 prefixEnd_4359380 := by exact prefixLift 4359380
  have htrace : WordTrace (prefixWord ++ tailWord_4359380) baseStart_4359380 baseEnd_4359380 := by
    simpa [prefixWord, tailWord_4359380, baseEnd_4359380] using wordTrace_append hprefix tailTrace_4359380
  have hstable : (prefixWord ++ tailWord_4359380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359380).length < 2 ^ (prefixWord ++ tailWord_4359380).sum := by decide
  have hdescent : baseEnd_4359380 < baseStart_4359380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359402 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_4359402 : Nat := 118140960795 + 4359402 * 2 ^ 59
def prefixEnd_4359402 : Nat := 4983230072969 + 3 ^ 40 * 4359402 * 2
def baseEnd_4359402 : Nat := 2238468592171658053326481

theorem tailTrace_4359402 : CollatzResearch.WordTrace tailWord_4359402 prefixEnd_4359402 2238468592171658053326481 := by
  unfold tailWord_4359402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39750113338159638857980115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106000302235092370287946973 39750113338159638857980115)
  ·
    refine ⟨59625170007239458286970173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39750113338159638857980115 59625170007239458286970173)
    ·
      refine ⟨22359438752714796857613815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59625170007239458286970173 22359438752714796857613815)
      ·
        refine ⟨33539158129072195286420723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22359438752714796857613815 33539158129072195286420723)
        ·
          refine ⟨50308737193608292929631085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33539158129072195286420723 50308737193608292929631085)
          ·
            refine ⟨18865776447603109848611657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50308737193608292929631085 18865776447603109848611657)
            ·
              refine ⟨14149332335702332386458743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18865776447603109848611657 14149332335702332386458743)
              ·
                refine ⟨21223998503553498579688115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14149332335702332386458743 21223998503553498579688115)
                ·
                  refine ⟨31835997755330247869532173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21223998503553498579688115 31835997755330247869532173)
                  ·
                    refine ⟨11938499158248842951074565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31835997755330247869532173 11938499158248842951074565)
                    ·
                      refine ⟨2238468592171658053326481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11938499158248842951074565 2238468592171658053326481)
                      ·
                        rfl

theorem cell23_4359402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_4359402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359402 prefixEnd_4359402 := by exact prefixLift 4359402
  have htrace : WordTrace (prefixWord ++ tailWord_4359402) baseStart_4359402 baseEnd_4359402 := by
    simpa [prefixWord, tailWord_4359402, baseEnd_4359402] using wordTrace_append hprefix tailTrace_4359402
  have hstable : (prefixWord ++ tailWord_4359402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359402).length < 2 ^ (prefixWord ++ tailWord_4359402).sum := by decide
  have hdescent : baseEnd_4359402 < baseStart_4359402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359415 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_4359415 : Nat := 118140960795 + 4359415 * 2 ^ 59
def prefixEnd_4359415 : Nat := 4983230072969 + 3 ^ 40 * 4359415 * 2
def baseEnd_4359415 : Nat := 2238475267420166502463921

theorem tailTrace_4359415 : CollatzResearch.WordTrace tailWord_4359415 prefixEnd_4359415 2238475267420166502463921 := by
  unfold tailWord_4359415
  simp only [CollatzResearch.WordTrace]
  refine ⟨159000927501591458652143699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106000618334394305768095799 159000927501591458652143699)
  ·
    refine ⟨238501391252387187978215549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159000927501591458652143699 238501391252387187978215549)
    ·
      refine ⟨89438021719645195491830831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238501391252387187978215549 89438021719645195491830831)
      ·
        refine ⟨134157032579467793237746247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89438021719645195491830831 134157032579467793237746247)
        ·
          refine ⟨201235548869201689856619371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134157032579467793237746247 201235548869201689856619371)
          ·
            refine ⟨301853323303802534784929057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201235548869201689856619371 301853323303802534784929057)
            ·
              refine ⟨226389992477851901088696793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301853323303802534784929057 226389992477851901088696793)
              ·
                refine ⟨169792494358388925816522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226389992477851901088696793 169792494358388925816522595)
                ·
                  refine ⟨254688741537583388724783893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169792494358388925816522595 254688741537583388724783893)
                  ·
                    refine ⟨11938534759574221346474245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 254688741537583388724783893 11938534759574221346474245)
                    ·
                      refine ⟨2238475267420166502463921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11938534759574221346474245 2238475267420166502463921)
                      ·
                        rfl

theorem cell23_4359415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_4359415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359415 prefixEnd_4359415 := by exact prefixLift 4359415
  have htrace : WordTrace (prefixWord ++ tailWord_4359415) baseStart_4359415 baseEnd_4359415 := by
    simpa [prefixWord, tailWord_4359415, baseEnd_4359415] using wordTrace_append hprefix tailTrace_4359415
  have hstable : (prefixWord ++ tailWord_4359415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359415).length < 2 ^ (prefixWord ++ tailWord_4359415).sum := by decide
  have hdescent : baseEnd_4359415 < baseStart_4359415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359452 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4359452 : Nat := 118140960795 + 4359452 * 2 ^ 59
def prefixEnd_4359452 : Nat := 4983230072969 + 3 ^ 40 * 4359452 * 2
def baseEnd_4359452 : Nat := 2238494266204382857701251

theorem tailTrace_4359452 : CollatzResearch.WordTrace tailWord_4359452 prefixEnd_4359452 2238494266204382857701251 := by
  unfold tailWord_4359452
  simp only [CollatzResearch.WordTrace]
  refine ⟨79501138501228706985620305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106001518001638275980827073 79501138501228706985620305)
  ·
    refine ⟨59625853875921530239215229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79501138501228706985620305 59625853875921530239215229)
    ·
      refine ⟨22359695203470573839705711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59625853875921530239215229 22359695203470573839705711)
      ·
        refine ⟨33539542805205860759558567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22359695203470573839705711 33539542805205860759558567)
        ·
          refine ⟨50309314207808791139337851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33539542805205860759558567 50309314207808791139337851)
          ·
            refine ⟨75463971311713186709006777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50309314207808791139337851 75463971311713186709006777)
            ·
              refine ⟨56597978483784890031755083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75463971311713186709006777 56597978483784890031755083)
              ·
                refine ⟨84896967725677335047632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56597978483784890031755083 84896967725677335047632625)
                ·
                  refine ⟨63672725794258001285724469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84896967725677335047632625 63672725794258001285724469)
                  ·
                    refine ⟨5969318043211687620536669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63672725794258001285724469 5969318043211687620536669)
                    ·
                      refine ⟨2238494266204382857701251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969318043211687620536669 2238494266204382857701251)
                      ·
                        rfl

theorem cell23_4359452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4359452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359452 prefixEnd_4359452 := by exact prefixLift 4359452
  have htrace : WordTrace (prefixWord ++ tailWord_4359452) baseStart_4359452 baseEnd_4359452 := by
    simpa [prefixWord, tailWord_4359452, baseEnd_4359452] using wordTrace_append hprefix tailTrace_4359452
  have hstable : (prefixWord ++ tailWord_4359452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359452).length < 2 ^ (prefixWord ++ tailWord_4359452).sum := by decide
  have hdescent : baseEnd_4359452 < baseStart_4359452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359456 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4359456 : Nat := 118140960795 + 4359456 * 2 ^ 59
def prefixEnd_4359456 : Nat := 4983230072969 + 3 ^ 40 * 4359456 * 2
def baseEnd_4359456 : Nat := 2238496320127000842051233

theorem tailTrace_4359456 : CollatzResearch.WordTrace tailWord_4359456 prefixEnd_4359456 2238496320127000842051233 := by
  unfold tailWord_4359456
  simp only [CollatzResearch.WordTrace]
  refine ⟨79501211447221461327193111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106001615262961948436257481 79501211447221461327193111)
  ·
    refine ⟨119251817170832191990789667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79501211447221461327193111 119251817170832191990789667)
    ·
      refine ⟨178877725756248287986184501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119251817170832191990789667 178877725756248287986184501)
      ·
        refine ⟨16769786789648276998704797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178877725756248287986184501 16769786789648276998704797)
        ·
          refine ⟨6288670046118103874514299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16769786789648276998704797 6288670046118103874514299)
          ·
            refine ⟨9433005069177155811771449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288670046118103874514299 9433005069177155811771449)
            ·
              refine ⟨7074753801882866858828587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9433005069177155811771449 7074753801882866858828587)
              ·
                refine ⟨10612130702824300288242881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074753801882866858828587 10612130702824300288242881)
                ·
                  refine ⟨7959098027118225216182161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10612130702824300288242881 7959098027118225216182161)
                  ·
                    refine ⟨5969323520338668912136621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7959098027118225216182161 5969323520338668912136621)
                    ·
                      refine ⟨2238496320127000842051233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969323520338668912136621 2238496320127000842051233)
                      ·
                        rfl

theorem cell23_4359456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4359456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359456 prefixEnd_4359456 := by exact prefixLift 4359456
  have htrace : WordTrace (prefixWord ++ tailWord_4359456) baseStart_4359456 baseEnd_4359456 := by
    simpa [prefixWord, tailWord_4359456, baseEnd_4359456] using wordTrace_append hprefix tailTrace_4359456
  have hstable : (prefixWord ++ tailWord_4359456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359456).length < 2 ^ (prefixWord ++ tailWord_4359456).sum := by decide
  have hdescent : baseEnd_4359456 < baseStart_4359456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359486 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_4359486 : Nat := 118140960795 + 4359486 * 2 ^ 59
def prefixEnd_4359486 : Nat := 4983230072969 + 3 ^ 40 * 4359486 * 2
def baseEnd_4359486 : Nat := 2238511724546635724676095

theorem tailTrace_4359486 : CollatzResearch.WordTrace tailWord_4359486 prefixEnd_4359486 2238511724546635724676095 := by
  unfold tailWord_4359486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19875439635541779722247289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106002344722889491851985541 19875439635541779722247289)
  ·
    refine ⟨14906579726656334791685467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19875439635541779722247289 14906579726656334791685467)
    ·
      refine ⟨22359869589984502187528201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14906579726656334791685467 22359869589984502187528201)
      ·
        refine ⟨16769902192488376640646151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22359869589984502187528201 16769902192488376640646151)
        ·
          refine ⟨25154853288732564960969227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16769902192488376640646151 25154853288732564960969227)
          ·
            refine ⟨37732279933098847441453841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25154853288732564960969227 37732279933098847441453841)
            ·
              refine ⟨28299209949824135581090381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37732279933098847441453841 28299209949824135581090381)
              ·
                refine ⟨10612203731184050842908893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28299209949824135581090381 10612203731184050842908893)
                ·
                  refine ⟨3979576399194019066090835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10612203731184050842908893 3979576399194019066090835)
                  ·
                    refine ⟨5969364598791028599136253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979576399194019066090835 5969364598791028599136253)
                    ·
                      refine ⟨2238511724546635724676095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969364598791028599136253 2238511724546635724676095)
                      ·
                        rfl

theorem cell23_4359486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_4359486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359486 prefixEnd_4359486 := by exact prefixLift 4359486
  have htrace : WordTrace (prefixWord ++ tailWord_4359486) baseStart_4359486 baseEnd_4359486 := by
    simpa [prefixWord, tailWord_4359486, baseEnd_4359486] using wordTrace_append hprefix tailTrace_4359486
  have hstable : (prefixWord ++ tailWord_4359486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359486).length < 2 ^ (prefixWord ++ tailWord_4359486).sum := by decide
  have hdescent : baseEnd_4359486 < baseStart_4359486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359489 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4359489 : Nat := 118140960795 + 4359489 * 2 ^ 59
def prefixEnd_4359489 : Nat := 4983230072969 + 3 ^ 40 * 4359489 * 2
def baseEnd_4359489 : Nat := 746171088329533070979527

theorem tailTrace_4359489 : CollatzResearch.WordTrace tailWord_4359489 prefixEnd_4359489 746171088329533070979527 := by
  unfold tailWord_4359489
  simp only [CollatzResearch.WordTrace]
  refine ⟨159003626503323369290337521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106002417668882246193558347 159003626503323369290337521)
  ·
    refine ⟨119252719877492526967753141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159003626503323369290337521 119252719877492526967753141)
    ·
      refine ⟨11179942488514924403226857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119252719877492526967753141 11179942488514924403226857)
      ·
        refine ⟨8384956866386193302420143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179942488514924403226857 8384956866386193302420143)
        ·
          refine ⟨12577435299579289953630215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384956866386193302420143 12577435299579289953630215)
          ·
            refine ⟨18866152949368934930445323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577435299579289953630215 18866152949368934930445323)
            ·
              refine ⟨28299229424053402395667985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18866152949368934930445323 28299229424053402395667985)
              ·
                refine ⟨21224422068040051796750989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28299229424053402395667985 21224422068040051796750989)
                ·
                  refine ⟨7959158275515019423781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21224422068040051796750989 7959158275515019423781621)
                  ·
                    refine ⟨746171088329533070979527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7959158275515019423781621 746171088329533070979527)
                    ·
                      rfl

theorem cell23_4359489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4359489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359489 prefixEnd_4359489 := by exact prefixLift 4359489
  have htrace : WordTrace (prefixWord ++ tailWord_4359489) baseStart_4359489 baseEnd_4359489 := by
    simpa [prefixWord, tailWord_4359489, baseEnd_4359489] using wordTrace_append hprefix tailTrace_4359489
  have hstable : (prefixWord ++ tailWord_4359489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359489).length < 2 ^ (prefixWord ++ tailWord_4359489).sum := by decide
  have hdescent : baseEnd_4359489 < baseStart_4359489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359509 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4359509 : Nat := 118140960795 + 4359509 * 2 ^ 59
def prefixEnd_4359509 : Nat := 4983230072969 + 3 ^ 40 * 4359509 * 2
def baseEnd_4359509 : Nat := 2238523534601689134688489

theorem tailTrace_4359509 : CollatzResearch.WordTrace tailWord_4359509 prefixEnd_4359509 2238523534601689134688489 := by
  unfold tailWord_4359509
  simp only [CollatzResearch.WordTrace]
  refine ⟨159004355963250912706065581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106002903975500608470710387 159004355963250912706065581)
  ·
    refine ⟨59626633486219092264774593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159004355963250912706065581 59626633486219092264774593)
    ·
      refine ⟨44719975114664319198580945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59626633486219092264774593 44719975114664319198580945)
      ·
        refine ⟨33539981335998239398935709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44719975114664319198580945 33539981335998239398935709)
        ·
          refine ⟨12577493000999339774600891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33539981335998239398935709 12577493000999339774600891)
          ·
            refine ⟨18866239501499009661901337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577493000999339774600891 18866239501499009661901337)
            ·
              refine ⟨14149679626124257246426003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18866239501499009661901337 14149679626124257246426003)
              ·
                refine ⟨21224519439186385869639005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14149679626124257246426003 21224519439186385869639005)
                ·
                  refine ⟨7959194789694894701114627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21224519439186385869639005 7959194789694894701114627)
                  ·
                    refine ⟨11938792184542342051671941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7959194789694894701114627 11938792184542342051671941)
                    ·
                      refine ⟨2238523534601689134688489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11938792184542342051671941 2238523534601689134688489)
                      ·
                        rfl

theorem cell23_4359509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4359509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359509 prefixEnd_4359509 := by exact prefixLift 4359509
  have htrace : WordTrace (prefixWord ++ tailWord_4359509) baseStart_4359509 baseEnd_4359509 := by
    simpa [prefixWord, tailWord_4359509, baseEnd_4359509] using wordTrace_append hprefix tailTrace_4359509
  have hstable : (prefixWord ++ tailWord_4359509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359509).length < 2 ^ (prefixWord ++ tailWord_4359509).sum := by decide
  have hdescent : baseEnd_4359509 < baseStart_4359509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359532 : List Nat := [2, 2, 1, 1, 5, 2, 10]
def baseStart_4359532 : Nat := 118140960795 + 4359532 * 2 ^ 59
def prefixEnd_4359532 : Nat := 4983230072969 + 3 ^ 40 * 4359532 * 2
def baseEnd_4359532 : Nat := 27636238822922747465443

theorem tailTrace_4359532 : CollatzResearch.WordTrace tailWord_4359532 prefixEnd_4359532 27636238822922747465443 := by
  unfold tailWord_4359532
  simp only [CollatzResearch.WordTrace]
  refine ⟨79502597421083793817076425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106003463228111725089435233 79502597421083793817076425)
  ·
    refine ⟨59626948065812845362807319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79502597421083793817076425 59626948065812845362807319)
    ·
      refine ⟨89440422098719268044210979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59626948065812845362807319 89440422098719268044210979)
      ·
        refine ⟨134160633148078902066316469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89440422098719268044210979 134160633148078902066316469)
        ·
          refine ⟨12577559357632397068717169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134160633148078902066316469 12577559357632397068717169)
          ·
            refine ⟨9433169518224297801537877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12577559357632397068717169 9433169518224297801537877)
            ·
              refine ⟨27636238822922747465443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9433169518224297801537877 27636238822922747465443)
              ·
                rfl

theorem cell23_4359532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 10].length) (baseStart_4359532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359532 prefixEnd_4359532 := by exact prefixLift 4359532
  have htrace : WordTrace (prefixWord ++ tailWord_4359532) baseStart_4359532 baseEnd_4359532 := by
    simpa [prefixWord, tailWord_4359532, baseEnd_4359532] using wordTrace_append hprefix tailTrace_4359532
  have hstable : (prefixWord ++ tailWord_4359532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359532).length < 2 ^ (prefixWord ++ tailWord_4359532).sum := by decide
  have hdescent : baseEnd_4359532 < baseStart_4359532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359543 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_4359543 : Nat := 118140960795 + 4359543 * 2 ^ 59
def prefixEnd_4359543 : Nat := 4983230072969 + 3 ^ 40 * 4359543 * 2
def baseEnd_4359543 : Nat := 2238540992943942001663333

theorem tailTrace_4359543 : CollatzResearch.WordTrace tailWord_4359543 prefixEnd_4359543 2238540992943942001663333 := by
  unfold tailWord_4359543
  simp only [CollatzResearch.WordTrace]
  refine ⟨159005596045127736512803283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106003730696751824341868855 159005596045127736512803283)
  ·
    refine ⟨238508394067691604769204925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159005596045127736512803283 238508394067691604769204925)
    ·
      refine ⟨89440647775384351788451847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238508394067691604769204925 89440647775384351788451847)
      ·
        refine ⟨134160971663076527682677771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89440647775384351788451847 134160971663076527682677771)
        ·
          refine ⟨201241457494614791524016657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134160971663076527682677771 201241457494614791524016657)
          ·
            refine ⟨150931093120961093643012493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201241457494614791524016657 150931093120961093643012493)
            ·
              refine ⟨56599159920360410116129685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150931093120961093643012493 56599159920360410116129685)
              ·
                refine ⟨2653085621266894224193579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56599159920360410116129685 2653085621266894224193579)
                ·
                  refine ⟨3979628431900341336290369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653085621266894224193579 3979628431900341336290369)
                  ·
                    refine ⟨2984721323925256002217777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3979628431900341336290369 2984721323925256002217777)
                    ·
                      refine ⟨2238540992943942001663333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984721323925256002217777 2238540992943942001663333)
                      ·
                        rfl

theorem cell23_4359543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_4359543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359543 prefixEnd_4359543 := by exact prefixLift 4359543
  have htrace : WordTrace (prefixWord ++ tailWord_4359543) baseStart_4359543 baseEnd_4359543 := by
    simpa [prefixWord, tailWord_4359543, baseEnd_4359543] using wordTrace_append hprefix tailTrace_4359543
  have hstable : (prefixWord ++ tailWord_4359543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359543).length < 2 ^ (prefixWord ++ tailWord_4359543).sum := by decide
  have hdescent : baseEnd_4359543 < baseStart_4359543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359553 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4359553 : Nat := 118140960795 + 4359553 * 2 ^ 59
def prefixEnd_4359553 : Nat := 4983230072969 + 3 ^ 40 * 4359553 * 2
def baseEnd_4359553 : Nat := 746182042583495654179429

theorem tailTrace_4359553 : CollatzResearch.WordTrace tailWord_4359553 prefixEnd_4359553 746182042583495654179429 := by
  unfold tailWord_4359553
  simp only [CollatzResearch.WordTrace]
  refine ⟨159005960775091508220667313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106003973850061005480444875 159005960775091508220667313)
  ·
    refine ⟨119254470581318631165500485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159005960775091508220667313 119254470581318631165500485)
    ·
      refine ⟨22360213233997243343531341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119254470581318631165500485 22360213233997243343531341)
      ·
        refine ⟨8385079962748966253824253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22360213233997243343531341 8385079962748966253824253)
        ·
          refine ⟨3144404986030862345184095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8385079962748966253824253 3144404986030862345184095)
          ·
            refine ⟨4716607479046293517776143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144404986030862345184095 4716607479046293517776143)
            ·
              refine ⟨7074911218569440276664215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716607479046293517776143 7074911218569440276664215)
              ·
                refine ⟨10612366827854160414996323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074911218569440276664215 10612366827854160414996323)
                ·
                  refine ⟨15918550241781240622494485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10612366827854160414996323 15918550241781240622494485)
                  ·
                    refine ⟨746182042583495654179429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15918550241781240622494485 746182042583495654179429)
                    ·
                      rfl

theorem cell23_4359553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4359553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359553 prefixEnd_4359553 := by exact prefixLift 4359553
  have htrace : WordTrace (prefixWord ++ tailWord_4359553) baseStart_4359553 baseEnd_4359553 := by
    simpa [prefixWord, tailWord_4359553, baseEnd_4359553] using wordTrace_append hprefix tailTrace_4359553
  have hstable : (prefixWord ++ tailWord_4359553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359553).length < 2 ^ (prefixWord ++ tailWord_4359553).sum := by decide
  have hdescent : baseEnd_4359553 < baseStart_4359553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359556 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_4359556 : Nat := 118140960795 + 4359556 * 2 ^ 59
def prefixEnd_4359556 : Nat := 4983230072969 + 3 ^ 40 * 4359556 * 2
def baseEnd_4359556 : Nat := 2238547668192450450800773

theorem tailTrace_4359556 : CollatzResearch.WordTrace tailWord_4359556 prefixEnd_4359556 2238547668192450450800773 := by
  unfold tailWord_4359556
  simp only [CollatzResearch.WordTrace]
  refine ⟨79503035097040319866513261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106004046796053759822017681 79503035097040319866513261)
  ·
    refine ⟨29813638161390119949942473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79503035097040319866513261 29813638161390119949942473)
    ·
      refine ⟨22360228621042589962456855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29813638161390119949942473 22360228621042589962456855)
      ·
        refine ⟨33540342931563884943685283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22360228621042589962456855 33540342931563884943685283)
        ·
          refine ⟨50310514397345827415527925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33540342931563884943685283 50310514397345827415527925)
          ·
            refine ⟨4716610724751171320205743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50310514397345827415527925 4716610724751171320205743)
            ·
              refine ⟨7074916087126756980308615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716610724751171320205743 7074916087126756980308615)
              ·
                refine ⟨10612374130690135470462923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074916087126756980308615 10612374130690135470462923)
                ·
                  refine ⟨15918561196035203205694385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10612374130690135470462923 15918561196035203205694385)
                  ·
                    refine ⟨11938920897026402404270789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15918561196035203205694385 11938920897026402404270789)
                    ·
                      refine ⟨2238547668192450450800773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11938920897026402404270789 2238547668192450450800773)
                      ·
                        rfl

theorem cell23_4359556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_4359556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359556 prefixEnd_4359556 := by exact prefixLift 4359556
  have htrace : WordTrace (prefixWord ++ tailWord_4359556) baseStart_4359556 baseEnd_4359556 := by
    simpa [prefixWord, tailWord_4359556, baseEnd_4359556] using wordTrace_append hprefix tailTrace_4359556
  have hstable : (prefixWord ++ tailWord_4359556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359556).length < 2 ^ (prefixWord ++ tailWord_4359556).sum := by decide
  have hdescent : baseEnd_4359556 < baseStart_4359556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359620 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4359620 : Nat := 118140960795 + 4359620 * 2 ^ 59
def prefixEnd_4359620 : Nat := 4983230072969 + 3 ^ 40 * 4359620 * 2
def baseEnd_4359620 : Nat := 2238580530954338200400479

theorem tailTrace_4359620 : CollatzResearch.WordTrace tailWord_4359620 prefixEnd_4359620 2238580530954338200400479 := by
  unfold tailWord_4359620
  simp only [CollatzResearch.WordTrace]
  refine ⟨79504202232924389331678157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106005602977232519108904209 79504202232924389331678157)
  ·
    refine ⟨29814075837346645999379309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79504202232924389331678157 29814075837346645999379309)
    ·
      refine ⟨11180278439004992249767241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29814075837346645999379309 11180278439004992249767241)
      ·
        refine ⟨8385208829253744187325431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11180278439004992249767241 8385208829253744187325431)
        ·
          refine ⟨12577813243880616280988147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385208829253744187325431 12577813243880616280988147)
          ·
            refine ⟨18866719865820924421482221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577813243880616280988147 18866719865820924421482221)
            ·
              refine ⟨7075019949682846658055833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18866719865820924421482221 7075019949682846658055833)
              ·
                refine ⟨5306264962262134993541875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7075019949682846658055833 5306264962262134993541875)
                ·
                  refine ⟨7959397443393202490312813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5306264962262134993541875 7959397443393202490312813)
                  ·
                    refine ⟨2984774041272450933867305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7959397443393202490312813 2984774041272450933867305)
                    ·
                      refine ⟨2238580530954338200400479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2984774041272450933867305 2238580530954338200400479)
                      ·
                        rfl

theorem cell23_4359620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4359620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359620 prefixEnd_4359620 := by exact prefixLift 4359620
  have htrace : WordTrace (prefixWord ++ tailWord_4359620) baseStart_4359620 baseEnd_4359620 := by
    simpa [prefixWord, tailWord_4359620, baseEnd_4359620] using wordTrace_append hprefix tailTrace_4359620
  have hstable : (prefixWord ++ tailWord_4359620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359620).length < 2 ^ (prefixWord ++ tailWord_4359620).sum := by decide
  have hdescent : baseEnd_4359620 < baseStart_4359620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359656 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 5]
def baseStart_4359656 : Nat := 118140960795 + 4359656 * 2 ^ 59
def prefixEnd_4359656 : Nat := 4983230072969 + 3 ^ 40 * 4359656 * 2
def baseEnd_4359656 : Nat := 248733224028655562172257

theorem tailTrace_4359656 : CollatzResearch.WordTrace tailWord_4359656 prefixEnd_4359656 248733224028655562172257 := by
  unfold tailWord_4359656
  simp only [CollatzResearch.WordTrace]
  refine ⟨79504858746859178405833411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106006478329145571207777881 79504858746859178405833411)
  ·
    refine ⟨119257288120288767608750117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79504858746859178405833411 119257288120288767608750117)
    ·
      refine ⟨22360741522554143926640647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119257288120288767608750117 22360741522554143926640647)
      ·
        refine ⟨33541112283831215889960971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22360741522554143926640647 33541112283831215889960971)
        ·
          refine ⟨50311668425746823834941457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33541112283831215889960971 50311668425746823834941457)
          ·
            refine ⟨37733751319310117876206093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50311668425746823834941457 37733751319310117876206093)
            ·
              refine ⟨14150156744741294203577285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37733751319310117876206093 14150156744741294203577285)
              ·
                refine ⟨2653154389638992663170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14150156744741294203577285 2653154389638992663170741)
                ·
                  refine ⟨248733224028655562172257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2653154389638992663170741 248733224028655562172257)
                  ·
                    rfl

theorem cell23_4359656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 5].length) (baseStart_4359656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359656 prefixEnd_4359656 := by exact prefixLift 4359656
  have htrace : WordTrace (prefixWord ++ tailWord_4359656) baseStart_4359656 baseEnd_4359656 := by
    simpa [prefixWord, tailWord_4359656, baseEnd_4359656] using wordTrace_append hprefix tailTrace_4359656
  have hstable : (prefixWord ++ tailWord_4359656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359656).length < 2 ^ (prefixWord ++ tailWord_4359656).sum := by decide
  have hdescent : baseEnd_4359656 < baseStart_4359656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359666 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4359666 : Nat := 118140960795 + 4359666 * 2 ^ 59
def prefixEnd_4359666 : Nat := 4983230072969 + 3 ^ 40 * 4359666 * 2
def baseEnd_4359666 : Nat := 2238604151064445020425267

theorem tailTrace_4359666 : CollatzResearch.WordTrace tailWord_4359666 prefixEnd_4359666 2238604151064445020425267 := by
  unfold tailWord_4359666
  simp only [CollatzResearch.WordTrace]
  refine ⟨39752520555920532129882713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106006721482454752346353901 39752520555920532129882713)
  ·
    refine ⟨29814390416940399097412035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39752520555920532129882713 29814390416940399097412035)
    ·
      refine ⟨44721585625410598646118053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29814390416940399097412035 44721585625410598646118053)
      ·
        refine ⟨8385297304764487246147135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44721585625410598646118053 8385297304764487246147135)
        ·
          refine ⟨12577945957146730869220703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8385297304764487246147135 12577945957146730869220703)
          ·
            refine ⟨18866918935720096303831055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577945957146730869220703 18866918935720096303831055)
            ·
              refine ⟨28300378403580144455746583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18866918935720096303831055 28300378403580144455746583)
              ·
                refine ⟨42450567605370216683619875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28300378403580144455746583 42450567605370216683619875)
                ·
                  refine ⟨63675851408055325025429813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42450567605370216683619875 63675851408055325025429813)
                  ·
                    refine ⟨5969611069505186721134045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63675851408055325025429813 5969611069505186721134045)
                    ·
                      refine ⟨2238604151064445020425267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969611069505186721134045 2238604151064445020425267)
                      ·
                        rfl

theorem cell23_4359666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4359666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359666 prefixEnd_4359666 := by exact prefixLift 4359666
  have htrace : WordTrace (prefixWord ++ tailWord_4359666) baseStart_4359666 baseEnd_4359666 := by
    simpa [prefixWord, tailWord_4359666, baseEnd_4359666] using wordTrace_append hprefix tailTrace_4359666
  have hstable : (prefixWord ++ tailWord_4359666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359666).length < 2 ^ (prefixWord ++ tailWord_4359666).sum := by decide
  have hdescent : baseEnd_4359666 < baseStart_4359666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359689 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_4359689 : Nat := 118140960795 + 4359689 * 2 ^ 59
def prefixEnd_4359689 : Nat := 4983230072969 + 3 ^ 40 * 4359689 * 2
def baseEnd_4359689 : Nat := 2238615961119498430437661

theorem tailTrace_4359689 : CollatzResearch.WordTrace tailWord_4359689 prefixEnd_4359689 2238615961119498430437661 := by
  unfold tailWord_4359689
  simp only [CollatzResearch.WordTrace]
  refine ⟨159010921102598803447618121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106007280735065868965078747 159010921102598803447618121)
  ·
    refine ⟨119258190826949102585713591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159010921102598803447618121 119258190826949102585713591)
    ·
      refine ⟨178887286240423653878570387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119258190826949102585713591 178887286240423653878570387)
      ·
        refine ⟨268330929360635480817855581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178887286240423653878570387 268330929360635480817855581)
        ·
          refine ⟨100624098510238305306695843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268330929360635480817855581 100624098510238305306695843)
          ·
            refine ⟨150936147765357457960043765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100624098510238305306695843 150936147765357457960043765)
            ·
              refine ⟨14150263853002261683754103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150936147765357457960043765 14150263853002261683754103)
              ·
                refine ⟨21225395779503392525631155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14150263853002261683754103 21225395779503392525631155)
                ·
                  refine ⟨31838093669255088788446733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21225395779503392525631155 31838093669255088788446733)
                  ·
                    refine ⟨11939285125970658295667525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31838093669255088788446733 11939285125970658295667525)
                    ·
                      refine ⟨2238615961119498430437661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11939285125970658295667525 2238615961119498430437661)
                      ·
                        rfl

theorem cell23_4359689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_4359689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359689 prefixEnd_4359689 := by exact prefixLift 4359689
  have htrace : WordTrace (prefixWord ++ tailWord_4359689) baseStart_4359689 baseEnd_4359689 := by
    simpa [prefixWord, tailWord_4359689, baseEnd_4359689] using wordTrace_append hprefix tailTrace_4359689
  have hstable : (prefixWord ++ tailWord_4359689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359689).length < 2 ^ (prefixWord ++ tailWord_4359689).sum := by decide
  have hdescent : baseEnd_4359689 < baseStart_4359689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359759 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 5, 5]
def baseStart_4359759 : Nat := 118140960795 + 4359759 * 2 ^ 59
def prefixEnd_4359759 : Nat := 4983230072969 + 3 ^ 40 * 4359759 * 2
def baseEnd_4359759 : Nat := 746217301588437718854113

theorem tailTrace_4359759 : CollatzResearch.WordTrace tailWord_4359759 prefixEnd_4359759 746217301588437718854113 := by
  unfold tailWord_4359759
  simp only [CollatzResearch.WordTrace]
  refine ⟨159013474212345205402666331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106008982808230136935110887 159013474212345205402666331)
  ·
    refine ⟨238520211318517808103999497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159013474212345205402666331 238520211318517808103999497)
    ·
      refine ⟨178890158488888356077999623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238520211318517808103999497 178890158488888356077999623)
      ·
        refine ⟨268335237733332534116999435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178890158488888356077999623 268335237733332534116999435)
        ·
          refine ⟨402502856599998801175499153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268335237733332534116999435 402502856599998801175499153)
          ·
            refine ⟨301877142449999100881624365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402502856599998801175499153 301877142449999100881624365)
            ·
              refine ⟨113203928418749662830609137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301877142449999100881624365 113203928418749662830609137)
              ·
                refine ⟨84902946314062247122956853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113203928418749662830609137 84902946314062247122956853)
                ·
                  refine ⟨7959651216943335667777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84902946314062247122956853 7959651216943335667777205)
                  ·
                    refine ⟨746217301588437718854113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7959651216943335667777205 746217301588437718854113)
                    ·
                      rfl

theorem cell23_4359759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_4359759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359759 prefixEnd_4359759 := by exact prefixLift 4359759
  have htrace : WordTrace (prefixWord ++ tailWord_4359759) baseStart_4359759 baseEnd_4359759 := by
    simpa [prefixWord, tailWord_4359759, baseEnd_4359759] using wordTrace_append hprefix tailTrace_4359759
  have hstable : (prefixWord ++ tailWord_4359759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359759).length < 2 ^ (prefixWord ++ tailWord_4359759).sum := by decide
  have hdescent : baseEnd_4359759 < baseStart_4359759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359849 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_4359849 : Nat := 118140960795 + 4359849 * 2 ^ 59
def prefixEnd_4359849 : Nat := 4983230072969 + 3 ^ 40 * 4359849 * 2
def baseEnd_4359849 : Nat := 746232706008072601478975

theorem tailTrace_4359849 : CollatzResearch.WordTrace tailWord_4359849 prefixEnd_4359849 746232706008072601478975 := by
  unfold tailWord_4359849
  simp only [CollatzResearch.WordTrace]
  refine ⟨159016756782019150773442601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106011171188012767182295067 159016756782019150773442601)
  ·
    refine ⟨119262567586514363080081951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159016756782019150773442601 119262567586514363080081951)
    ·
      refine ⟨178893851379771544620122927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119262567586514363080081951 178893851379771544620122927)
      ·
        refine ⟨268340777069657316930184391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178893851379771544620122927 268340777069657316930184391)
        ·
          refine ⟨402511165604485975395276587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268340777069657316930184391 402511165604485975395276587)
          ·
            refine ⟨603766748406728963092914881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402511165604485975395276587 603766748406728963092914881)
            ·
              refine ⟨452825061305046722319686161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603766748406728963092914881 452825061305046722319686161)
              ·
                refine ⟨339618795978785041739764621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452825061305046722319686161 339618795978785041739764621)
                ·
                  refine ⟨127357048492044390652411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339618795978785041739764621 127357048492044390652411733)
                  ·
                    refine ⟨746232706008072601478975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127357048492044390652411733 746232706008072601478975)
                    ·
                      rfl

theorem cell23_4359849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_4359849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359849 prefixEnd_4359849 := by exact prefixLift 4359849
  have htrace : WordTrace (prefixWord ++ tailWord_4359849) baseStart_4359849 baseEnd_4359849 := by
    simpa [prefixWord, tailWord_4359849, baseEnd_4359849] using wordTrace_append hprefix tailTrace_4359849
  have hstable : (prefixWord ++ tailWord_4359849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359849).length < 2 ^ (prefixWord ++ tailWord_4359849).sum := by decide
  have hdescent : baseEnd_4359849 < baseStart_4359849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359853 : List Nat := [1, 5, 2, 1, 1, 1, 5, 7]
def baseStart_4359853 : Nat := 118140960795 + 4359853 * 2 ^ 59
def prefixEnd_4359853 : Nat := 4983230072969 + 3 ^ 40 * 4359853 * 2
def baseEnd_4359853 : Nat := 82914821183216140325441

theorem tailTrace_4359853 : CollatzResearch.WordTrace tailWord_4359853 prefixEnd_4359853 82914821183216140325441 := by
  unfold tailWord_4359853
  simp only [CollatzResearch.WordTrace]
  refine ⟨159016902674004659456588213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106011268449336439637725475 159016902674004659456588213)
  ·
    refine ⟨14907834625687936824055145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159016902674004659456588213 14907834625687936824055145)
    ·
      refine ⟨11180875969265952618041359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14907834625687936824055145 11180875969265952618041359)
      ·
        refine ⟨16771313953898928927062039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11180875969265952618041359 16771313953898928927062039)
        ·
          refine ⟨25156970930848393390593059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16771313953898928927062039 25156970930848393390593059)
          ·
            refine ⟨37735456396272590085889589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25156970930848393390593059 37735456396272590085889589)
            ·
              refine ⟨3537699037150555320552149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37735456396272590085889589 3537699037150555320552149)
              ·
                refine ⟨82914821183216140325441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3537699037150555320552149 82914821183216140325441)
                ·
                  rfl

theorem cell23_4359853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 7].length) (baseStart_4359853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359853 prefixEnd_4359853 := by exact prefixLift 4359853
  have htrace : WordTrace (prefixWord ++ tailWord_4359853) baseStart_4359853 baseEnd_4359853 := by
    simpa [prefixWord, tailWord_4359853, baseEnd_4359853] using wordTrace_append hprefix tailTrace_4359853
  have hstable : (prefixWord ++ tailWord_4359853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359853).length < 2 ^ (prefixWord ++ tailWord_4359853).sum := by decide
  have hdescent : baseEnd_4359853 < baseStart_4359853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359863 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_4359863 : Nat := 118140960795 + 4359863 * 2 ^ 59
def prefixEnd_4359863 : Nat := 4983230072969 + 3 ^ 40 * 4359863 * 2
def baseEnd_4359863 : Nat := 2238705306753380749661861

theorem tailTrace_4359863 : CollatzResearch.WordTrace tailWord_4359863 prefixEnd_4359863 2238705306753380749661861 := by
  unfold tailWord_4359863
  simp only [CollatzResearch.WordTrace]
  refine ⟨159017267403968431164452243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106011511602645620776301495 159017267403968431164452243)
  ·
    refine ⟨238525901105952646746678365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159017267403968431164452243 238525901105952646746678365)
    ·
      refine ⟨89447212914732242530004387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238525901105952646746678365 89447212914732242530004387)
      ·
        refine ⟨134170819372098363795006581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89447212914732242530004387 134170819372098363795006581)
        ·
          refine ⟨12578514316134221605781867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134170819372098363795006581 12578514316134221605781867)
          ·
            refine ⟨18867771474201332408672801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12578514316134221605781867 18867771474201332408672801)
            ·
              refine ⟨14150828605650999306504601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18867771474201332408672801 14150828605650999306504601)
              ·
                refine ⟨10613121454238249479878451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14150828605650999306504601 10613121454238249479878451)
                ·
                  refine ⟨15919682181357374219817677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10613121454238249479878451 15919682181357374219817677)
                  ·
                    refine ⟨5969880818009015332431629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15919682181357374219817677 5969880818009015332431629)
                    ·
                      refine ⟨2238705306753380749661861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969880818009015332431629 2238705306753380749661861)
                      ·
                        rfl

theorem cell23_4359863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_4359863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359863 prefixEnd_4359863 := by exact prefixLift 4359863
  have htrace : WordTrace (prefixWord ++ tailWord_4359863) baseStart_4359863 baseEnd_4359863 := by
    simpa [prefixWord, tailWord_4359863, baseEnd_4359863] using wordTrace_append hprefix tailTrace_4359863
  have hstable : (prefixWord ++ tailWord_4359863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359863).length < 2 ^ (prefixWord ++ tailWord_4359863).sum := by decide
  have hdescent : baseEnd_4359863 < baseStart_4359863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359874 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4359874 : Nat := 118140960795 + 4359874 * 2 ^ 59
def prefixEnd_4359874 : Nat := 4983230072969 + 3 ^ 40 * 4359874 * 2
def baseEnd_4359874 : Nat := 746236985013526735541437

theorem tailTrace_4359874 : CollatzResearch.WordTrace tailWord_4359874 prefixEnd_4359874 746236985013526735541437 := by
  unfold tailWord_4359874
  simp only [CollatzResearch.WordTrace]
  refine ⟨39754417151732145010775669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106011779071285720028735117 39754417151732145010775669)
  ·
    refine ⟨3726976607974888594760219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39754417151732145010775669 3726976607974888594760219)
    ·
      refine ⟨5590464911962332892140329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726976607974888594760219 5590464911962332892140329)
      ·
        refine ⟨4192848683971749669105247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5590464911962332892140329 4192848683971749669105247)
        ·
          refine ⟨6289273025957624503657871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192848683971749669105247 6289273025957624503657871)
          ·
            refine ⟨9433909538936436755486807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289273025957624503657871 9433909538936436755486807)
            ·
              refine ⟨14150864308404655133230211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9433909538936436755486807 14150864308404655133230211)
              ·
                refine ⟨21226296462606982699845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14150864308404655133230211 21226296462606982699845317)
                ·
                  refine ⟨3979930586738809256220997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21226296462606982699845317 3979930586738809256220997)
                  ·
                    refine ⟨746236985013526735541437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979930586738809256220997 746236985013526735541437)
                    ·
                      rfl

theorem cell23_4359874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4359874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359874 prefixEnd_4359874 := by exact prefixLift 4359874
  have htrace : WordTrace (prefixWord ++ tailWord_4359874) baseStart_4359874 baseEnd_4359874 := by
    simpa [prefixWord, tailWord_4359874, baseEnd_4359874] using wordTrace_append hprefix tailTrace_4359874
  have hstable : (prefixWord ++ tailWord_4359874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359874).length < 2 ^ (prefixWord ++ tailWord_4359874).sum := by decide
  have hdescent : baseEnd_4359874 < baseStart_4359874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359894 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4359894 : Nat := 118140960795 + 4359894 * 2 ^ 59
def prefixEnd_4359894 : Nat := 4983230072969 + 3 ^ 40 * 4359894 * 2
def baseEnd_4359894 : Nat := 2238721224653670128374219

theorem tailTrace_4359894 : CollatzResearch.WordTrace tailWord_4359894 prefixEnd_4359894 2238721224653670128374219 := by
  unfold tailWord_4359894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938649879178507716176921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106012265377904082305887157 9938649879178507716176921)
  ·
    refine ⟨7453987409383880787132691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9938649879178507716176921 7453987409383880787132691)
    ·
      refine ⟨11180981114075821180699037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453987409383880787132691 11180981114075821180699037)
      ·
        refine ⟨4192867917778432942762139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11180981114075821180699037 4192867917778432942762139)
        ·
          refine ⟨6289301876667649414143209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192867917778432942762139 6289301876667649414143209)
          ·
            refine ⟨4716976407500737060607407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6289301876667649414143209 4716976407500737060607407)
            ·
              refine ⟨7075464611251105590911111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716976407500737060607407 7075464611251105590911111)
              ·
                refine ⟨10613196916876658386366667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7075464611251105590911111 10613196916876658386366667)
                ·
                  refine ⟨15919795375314987579550001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10613196916876658386366667 15919795375314987579550001)
                  ·
                    refine ⟨11939846531486240684662501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15919795375314987579550001 11939846531486240684662501)
                    ·
                      refine ⟨2238721224653670128374219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11939846531486240684662501 2238721224653670128374219)
                      ·
                        rfl

theorem cell23_4359894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4359894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359894 prefixEnd_4359894 := by exact prefixLift 4359894
  have htrace : WordTrace (prefixWord ++ tailWord_4359894) baseStart_4359894 baseEnd_4359894 := by
    simpa [prefixWord, tailWord_4359894, baseEnd_4359894] using wordTrace_append hprefix tailTrace_4359894
  have hstable : (prefixWord ++ tailWord_4359894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359894).length < 2 ^ (prefixWord ++ tailWord_4359894).sum := by decide
  have hdescent : baseEnd_4359894 < baseStart_4359894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359896 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_4359896 : Nat := 118140960795 + 4359896 * 2 ^ 59
def prefixEnd_4359896 : Nat := 4983230072969 + 3 ^ 40 * 4359896 * 2
def baseEnd_4359896 : Nat := 746240750538326373516403

theorem tailTrace_4359896 : CollatzResearch.WordTrace tailWord_4359896 prefixEnd_4359896 746240750538326373516403 := by
  unfold tailWord_4359896
  simp only [CollatzResearch.WordTrace]
  refine ⟨79509235506424438900201771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106012314008565918533602361 79509235506424438900201771)
  ·
    refine ⟨119263853259636658350302657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79509235506424438900201771 119263853259636658350302657)
    ·
      refine ⟨89447889944727493762726993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119263853259636658350302657 89447889944727493762726993)
      ·
        refine ⟨67085917458545620322045245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89447889944727493762726993 67085917458545620322045245)
        ·
          refine ⟨25157219046954607620766967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67085917458545620322045245 25157219046954607620766967)
          ·
            refine ⟨37735828570431911431150451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25157219046954607620766967 37735828570431911431150451)
            ·
              refine ⟨56603742855647867146725677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37735828570431911431150451 56603742855647867146725677)
              ·
                refine ⟨21226403570867950180022129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56603742855647867146725677 21226403570867950180022129)
                ·
                  refine ⟨15919802678150962635016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21226403570867950180022129 15919802678150962635016597)
                  ·
                    refine ⟨746240750538326373516403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15919802678150962635016597 746240750538326373516403)
                    ·
                      rfl

theorem cell23_4359896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_4359896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359896 prefixEnd_4359896 := by exact prefixLift 4359896
  have htrace : WordTrace (prefixWord ++ tailWord_4359896) baseStart_4359896 baseEnd_4359896 := by
    simpa [prefixWord, tailWord_4359896, baseEnd_4359896] using wordTrace_append hprefix tailTrace_4359896
  have hstable : (prefixWord ++ tailWord_4359896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359896).length < 2 ^ (prefixWord ++ tailWord_4359896).sum := by decide
  have hdescent : baseEnd_4359896 < baseStart_4359896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359897 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 2, 1, 3]
def baseStart_4359897 : Nat := 118140960795 + 4359897 * 2 ^ 59
def prefixEnd_4359897 : Nat := 4983230072969 + 3 ^ 40 * 4359897 * 2
def baseEnd_4359897 : Nat := 2238722765095633616636705

theorem tailTrace_4359897 : CollatzResearch.WordTrace tailWord_4359897 prefixEnd_4359897 2238722765095633616636705 := by
  unfold tailWord_4359897
  simp only [CollatzResearch.WordTrace]
  refine ⟨159018507485845254971189945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106012338323896836647459963 159018507485845254971189945)
  ·
    refine ⟨119263880614383941228392459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159018507485845254971189945 119263880614383941228392459)
    ·
      refine ⟨178895820921575911842588689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119263880614383941228392459 178895820921575911842588689)
      ·
        refine ⟨134171865691181933881941517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178895820921575911842588689 134171865691181933881941517)
        ·
          refine ⟨50314449634193225205728069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134171865691181933881941517 50314449634193225205728069)
          ·
            refine ⟨9433959306411229726074013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50314449634193225205728069 9433959306411229726074013)
            ·
              refine ⟨3537734739904211147277755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9433959306411229726074013 3537734739904211147277755)
              ·
                refine ⟨5306602109856316720916633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537734739904211147277755 5306602109856316720916633)
                ·
                  refine ⟨3979951582392237540687475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306602109856316720916633 3979951582392237540687475)
                  ·
                    refine ⟨5969927373588356311031213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3979951582392237540687475 5969927373588356311031213)
                    ·
                      refine ⟨2238722765095633616636705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5969927373588356311031213 2238722765095633616636705)
                      ·
                        rfl

theorem cell23_4359897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_4359897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359897 prefixEnd_4359897 := by exact prefixLift 4359897
  have htrace : WordTrace (prefixWord ++ tailWord_4359897) baseStart_4359897 baseEnd_4359897 := by
    simpa [prefixWord, tailWord_4359897, baseEnd_4359897] using wordTrace_append hprefix tailTrace_4359897
  have hstable : (prefixWord ++ tailWord_4359897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359897).length < 2 ^ (prefixWord ++ tailWord_4359897).sum := by decide
  have hdescent : baseEnd_4359897 < baseStart_4359897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359916 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_4359916 : Nat := 118140960795 + 4359916 * 2 ^ 59
def prefixEnd_4359916 : Nat := 4983230072969 + 3 ^ 40 * 4359916 * 2
def baseEnd_4359916 : Nat := 2238732521228069042299117

theorem tailTrace_4359916 : CollatzResearch.WordTrace tailWord_4359916 prefixEnd_4359916 2238732521228069042299117 := by
  unfold tailWord_4359916
  simp only [CollatzResearch.WordTrace]
  refine ⟨79509600236388210608065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106012800315184280810754401 79509600236388210608065801)
  ·
    refine ⟨59632200177291157956049351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79509600236388210608065801 59632200177291157956049351)
    ·
      refine ⟨89448300265936736934074027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59632200177291157956049351 89448300265936736934074027)
      ·
        refine ⟨134172450398905105401111041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89448300265936736934074027 134172450398905105401111041)
        ·
          refine ⟨100629337799178829050833281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134172450398905105401111041 100629337799178829050833281)
          ·
            refine ⟨75472003349384121788124961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100629337799178829050833281 75472003349384121788124961)
            ·
              refine ⟨56604002512038091341093721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75472003349384121788124961 56604002512038091341093721)
              ·
                refine ⟨42453001884028568505820291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56604002512038091341093721 42453001884028568505820291)
                ·
                  refine ⟨63679502826042852758730437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42453001884028568505820291 63679502826042852758730437)
                  ·
                    refine ⟨11939906779883034892261957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63679502826042852758730437 11939906779883034892261957)
                    ·
                      refine ⟨2238732521228069042299117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11939906779883034892261957 2238732521228069042299117)
                      ·
                        rfl

theorem cell23_4359916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_4359916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359916 prefixEnd_4359916 := by exact prefixLift 4359916
  have htrace : WordTrace (prefixWord ++ tailWord_4359916) baseStart_4359916 baseEnd_4359916 := by
    simpa [prefixWord, tailWord_4359916, baseEnd_4359916] using wordTrace_append hprefix tailTrace_4359916
  have hstable : (prefixWord ++ tailWord_4359916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359916).length < 2 ^ (prefixWord ++ tailWord_4359916).sum := by decide
  have hdescent : baseEnd_4359916 < baseStart_4359916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359942 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4359942 : Nat := 118140960795 + 4359942 * 2 ^ 59
def prefixEnd_4359942 : Nat := 4983230072969 + 3 ^ 40 * 4359942 * 2
def baseEnd_4359942 : Nat := 746248623908361980191333

theorem tailTrace_4359942 : CollatzResearch.WordTrace tailWord_4359942 prefixEnd_4359942 746248623908361980191333 := by
  unfold tailWord_4359942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969379649083819614268065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106013432513788151771052053 4969379649083819614268065)
  ·
    refine ⟨3727034736812864710701049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4969379649083819614268065 3727034736812864710701049)
    ·
      refine ⟨2795276052609648533025787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3727034736812864710701049 2795276052609648533025787)
      ·
        refine ⟨4192914078914472799538681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795276052609648533025787 4192914078914472799538681)
        ·
          refine ⟨3144685559185854599654011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4192914078914472799538681 3144685559185854599654011)
          ·
            refine ⟨4717028338778781899481017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144685559185854599654011 4717028338778781899481017)
            ·
              refine ⟨3537771254084086424610763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717028338778781899481017 3537771254084086424610763)
              ·
                refine ⟨5306656881126129636916145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537771254084086424610763 5306656881126129636916145)
                ·
                  refine ⟨3979992660844597227687109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306656881126129636916145 3979992660844597227687109)
                  ·
                    refine ⟨746248623908361980191333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979992660844597227687109 746248623908361980191333)
                    ·
                      rfl

theorem cell23_4359942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4359942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359942 prefixEnd_4359942 := by exact prefixLift 4359942
  have htrace : WordTrace (prefixWord ++ tailWord_4359942) baseStart_4359942 baseEnd_4359942 := by
    simpa [prefixWord, tailWord_4359942, baseEnd_4359942] using wordTrace_append hprefix tailTrace_4359942
  have hstable : (prefixWord ++ tailWord_4359942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359942).length < 2 ^ (prefixWord ++ tailWord_4359942).sum := by decide
  have hdescent : baseEnd_4359942 < baseStart_4359942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359963 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 5, 2]
def baseStart_4359963 : Nat := 118140960795 + 4359963 * 2 ^ 59
def prefixEnd_4359963 : Nat := 4983230072969 + 3 ^ 40 * 4359963 * 2
def baseEnd_4359963 : Nat := 2238756654818830358411401

theorem tailTrace_4359963 : CollatzResearch.WordTrace tailWord_4359963 prefixEnd_4359963 2238756654818830358411401 := by
  unfold tailWord_4359963
  simp only [CollatzResearch.WordTrace]
  refine ⟨159020914703606148243092543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106013943135737432162061695 159020914703606148243092543)
  ·
    refine ⟨238531372055409222364638815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159020914703606148243092543 238531372055409222364638815)
    ·
      refine ⟨357797058083113833546958223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238531372055409222364638815 357797058083113833546958223)
      ·
        refine ⟨536695587124670750320437335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357797058083113833546958223 536695587124670750320437335)
        ·
          refine ⟨805043380687006125480656003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536695587124670750320437335 805043380687006125480656003)
          ·
            refine ⟨1207565071030509188220984005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805043380687006125480656003 1207565071030509188220984005)
            ·
              refine ⟨226418450818220472791434501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1207565071030509188220984005 226418450818220472791434501)
              ·
                refine ⟨42453459528416338648393969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 226418450818220472791434501 42453459528416338648393969)
                ·
                  refine ⟨31840094646312253986295477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42453459528416338648393969 31840094646312253986295477)
                  ·
                    refine ⟨2985008873091773811215201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31840094646312253986295477 2985008873091773811215201)
                    ·
                      refine ⟨2238756654818830358411401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985008873091773811215201 2238756654818830358411401)
                      ·
                        rfl

theorem cell23_4359963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5, 2].length) (baseStart_4359963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359963 prefixEnd_4359963 := by exact prefixLift 4359963
  have htrace : WordTrace (prefixWord ++ tailWord_4359963) baseStart_4359963 baseEnd_4359963 := by
    simpa [prefixWord, tailWord_4359963, baseEnd_4359963] using wordTrace_append hprefix tailTrace_4359963
  have hstable : (prefixWord ++ tailWord_4359963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359963).length < 2 ^ (prefixWord ++ tailWord_4359963).sum := by decide
  have hdescent : baseEnd_4359963 < baseStart_4359963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4359973 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_4359973 : Nat := 118140960795 + 4359973 * 2 ^ 59
def prefixEnd_4359973 : Nat := 4983230072969 + 3 ^ 40 * 4359973 * 2
def baseEnd_4359973 : Nat := 746253929875125106428785

theorem tailTrace_4359973 : CollatzResearch.WordTrace tailWord_4359973 prefixEnd_4359973 746253929875125106428785 := by
  unfold tailWord_4359973
  simp only [CollatzResearch.WordTrace]
  refine ⟨159021279433569919950956573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106014186289046613300637715 159021279433569919950956573)
  ·
    refine ⟨59632979787588719981608715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159021279433569919950956573 59632979787588719981608715)
    ·
      refine ⟨89449469681383079972413073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59632979787588719981608715 89449469681383079972413073)
      ·
        refine ⟨67087102261037309979309805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89449469681383079972413073 67087102261037309979309805)
        ·
          refine ⟨25157663347888991242241177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67087102261037309979309805 25157663347888991242241177)
          ·
            refine ⟨18868247510916743431680883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25157663347888991242241177 18868247510916743431680883)
            ·
              refine ⟨28302371266375115147521325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18868247510916743431680883 28302371266375115147521325)
              ·
                refine ⟨10613389224890668180320497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28302371266375115147521325 10613389224890668180320497)
                ·
                  refine ⟨7960041918668001135240373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10613389224890668180320497 7960041918668001135240373)
                  ·
                    refine ⟨746253929875125106428785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7960041918668001135240373 746253929875125106428785)
                    ·
                      rfl

theorem cell23_4359973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_4359973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4359973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4359973 prefixEnd_4359973 := by exact prefixLift 4359973
  have htrace : WordTrace (prefixWord ++ tailWord_4359973) baseStart_4359973 baseEnd_4359973 := by
    simpa [prefixWord, tailWord_4359973, baseEnd_4359973] using wordTrace_append hprefix tailTrace_4359973
  have hstable : (prefixWord ++ tailWord_4359973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4359973).length < 2 ^ (prefixWord ++ tailWord_4359973).sum := by decide
  have hdescent : baseEnd_4359973 < baseStart_4359973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4359973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360010 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_4360010 : Nat := 118140960795 + 4360010 * 2 ^ 59
def prefixEnd_4360010 : Nat := 4983230072969 + 3 ^ 40 * 4360010 * 2
def baseEnd_4360010 : Nat := 2238780788409591674523685

theorem tailTrace_4360010 : CollatzResearch.WordTrace tailWord_4360010 prefixEnd_4360010 2238780788409591674523685 := by
  unfold tailWord_4360010
  simp only [CollatzResearch.WordTrace]
  refine ⟨39755657233608968817513371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106015085956290583513368989 39755657233608968817513371)
  ·
    refine ⟨59633485850413453226270057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39755657233608968817513371 59633485850413453226270057)
    ·
      refine ⟨44725114387810089919702543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59633485850413453226270057 44725114387810089919702543)
      ·
        refine ⟨67087671581715134879553815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44725114387810089919702543 67087671581715134879553815)
        ·
          refine ⟨100631507372572702319330723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67087671581715134879553815 100631507372572702319330723)
          ·
            refine ⟨150947261058859053478996085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100631507372572702319330723 150947261058859053478996085)
            ·
              refine ⟨14151305724268036263655883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150947261058859053478996085 14151305724268036263655883)
              ·
                refine ⟨21226958586402054395483825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14151305724268036263655883 21226958586402054395483825)
                ·
                  refine ⟨15920218939801540796612869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21226958586402054395483825 15920218939801540796612869)
                  ·
                    refine ⟨2985041051212788899364913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15920218939801540796612869 2985041051212788899364913)
                    ·
                      refine ⟨2238780788409591674523685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985041051212788899364913 2238780788409591674523685)
                      ·
                        rfl

theorem cell23_4360010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_4360010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360010 prefixEnd_4360010 := by exact prefixLift 4360010
  have htrace : WordTrace (prefixWord ++ tailWord_4360010) baseStart_4360010 baseEnd_4360010 := by
    simpa [prefixWord, tailWord_4360010, baseEnd_4360010] using wordTrace_append hprefix tailTrace_4360010
  have hstable : (prefixWord ++ tailWord_4360010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360010).length < 2 ^ (prefixWord ++ tailWord_4360010).sum := by decide
  have hdescent : baseEnd_4360010 < baseStart_4360010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360016 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 10]
def baseStart_4360016 : Nat := 118140960795 + 4360016 * 2 ^ 59
def prefixEnd_4360016 : Nat := 4983230072969 + 3 ^ 40 * 4360016 * 2
def baseEnd_4360016 : Nat := 248753763254835405672073

theorem tailTrace_4360016 : CollatzResearch.WordTrace tailWord_4360016 prefixEnd_4360016 248753763254835405672073 := by
  unfold tailWord_4360016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79511423886207069147385951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106015231848276092196514601 79511423886207069147385951)
  ·
    refine ⟨119267135829310603721078927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79511423886207069147385951 119267135829310603721078927)
    ·
      refine ⟨178900703743965905581618391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119267135829310603721078927 178900703743965905581618391)
      ·
        refine ⟨268351055615948858372427587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178900703743965905581618391 268351055615948858372427587)
        ·
          refine ⟨402526583423923287558641381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268351055615948858372427587 402526583423923287558641381)
          ·
            refine ⟨75473734391985616417245259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 402526583423923287558641381 75473734391985616417245259)
            ·
              refine ⟨113210601587978424625867889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75473734391985616417245259 113210601587978424625867889)
              ·
                refine ⟨84907951190983818469400917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113210601587978424625867889 84907951190983818469400917)
                ·
                  refine ⟨248753763254835405672073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84907951190983818469400917 248753763254835405672073)
                  ·
                    rfl

theorem cell23_4360016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_4360016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360016 prefixEnd_4360016 := by exact prefixLift 4360016
  have htrace : WordTrace (prefixWord ++ tailWord_4360016) baseStart_4360016 baseEnd_4360016 := by
    simpa [prefixWord, tailWord_4360016, baseEnd_4360016] using wordTrace_append hprefix tailTrace_4360016
  have hstable : (prefixWord ++ tailWord_4360016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360016).length < 2 ^ (prefixWord ++ tailWord_4360016).sum := by decide
  have hdescent : baseEnd_4360016 < baseStart_4360016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360020 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4360020 : Nat := 118140960795 + 4360020 * 2 ^ 59
def prefixEnd_4360020 : Nat := 4983230072969 + 3 ^ 40 * 4360020 * 2
def baseEnd_4360020 : Nat := 746261974405378878466213

theorem tailTrace_4360020 : CollatzResearch.WordTrace tailWord_4360020 prefixEnd_4360020 746261974405378878466213 := by
  unfold tailWord_4360020
  simp only [CollatzResearch.WordTrace]
  refine ⟨79511496832199823488958757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106015329109599764651945009 79511496832199823488958757)
  ·
    refine ⟨14908405656037466904179767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79511496832199823488958757 14908405656037466904179767)
    ·
      refine ⟨22362608484056200356269651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14908405656037466904179767 22362608484056200356269651)
      ·
        refine ⟨33543912726084300534404477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22362608484056200356269651 33543912726084300534404477)
        ·
          refine ⟨12578967272281612700401679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33543912726084300534404477 12578967272281612700401679)
          ·
            refine ⟨18868450908422419050602519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12578967272281612700401679 18868450908422419050602519)
            ·
              refine ⟨28302676362633628575903779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18868450908422419050602519 28302676362633628575903779)
              ·
                refine ⟨42454014543950442863855669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28302676362633628575903779 42454014543950442863855669)
                ·
                  refine ⟨3980063863495354018486469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42454014543950442863855669 3980063863495354018486469)
                  ·
                    refine ⟨746261974405378878466213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980063863495354018486469 746261974405378878466213)
                    ·
                      rfl

theorem cell23_4360020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4360020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360020 prefixEnd_4360020 := by exact prefixLift 4360020
  have htrace : WordTrace (prefixWord ++ tailWord_4360020) baseStart_4360020 baseEnd_4360020 := by
    simpa [prefixWord, tailWord_4360020, baseEnd_4360020] using wordTrace_append hprefix tailTrace_4360020
  have hstable : (prefixWord ++ tailWord_4360020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360020).length < 2 ^ (prefixWord ++ tailWord_4360020).sum := by decide
  have hdescent : baseEnd_4360020 < baseStart_4360020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360053 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4360053 : Nat := 118140960795 + 4360053 * 2 ^ 59
def prefixEnd_4360053 : Nat := 4983230072969 + 3 ^ 40 * 4360053 * 2
def baseEnd_4360053 : Nat := 2238802868077735006285987

theorem tailTrace_4360053 : CollatzResearch.WordTrace tailWord_4360053 prefixEnd_4360053 2238802868077735006285987 := by
  unfold tailWord_4360053
  simp only [CollatzResearch.WordTrace]
  refine ⟨159024197273280093613868813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106016131515520062409245875 159024197273280093613868813)
  ·
    refine ⟨59634073977480035105200805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159024197273280093613868813 59634073977480035105200805)
    ·
      refine ⟨11181388870777506582225151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59634073977480035105200805 11181388870777506582225151)
      ·
        refine ⟨16772083306166259873337727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11181388870777506582225151 16772083306166259873337727)
        ·
          refine ⟨25158124959249389810006591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16772083306166259873337727 25158124959249389810006591)
          ·
            refine ⟨37737187438874084715009887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25158124959249389810006591 37737187438874084715009887)
            ·
              refine ⟨56605781158311127072514831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37737187438874084715009887 56605781158311127072514831)
              ·
                refine ⟨84908671737466690608772247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56605781158311127072514831 84908671737466690608772247)
                ·
                  refine ⟨127363007606200035913158371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84908671737466690608772247 127363007606200035913158371)
                  ·
                    refine ⟨191044511409300053869737557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127363007606200035913158371 191044511409300053869737557)
                    ·
                      refine ⟨2238802868077735006285987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191044511409300053869737557 2238802868077735006285987)
                      ·
                        rfl

theorem cell23_4360053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4360053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360053 prefixEnd_4360053 := by exact prefixLift 4360053
  have htrace : WordTrace (prefixWord ++ tailWord_4360053) baseStart_4360053 baseEnd_4360053 := by
    simpa [prefixWord, tailWord_4360053, baseEnd_4360053] using wordTrace_append hprefix tailTrace_4360053
  have hstable : (prefixWord ++ tailWord_4360053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360053).length < 2 ^ (prefixWord ++ tailWord_4360053).sum := by decide
  have hdescent : baseEnd_4360053 < baseStart_4360053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360054 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4360054 : Nat := 118140960795 + 4360054 * 2 ^ 59
def prefixEnd_4360054 : Nat := 4983230072969 + 3 ^ 40 * 4360054 * 2
def baseEnd_4360054 : Nat := 746267793852796500791161

theorem tailTrace_4360054 : CollatzResearch.WordTrace tailWord_4360054 prefixEnd_4360054 746267793852796500791161 := by
  unfold tailWord_4360054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939014609142279424040951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106016155830850980523103477 9939014609142279424040951)
  ·
    refine ⟨14908521913713419136061427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9939014609142279424040951 14908521913713419136061427)
    ·
      refine ⟨22362782870570128704092141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14908521913713419136061427 22362782870570128704092141)
      ·
        refine ⟨8386043576463798264034553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22362782870570128704092141 8386043576463798264034553)
        ·
          refine ⟨6289532682347848698025915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8386043576463798264034553 6289532682347848698025915)
          ·
            refine ⟨9434299023521773047038873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6289532682347848698025915 9434299023521773047038873)
            ·
              refine ⟨7075724267641329785279155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9434299023521773047038873 7075724267641329785279155)
              ·
                refine ⟨10613586401461994677918733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7075724267641329785279155 10613586401461994677918733)
                ·
                  refine ⟨3980094900548248004219525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10613586401461994677918733 3980094900548248004219525)
                  ·
                    refine ⟨746267793852796500791161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980094900548248004219525 746267793852796500791161)
                    ·
                      rfl

theorem cell23_4360054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4360054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360054 prefixEnd_4360054 := by exact prefixLift 4360054
  have htrace : WordTrace (prefixWord ++ tailWord_4360054) baseStart_4360054 baseEnd_4360054 := by
    simpa [prefixWord, tailWord_4360054, baseEnd_4360054] using wordTrace_append hprefix tailTrace_4360054
  have hstable : (prefixWord ++ tailWord_4360054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360054).length < 2 ^ (prefixWord ++ tailWord_4360054).sum := by decide
  have hdescent : baseEnd_4360054 < baseStart_4360054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360083 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4]
def baseStart_4360083 : Nat := 118140960795 + 4360083 * 2 ^ 59
def prefixEnd_4360083 : Nat := 4983230072969 + 3 ^ 40 * 4360083 * 2
def baseEnd_4360083 : Nat := 2238818272497369888910849

theorem tailTrace_4360083 : CollatzResearch.WordTrace tailWord_4360083 prefixEnd_4360083 2238818272497369888910849 := by
  unfold tailWord_4360083
  simp only [CollatzResearch.WordTrace]
  refine ⟨159025291463171408737460903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106016860975447605824973935 159025291463171408737460903)
  ·
    refine ⟨238537937194757113106191355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159025291463171408737460903 238537937194757113106191355)
    ·
      refine ⟨357806905792135669659287033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238537937194757113106191355 357806905792135669659287033)
      ·
        refine ⟨268355179344101752244465275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357806905792135669659287033 268355179344101752244465275)
        ·
          refine ⟨402532769016152628366697913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268355179344101752244465275 402532769016152628366697913)
          ·
            refine ⟨301899576762114471275023435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402532769016152628366697913 301899576762114471275023435)
            ·
              refine ⟨452849365143171706912535153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301899576762114471275023435 452849365143171706912535153)
              ·
                refine ⟨339637023857378780184401365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452849365143171706912535153 339637023857378780184401365)
                ·
                  refine ⟨7960242746657315160571907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 339637023857378780184401365 7960242746657315160571907)
                  ·
                    refine ⟨11940364119985972740857861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7960242746657315160571907 11940364119985972740857861)
                    ·
                      refine ⟨2238818272497369888910849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11940364119985972740857861 2238818272497369888910849)
                      ·
                        rfl

theorem cell23_4360083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_4360083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360083 prefixEnd_4360083 := by exact prefixLift 4360083
  have htrace : WordTrace (prefixWord ++ tailWord_4360083) baseStart_4360083 baseEnd_4360083 := by
    simpa [prefixWord, tailWord_4360083, baseEnd_4360083] using wordTrace_append hprefix tailTrace_4360083
  have hstable : (prefixWord ++ tailWord_4360083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360083).length < 2 ^ (prefixWord ++ tailWord_4360083).sum := by decide
  have hdescent : baseEnd_4360083 < baseStart_4360083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360088 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 1, 4]
def baseStart_4360088 : Nat := 118140960795 + 4360088 * 2 ^ 59
def prefixEnd_4360088 : Nat := 4983230072969 + 3 ^ 40 * 4360088 * 2
def baseEnd_4360088 : Nat := 746273613300214123116109

theorem tailTrace_4360088 : CollatzResearch.WordTrace tailWord_4360088 prefixEnd_4360088 746273613300214123116109 := by
  unfold tailWord_4360088
  simp only [CollatzResearch.WordTrace]
  refine ⟨79512736914076647295696459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106016982552102196394261945 79512736914076647295696459)
  ·
    refine ⟨119269105371114970943544689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79512736914076647295696459 119269105371114970943544689)
    ·
      refine ⟨89451829028336228207658517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119269105371114970943544689 89451829028336228207658517)
      ·
        refine ⟨4193054485703260697233993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89451829028336228207658517 4193054485703260697233993)
        ·
          refine ⟨3144790864277445522925495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4193054485703260697233993 3144790864277445522925495)
          ·
            refine ⟨4717186296416168284388243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144790864277445522925495 4717186296416168284388243)
            ·
              refine ⟨7075779444624252426582365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717186296416168284388243 7075779444624252426582365)
              ·
                refine ⟨2653417291734094659968387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7075779444624252426582365 2653417291734094659968387)
                ·
                  refine ⟨3980125937601141989952581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653417291734094659968387 3980125937601141989952581)
                  ·
                    refine ⟨746273613300214123116109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980125937601141989952581 746273613300214123116109)
                    ·
                      rfl

theorem cell23_4360088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_4360088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360088 prefixEnd_4360088 := by exact prefixLift 4360088
  have htrace : WordTrace (prefixWord ++ tailWord_4360088) baseStart_4360088 baseEnd_4360088 := by
    simpa [prefixWord, tailWord_4360088, baseEnd_4360088] using wordTrace_append hprefix tailTrace_4360088
  have hstable : (prefixWord ++ tailWord_4360088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360088).length < 2 ^ (prefixWord ++ tailWord_4360088).sum := by decide
  have hdescent : baseEnd_4360088 < baseStart_4360088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360120 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_4360120 : Nat := 118140960795 + 4360120 * 2 ^ 59
def prefixEnd_4360120 : Nat := 4983230072969 + 3 ^ 40 * 4360120 * 2
def baseEnd_4360120 : Nat := 2238837271281586244148179

theorem tailTrace_4360120 : CollatzResearch.WordTrace tailWord_4360120 prefixEnd_4360120 2238837271281586244148179 := by
  unfold tailWord_4360120
  simp only [CollatzResearch.WordTrace]
  refine ⟨79513320482018682028278907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106017760642691576037705209 79513320482018682028278907)
  ·
    refine ⟨119269980723028023042418361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79513320482018682028278907 119269980723028023042418361)
    ·
      refine ⟨89452485542271017281813771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119269980723028023042418361 89452485542271017281813771)
      ·
        refine ⟨134178728313406525922720657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89452485542271017281813771 134178728313406525922720657)
        ·
          refine ⟨100634046235054894442040493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134178728313406525922720657 100634046235054894442040493)
          ·
            refine ⟨37737767338145585415765185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100634046235054894442040493 37737767338145585415765185)
            ·
              refine ⟨28303325503609189061823889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37737767338145585415765185 28303325503609189061823889)
              ·
                refine ⟨21227494127706891796367917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28303325503609189061823889 21227494127706891796367917)
                ·
                  refine ⟨7960310297890084423637969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21227494127706891796367917 7960310297890084423637969)
                  ·
                    refine ⟨5970232723417563317728477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7960310297890084423637969 5970232723417563317728477)
                    ·
                      refine ⟨2238837271281586244148179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5970232723417563317728477 2238837271281586244148179)
                      ·
                        rfl

theorem cell23_4360120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_4360120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360120 prefixEnd_4360120 := by exact prefixLift 4360120
  have htrace : WordTrace (prefixWord ++ tailWord_4360120) baseStart_4360120 baseEnd_4360120 := by
    simpa [prefixWord, tailWord_4360120, baseEnd_4360120] using wordTrace_append hprefix tailTrace_4360120
  have hstable : (prefixWord ++ tailWord_4360120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360120).length < 2 ^ (prefixWord ++ tailWord_4360120).sum := by decide
  have hdescent : baseEnd_4360120 < baseStart_4360120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360154 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_4360154 : Nat := 118140960795 + 4360154 * 2 ^ 59
def prefixEnd_4360154 : Nat := 4983230072969 + 3 ^ 40 * 4360154 * 2
def baseEnd_4360154 : Nat := 2238854729623839111123023

theorem tailTrace_4360154 : CollatzResearch.WordTrace tailWord_4360154 prefixEnd_4360154 2238854729623839111123023 := by
  unfold tailWord_4360154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39756970261478546965823879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106018587363942791908863677 39756970261478546965823879)
  ·
    refine ⟨59635455392217820448735819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39756970261478546965823879 59635455392217820448735819)
    ·
      refine ⟨89453183088326730673103729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59635455392217820448735819 89453183088326730673103729)
      ·
        refine ⟨67089887316245048004827797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89453183088326730673103729 67089887316245048004827797)
        ·
          refine ⟨3144838467948986625226303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67089887316245048004827797 3144838467948986625226303)
          ·
            refine ⟨4717257701923479937839455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144838467948986625226303 4717257701923479937839455)
            ·
              refine ⟨7075886552885219906759183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4717257701923479937839455 7075886552885219906759183)
              ·
                refine ⟨10613829829327829860138775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7075886552885219906759183 10613829829327829860138775)
                ·
                  refine ⟨15920744743991744790208163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10613829829327829860138775 15920744743991744790208163)
                  ·
                    refine ⟨23881117115987617185312245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15920744743991744790208163 23881117115987617185312245)
                    ·
                      refine ⟨2238854729623839111123023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23881117115987617185312245 2238854729623839111123023)
                      ·
                        rfl

theorem cell23_4360154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_4360154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360154 prefixEnd_4360154 := by exact prefixLift 4360154
  have htrace : WordTrace (prefixWord ++ tailWord_4360154) baseStart_4360154 baseEnd_4360154 := by
    simpa [prefixWord, tailWord_4360154, baseEnd_4360154] using wordTrace_append hprefix tailTrace_4360154
  have hstable : (prefixWord ++ tailWord_4360154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360154).length < 2 ^ (prefixWord ++ tailWord_4360154).sum := by decide
  have hdescent : baseEnd_4360154 < baseStart_4360154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360162 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_4360162 : Nat := 118140960795 + 4360162 * 2 ^ 59
def prefixEnd_4360162 : Nat := 4983230072969 + 3 ^ 40 * 4360162 * 2
def baseEnd_4360162 : Nat := 2238858837469075079822987

theorem tailTrace_4360162 : CollatzResearch.WordTrace tailWord_4360162 prefixEnd_4360162 2238858837469075079822987 := by
  unfold tailWord_4360162
  simp only [CollatzResearch.WordTrace]
  refine ⟨39757043207471301307396685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106018781886590136819724493 39757043207471301307396685)
  ·
    refine ⟨14908891202801737990273757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39757043207471301307396685 14908891202801737990273757)
    ·
      refine ⟨5590834201050651746352659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14908891202801737990273757 5590834201050651746352659)
      ·
        refine ⟨8386251301575977619528989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590834201050651746352659 8386251301575977619528989)
        ·
          refine ⟨3144844238090991607323371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8386251301575977619528989 3144844238090991607323371)
          ·
            refine ⟨4717266357136487410985057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144844238090991607323371 4717266357136487410985057)
            ·
              refine ⟨3537949767852365558238793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717266357136487410985057 3537949767852365558238793)
              ·
                refine ⟨2653462325889274168679095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3537949767852365558238793 2653462325889274168679095)
                ·
                  refine ⟨3980193488833911253018643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653462325889274168679095 3980193488833911253018643)
                  ·
                    refine ⟨5970290233250866879527965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3980193488833911253018643 5970290233250866879527965)
                    ·
                      refine ⟨2238858837469075079822987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5970290233250866879527965 2238858837469075079822987)
                      ·
                        rfl

theorem cell23_4360162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_4360162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360162 prefixEnd_4360162 := by exact prefixLift 4360162
  have htrace : WordTrace (prefixWord ++ tailWord_4360162) baseStart_4360162 baseEnd_4360162 := by
    simpa [prefixWord, tailWord_4360162, baseEnd_4360162] using wordTrace_append hprefix tailTrace_4360162
  have hstable : (prefixWord ++ tailWord_4360162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360162).length < 2 ^ (prefixWord ++ tailWord_4360162).sum := by decide
  have hdescent : baseEnd_4360162 < baseStart_4360162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360277 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4360277 : Nat := 118140960795 + 4360277 * 2 ^ 59
def prefixEnd_4360277 : Nat := 4983230072969 + 3 ^ 40 * 4360277 * 2
def baseEnd_4360277 : Nat := 746305962581447376628319

theorem tailTrace_4360277 : CollatzResearch.WordTrace tailWord_4360277 prefixEnd_4360277 746305962581447376628319 := by
  unfold tailWord_4360277
  simp only [CollatzResearch.WordTrace]
  refine ⟨159032367224468579870023085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106021578149645719913348723 159032367224468579870023085)
  ·
    refine ⟨59637137709175717451258657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159032367224468579870023085 59637137709175717451258657)
    ·
      refine ⟨44727853281881788088443993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59637137709175717451258657 44727853281881788088443993)
      ·
        refine ⟨33545889961411341066332995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44727853281881788088443993 33545889961411341066332995)
        ·
          refine ⟨50318834942117011599499493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33545889961411341066332995 50318834942117011599499493)
          ·
            refine ⟨9434781551646939674906155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50318834942117011599499493 9434781551646939674906155)
            ·
              refine ⟨14152172327470409512359233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9434781551646939674906155 14152172327470409512359233)
              ·
                refine ⟨10614129245602807134269425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14152172327470409512359233 10614129245602807134269425)
                ·
                  refine ⟨7960596934202105350702069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10614129245602807134269425 7960596934202105350702069)
                  ·
                    refine ⟨746305962581447376628319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7960596934202105350702069 746305962581447376628319)
                    ·
                      rfl

theorem cell23_4360277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4360277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360277 prefixEnd_4360277 := by exact prefixLift 4360277
  have htrace : WordTrace (prefixWord ++ tailWord_4360277) baseStart_4360277 baseEnd_4360277 := by
    simpa [prefixWord, tailWord_4360277, baseEnd_4360277] using wordTrace_append hprefix tailTrace_4360277
  have hstable : (prefixWord ++ tailWord_4360277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360277).length < 2 ^ (prefixWord ++ tailWord_4360277).sum := by decide
  have hdescent : baseEnd_4360277 < baseStart_4360277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360297 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 6, 2]
def baseStart_4360297 : Nat := 118140960795 + 4360297 * 2 ^ 59
def prefixEnd_4360297 : Nat := 4983230072969 + 3 ^ 40 * 4360297 * 2
def baseEnd_4360297 : Nat := 2238928157357432051634865

theorem tailTrace_4360297 : CollatzResearch.WordTrace tailWord_4360297 prefixEnd_4360297 2238928157357432051634865 := by
  unfold tailWord_4360297
  simp only [CollatzResearch.WordTrace]
  refine ⟨159033096684396123285751145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106022064456264082190500763 159033096684396123285751145)
  ·
    refine ⟨119274822513297092464313359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159033096684396123285751145 119274822513297092464313359)
    ·
      refine ⟨178912233769945638696470039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119274822513297092464313359 178912233769945638696470039)
      ·
        refine ⟨268368350654918458044705059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178912233769945638696470039 268368350654918458044705059)
        ·
          refine ⟨402552525982377687067057589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268368350654918458044705059 402552525982377687067057589)
          ·
            refine ⟨37739299310847908162536649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 402552525982377687067057589 37739299310847908162536649)
            ·
              refine ⟨28304474483135931121902487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37739299310847908162536649 28304474483135931121902487)
              ·
                refine ⟨42456711724703896682853731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28304474483135931121902487 42456711724703896682853731)
                ·
                  refine ⟨63685067587055845024280597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42456711724703896682853731 63685067587055845024280597)
                  ·
                    refine ⟨2985237543143242735513153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63685067587055845024280597 2985237543143242735513153)
                    ·
                      refine ⟨2238928157357432051634865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985237543143242735513153 2238928157357432051634865)
                      ·
                        rfl

theorem cell23_4360297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6, 2].length) (baseStart_4360297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360297 prefixEnd_4360297 := by exact prefixLift 4360297
  have htrace : WordTrace (prefixWord ++ tailWord_4360297) baseStart_4360297 baseEnd_4360297 := by
    simpa [prefixWord, tailWord_4360297, baseEnd_4360297] using wordTrace_append hprefix tailTrace_4360297
  have hstable : (prefixWord ++ tailWord_4360297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360297).length < 2 ^ (prefixWord ++ tailWord_4360297).sum := by decide
  have hdescent : baseEnd_4360297 < baseStart_4360297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360354 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 6]
def baseStart_4360354 : Nat := 118140960795 + 4360354 * 2 ^ 59
def prefixEnd_4360354 : Nat := 4983230072969 + 3 ^ 40 * 4360354 * 2
def baseEnd_4360354 : Nat := 248773047306082036513567

theorem tailTrace_4360354 : CollatzResearch.WordTrace tailWord_4360354 prefixEnd_4360354 248773047306082036513567 := by
  unfold tailWord_4360354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39758793911297405505144029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106023450430126414680384077 39758793911297405505144029)
  ·
    refine ⟨14909547716736527064429011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39758793911297405505144029 14909547716736527064429011)
    ·
      refine ⟨22364321575104790596643517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14909547716736527064429011 22364321575104790596643517)
      ·
        refine ⟨8386620590664296473741319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22364321575104790596643517 8386620590664296473741319)
        ·
          refine ⟨12579930885996444710611979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8386620590664296473741319 12579930885996444710611979)
          ·
            refine ⟨18869896328994667065917969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12579930885996444710611979 18869896328994667065917969)
            ·
              refine ⟨14152422246746000299438477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18869896328994667065917969 14152422246746000299438477)
              ·
                refine ⟨5307158342529750112289429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14152422246746000299438477 5307158342529750112289429)
                ·
                  refine ⟨248773047306082036513567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5307158342529750112289429 248773047306082036513567)
                  ·
                    rfl

theorem cell23_4360354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_4360354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360354 prefixEnd_4360354 := by exact prefixLift 4360354
  have htrace : WordTrace (prefixWord ++ tailWord_4360354) baseStart_4360354 baseEnd_4360354 := by
    simpa [prefixWord, tailWord_4360354, baseEnd_4360354] using wordTrace_append hprefix tailTrace_4360354
  have hstable : (prefixWord ++ tailWord_4360354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360354).length < 2 ^ (prefixWord ++ tailWord_4360354).sum := by decide
  have hdescent : baseEnd_4360354 < baseStart_4360354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360367 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 1, 5]
def baseStart_4360367 : Nat := 118140960795 + 4360367 * 2 ^ 59
def prefixEnd_4360367 : Nat := 4983230072969 + 3 ^ 40 * 4360367 * 2
def baseEnd_4360367 : Nat := 746321367001082259253181

theorem tailTrace_4360367 : CollatzResearch.WordTrace tailWord_4360367 prefixEnd_4360367 746321367001082259253181 := by
  unfold tailWord_4360367
  simp only [CollatzResearch.WordTrace]
  refine ⟨159035649794142525240799355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106023766529428350160532903 159035649794142525240799355)
  ·
    refine ⟨238553474691213787861199033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159035649794142525240799355 238553474691213787861199033)
    ·
      refine ⟨178915106018410340895899275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238553474691213787861199033 178915106018410340895899275)
      ·
        refine ⟨268372659027615511343848913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178915106018410340895899275 268372659027615511343848913)
        ·
          refine ⟨201279494270711633507886685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268372659027615511343848913 201279494270711633507886685)
          ·
            refine ⟨75479810351516862565457507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201279494270711633507886685 75479810351516862565457507)
            ·
              refine ⟨113219715527275293848186261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75479810351516862565457507 113219715527275293848186261)
              ·
                refine ⟨5307174165341029399133731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113219715527275293848186261 5307174165341029399133731)
                ·
                  refine ⟨7960761248011544098700597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5307174165341029399133731 7960761248011544098700597)
                  ·
                    refine ⟨746321367001082259253181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7960761248011544098700597 746321367001082259253181)
                    ·
                      rfl

theorem cell23_4360367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_4360367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360367 prefixEnd_4360367 := by exact prefixLift 4360367
  have htrace : WordTrace (prefixWord ++ tailWord_4360367) baseStart_4360367 baseEnd_4360367 := by
    simpa [prefixWord, tailWord_4360367, baseEnd_4360367] using wordTrace_append hprefix tailTrace_4360367
  have hstable : (prefixWord ++ tailWord_4360367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360367).length < 2 ^ (prefixWord ++ tailWord_4360367).sum := by decide
  have hdescent : baseEnd_4360367 < baseStart_4360367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360384 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_4360384 : Nat := 118140960795 + 4360384 * 2 ^ 59
def prefixEnd_4360384 : Nat := 4983230072969 + 3 ^ 40 * 4360384 * 2
def baseEnd_4360384 : Nat := 746324276724791070415655

theorem tailTrace_4360384 : CollatzResearch.WordTrace tailWord_4360384 prefixEnd_4360384 746324276724791070415655 := by
  unfold tailWord_4360384
  simp only [CollatzResearch.WordTrace]
  refine ⟨79518134917540468572084103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106024179890053958096112137 79518134917540468572084103)
  ·
    refine ⟨119277202376310702858126155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79518134917540468572084103 119277202376310702858126155)
    ·
      refine ⟨178915803564466054287189233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119277202376310702858126155 178915803564466054287189233)
      ·
        refine ⟨134186852673349540715391925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178915803564466054287189233 134186852673349540715391925)
        ·
          refine ⟨12580017438126519442067993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134186852673349540715391925 12580017438126519442067993)
          ·
            refine ⟨9435013078594889581550995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12580017438126519442067993 9435013078594889581550995)
            ·
              refine ⟨14152519617892334372326493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435013078594889581550995 14152519617892334372326493)
              ·
                refine ⟨5307194856709625389622435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14152519617892334372326493 5307194856709625389622435)
                ·
                  refine ⟨7960792285064438084433653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5307194856709625389622435 7960792285064438084433653)
                  ·
                    refine ⟨746324276724791070415655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7960792285064438084433653 746324276724791070415655)
                    ·
                      rfl

theorem cell23_4360384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_4360384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360384 prefixEnd_4360384 := by exact prefixLift 4360384
  have htrace : WordTrace (prefixWord ++ tailWord_4360384) baseStart_4360384 baseEnd_4360384 := by
    simpa [prefixWord, tailWord_4360384, baseEnd_4360384] using wordTrace_append hprefix tailTrace_4360384
  have hstable : (prefixWord ++ tailWord_4360384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360384).length < 2 ^ (prefixWord ++ tailWord_4360384).sum := by decide
  have hdescent : baseEnd_4360384 < baseStart_4360384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360398 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_4360398 : Nat := 118140960795 + 4360398 * 2 ^ 59
def prefixEnd_4360398 : Nat := 4983230072969 + 3 ^ 40 * 4360398 * 2
def baseEnd_4360398 : Nat := 2238980018903536156471901

theorem tailTrace_4360398 : CollatzResearch.WordTrace tailWord_4360398 prefixEnd_4360398 2238980018903536156471901 := by
  unfold tailWord_4360398
  simp only [CollatzResearch.WordTrace]
  refine ⟨19879597557128777191897231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106024520304686811690118565 19879597557128777191897231)
  ·
    refine ⟨29819396335693165787845847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19879597557128777191897231 29819396335693165787845847)
    ·
      refine ⟨44729094503539748681768771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29819396335693165787845847 44729094503539748681768771)
      ·
        refine ⟨67093641755309623022653157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44729094503539748681768771 67093641755309623022653157)
        ·
          refine ⟨12580057829120554316747467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67093641755309623022653157 12580057829120554316747467)
          ·
            refine ⟨18870086743680831475121201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12580057829120554316747467 18870086743680831475121201)
            ·
              refine ⟨14152565057760623606340901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18870086743680831475121201 14152565057760623606340901)
              ·
                refine ⟨2653605948330116926188919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14152565057760623606340901 2653605948330116926188919)
                ·
                  refine ⟨3980408922495175389283379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653605948330116926188919 3980408922495175389283379)
                  ·
                    refine ⟨5970613383742763083925069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3980408922495175389283379 5970613383742763083925069)
                    ·
                      refine ⟨2238980018903536156471901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5970613383742763083925069 2238980018903536156471901)
                      ·
                        rfl

theorem cell23_4360398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_4360398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360398 prefixEnd_4360398 := by exact prefixLift 4360398
  have htrace : WordTrace (prefixWord ++ tailWord_4360398) baseStart_4360398 baseEnd_4360398 := by
    simpa [prefixWord, tailWord_4360398, baseEnd_4360398] using wordTrace_append hprefix tailTrace_4360398
  have hstable : (prefixWord ++ tailWord_4360398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360398).length < 2 ^ (prefixWord ++ tailWord_4360398).sum := by decide
  have hdescent : baseEnd_4360398 < baseStart_4360398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360417 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4360417 : Nat := 118140960795 + 4360417 * 2 ^ 59
def prefixEnd_4360417 : Nat := 4983230072969 + 3 ^ 40 * 4360417 * 2
def baseEnd_4360417 : Nat := 2238989775035971582134313

theorem tailTrace_4360417 : CollatzResearch.WordTrace tailWord_4360417 prefixEnd_4360417 2238989775035971582134313 := by
  unfold tailWord_4360417
  simp only [CollatzResearch.WordTrace]
  refine ⟨159037473443961383780119505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106024982295974255853413003 159037473443961383780119505)
  ·
    refine ⟨119278105082971037835089629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159037473443961383780119505 119278105082971037835089629)
    ·
      refine ⟨44729289406114139188158611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119278105082971037835089629 44729289406114139188158611)
      ·
        refine ⟨67093934109171208782237917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44729289406114139188158611 67093934109171208782237917)
        ·
          refine ⟨25160225290939203293339219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67093934109171208782237917 25160225290939203293339219)
          ·
            refine ⟨37740337936408804940008829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25160225290939203293339219 37740337936408804940008829)
            ·
              refine ⟨14152626726153301852503311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37740337936408804940008829 14152626726153301852503311)
              ·
                refine ⟨21228940089229952778754967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14152626726153301852503311 21228940089229952778754967)
                ·
                  refine ⟨31843410133844929168132451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21228940089229952778754967 31843410133844929168132451)
                  ·
                    refine ⟨47765115200767393752198677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31843410133844929168132451 47765115200767393752198677)
                    ·
                      refine ⟨2238989775035971582134313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47765115200767393752198677 2238989775035971582134313)
                      ·
                        rfl

theorem cell23_4360417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4360417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360417 prefixEnd_4360417 := by exact prefixLift 4360417
  have htrace : WordTrace (prefixWord ++ tailWord_4360417) baseStart_4360417 baseEnd_4360417 := by
    simpa [prefixWord, tailWord_4360417, baseEnd_4360417] using wordTrace_append hprefix tailTrace_4360417
  have hstable : (prefixWord ++ tailWord_4360417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360417).length < 2 ^ (prefixWord ++ tailWord_4360417).sum := by decide
  have hdescent : baseEnd_4360417 < baseStart_4360417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360421 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4360421 : Nat := 118140960795 + 4360421 * 2 ^ 59
def prefixEnd_4360421 : Nat := 4983230072969 + 3 ^ 40 * 4360421 * 2
def baseEnd_4360421 : Nat := 2238991828958589566484295

theorem tailTrace_4360421 : CollatzResearch.WordTrace tailWord_4360421 prefixEnd_4360421 2238991828958589566484295 := by
  unfold tailWord_4360421
  simp only [CollatzResearch.WordTrace]
  refine ⟨159037619335946892463265117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106025079557297928308843411 159037619335946892463265117)
  ·
    refine ⟨59639107250980084673724419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159037619335946892463265117 59639107250980084673724419)
    ·
      refine ⟨89458660876470127010586629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59639107250980084673724419 89458660876470127010586629)
      ·
        refine ⟨16773498914338148814484993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89458660876470127010586629 16773498914338148814484993)
        ·
          refine ⟨12580124185753611610863745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16773498914338148814484993 12580124185753611610863745)
          ·
            refine ⟨9435093139315208708147809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12580124185753611610863745 9435093139315208708147809)
            ·
              refine ⟨7076319854486406531110857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9435093139315208708147809 7076319854486406531110857)
              ·
                refine ⟨5307239890864804898333143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7076319854486406531110857 5307239890864804898333143)
                ·
                  refine ⟨7960859836297207347499715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5307239890864804898333143 7960859836297207347499715)
                  ·
                    refine ⟨11941289754445811021249573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7960859836297207347499715 11941289754445811021249573)
                    ·
                      refine ⟨2238991828958589566484295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11941289754445811021249573 2238991828958589566484295)
                      ·
                        rfl

theorem cell23_4360421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4360421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360421 prefixEnd_4360421 := by exact prefixLift 4360421
  have htrace : WordTrace (prefixWord ++ tailWord_4360421) baseStart_4360421 baseEnd_4360421 := by
    simpa [prefixWord, tailWord_4360421, baseEnd_4360421] using wordTrace_append hprefix tailTrace_4360421
  have hstable : (prefixWord ++ tailWord_4360421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360421).length < 2 ^ (prefixWord ++ tailWord_4360421).sum := by decide
  have hdescent : baseEnd_4360421 < baseStart_4360421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360524 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4360524 : Nat := 118140960795 + 4360524 * 2 ^ 59
def prefixEnd_4360524 : Nat := 4983230072969 + 3 ^ 40 * 4360524 * 2
def baseEnd_4360524 : Nat := 2239044717466002663496321

theorem tailTrace_4360524 : CollatzResearch.WordTrace tailWord_4360524 prefixEnd_4360524 2239044717466002663496321 := by
  unfold tailWord_4360524
  simp only [CollatzResearch.WordTrace]
  refine ⟨79520688027286870527132313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106027584036382494036176417 79520688027286870527132313)
  ·
    refine ⟨59640516020465152895349235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79520688027286870527132313 59640516020465152895349235)
    ·
      refine ⟨89460774030697729343023853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59640516020465152895349235 89460774030697729343023853)
      ·
        refine ⟨33547790261511648503633945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89460774030697729343023853 33547790261511648503633945)
        ·
          refine ⟨25160842696133736377725459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33547790261511648503633945 25160842696133736377725459)
          ·
            refine ⟨37741264044200604566588189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25160842696133736377725459 37741264044200604566588189)
            ·
              refine ⟨14152974016575226712470571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37741264044200604566588189 14152974016575226712470571)
              ·
                refine ⟨21229461024862840068705857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14152974016575226712470571 21229461024862840068705857)
                ·
                  refine ⟨15922095768647130051529393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21229461024862840068705857 15922095768647130051529393)
                  ·
                    refine ⟨11941571826485347538647045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15922095768647130051529393 11941571826485347538647045)
                    ·
                      refine ⟨2239044717466002663496321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11941571826485347538647045 2239044717466002663496321)
                      ·
                        rfl

theorem cell23_4360524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4360524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360524 prefixEnd_4360524 := by exact prefixLift 4360524
  have htrace : WordTrace (prefixWord ++ tailWord_4360524) baseStart_4360524 baseEnd_4360524 := by
    simpa [prefixWord, tailWord_4360524, baseEnd_4360524] using wordTrace_append hprefix tailTrace_4360524
  have hstable : (prefixWord ++ tailWord_4360524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360524).length < 2 ^ (prefixWord ++ tailWord_4360524).sum := by decide
  have hdescent : baseEnd_4360524 < baseStart_4360524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360528 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2]
def baseStart_4360528 : Nat := 118140960795 + 4360528 * 2 ^ 59
def prefixEnd_4360528 : Nat := 4983230072969 + 3 ^ 40 * 4360528 * 2
def baseEnd_4360528 : Nat := 2239046771388620647846303

theorem tailTrace_4360528 : CollatzResearch.WordTrace tailWord_4360528 prefixEnd_4360528 2239046771388620647846303 := by
  unfold tailWord_4360528
  simp only [CollatzResearch.WordTrace]
  refine ⟨79520760973279624868705119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106027681297706166491606825 79520760973279624868705119)
  ·
    refine ⟨119281141459919437303057679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79520760973279624868705119 119281141459919437303057679)
    ·
      refine ⟨178921712189879155954586519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119281141459919437303057679 178921712189879155954586519)
      ·
        refine ⟨268382568284818733931879779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178921712189879155954586519 268382568284818733931879779)
        ·
          refine ⟨402573852427228100897819669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268382568284818733931879779 402573852427228100897819669)
          ·
            refine ⟨18870649332526317229585297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 402573852427228100897819669 18870649332526317229585297)
            ·
              refine ⟨14152986999394737922188973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18870649332526317229585297 14152986999394737922188973)
              ·
                refine ⟨5307370124773026720820865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14152986999394737922188973 5307370124773026720820865)
                ·
                  refine ⟨3980527593579770040615649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5307370124773026720820865 3980527593579770040615649)
                  ·
                    refine ⟨2985395695184827530461737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3980527593579770040615649 2985395695184827530461737)
                    ·
                      refine ⟨2239046771388620647846303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985395695184827530461737 2239046771388620647846303)
                      ·
                        rfl

theorem cell23_4360528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2].length) (baseStart_4360528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360528 prefixEnd_4360528 := by exact prefixLift 4360528
  have htrace : WordTrace (prefixWord ++ tailWord_4360528) baseStart_4360528 baseEnd_4360528 := by
    simpa [prefixWord, tailWord_4360528, baseEnd_4360528] using wordTrace_append hprefix tailTrace_4360528
  have hstable : (prefixWord ++ tailWord_4360528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360528).length < 2 ^ (prefixWord ++ tailWord_4360528).sum := by decide
  have hdescent : baseEnd_4360528 < baseStart_4360528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360551 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 5]
def baseStart_4360551 : Nat := 118140960795 + 4360551 * 2 ^ 59
def prefixEnd_4360551 : Nat := 4983230072969 + 3 ^ 40 * 4360551 * 2
def baseEnd_4360551 : Nat := 248784286827074895317633

theorem tailTrace_4360551 : CollatzResearch.WordTrace tailWord_4360551 prefixEnd_4360551 248784286827074895317633 := by
  unfold tailWord_4360551
  simp only [CollatzResearch.WordTrace]
  refine ⟨159042360825475924665497507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106028240550317283110331671 159042360825475924665497507)
  ·
    refine ⟨238563541238213886998246261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159042360825475924665497507 238563541238213886998246261)
    ·
      refine ⟨22365331991082551906085587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238563541238213886998246261 22365331991082551906085587)
      ·
        refine ⟨33547997986623827859128381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22365331991082551906085587 33547997986623827859128381)
        ·
          refine ⟨12580499244983935447173143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33547997986623827859128381 12580499244983935447173143)
          ·
            refine ⟨18870748867475903170759715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12580499244983935447173143 18870748867475903170759715)
            ·
              refine ⟨28306123301213854756139573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18870748867475903170759715 28306123301213854756139573)
              ·
                refine ⟨2653699059488798883388085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28306123301213854756139573 2653699059488798883388085)
                ·
                  refine ⟨248784286827074895317633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2653699059488798883388085 248784286827074895317633)
                  ·
                    rfl

theorem cell23_4360551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 5].length) (baseStart_4360551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360551 prefixEnd_4360551 := by exact prefixLift 4360551
  have htrace : WordTrace (prefixWord ++ tailWord_4360551) baseStart_4360551 baseEnd_4360551 := by
    simpa [prefixWord, tailWord_4360551, baseEnd_4360551] using wordTrace_append hprefix tailTrace_4360551
  have hstable : (prefixWord ++ tailWord_4360551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360551).length < 2 ^ (prefixWord ++ tailWord_4360551).sum := by decide
  have hdescent : baseEnd_4360551 < baseStart_4360551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360584 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4360584 : Nat := 118140960795 + 4360584 * 2 ^ 59
def prefixEnd_4360584 : Nat := 4983230072969 + 3 ^ 40 * 4360584 * 2
def baseEnd_4360584 : Nat := 2239075526305272428746045

theorem tailTrace_4360584 : CollatzResearch.WordTrace tailWord_4360584 prefixEnd_4360584 2239075526305272428746045 := by
  unfold tailWord_4360584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79521782217178185650724403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106029042956237580867632537 79521782217178185650724403)
  ·
    refine ⟨119282673325767278476086605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79521782217178185650724403 119282673325767278476086605)
    ·
      refine ⟨44731002497162729428532477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119282673325767278476086605 44731002497162729428532477)
      ·
        refine ⟨16774125936436023535699679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44731002497162729428532477 16774125936436023535699679)
        ·
          refine ⟨25161188904654035303549519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16774125936436023535699679 25161188904654035303549519)
          ·
            refine ⟨37741783356981052955324279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25161188904654035303549519 37741783356981052955324279)
            ·
              refine ⟨56612675035471579432986419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37741783356981052955324279 56612675035471579432986419)
              ·
                refine ⟨84919012553207369149479629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56612675035471579432986419 84919012553207369149479629)
                ·
                  refine ⟨31844629707452763431054861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84919012553207369149479629 31844629707452763431054861)
                  ·
                    refine ⟨11941736140294786286645573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31844629707452763431054861 11941736140294786286645573)
                    ·
                      refine ⟨2239075526305272428746045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11941736140294786286645573 2239075526305272428746045)
                      ·
                        rfl

theorem cell23_4360584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4360584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360584 prefixEnd_4360584 := by exact prefixLift 4360584
  have htrace : WordTrace (prefixWord ++ tailWord_4360584) baseStart_4360584 baseEnd_4360584 := by
    simpa [prefixWord, tailWord_4360584, baseEnd_4360584] using wordTrace_append hprefix tailTrace_4360584
  have hstable : (prefixWord ++ tailWord_4360584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360584).length < 2 ^ (prefixWord ++ tailWord_4360584).sum := by decide
  have hdescent : baseEnd_4360584 < baseStart_4360584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360651 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 3]
def baseStart_4360651 : Nat := 118140960795 + 4360651 * 2 ^ 59
def prefixEnd_4360651 : Nat := 4983230072969 + 3 ^ 40 * 4360651 * 2
def baseEnd_4360651 : Nat := 2239109929509123666608237

theorem tailTrace_4360651 : CollatzResearch.WordTrace tailWord_4360651 prefixEnd_4360651 2239109929509123666608237 := by
  unfold tailWord_4360651
  simp only [CollatzResearch.WordTrace]
  refine ⟨159046008125113641744137807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106030672083409094496091871 159046008125113641744137807)
  ·
    refine ⟨238569012187670462616206711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159046008125113641744137807 238569012187670462616206711)
    ·
      refine ⟨357853518281505693924310067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238569012187670462616206711 357853518281505693924310067)
      ·
        refine ⟨536780277422258540886465101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357853518281505693924310067 536780277422258540886465101)
        ·
          refine ⟨201292604033346952832424413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536780277422258540886465101 201292604033346952832424413)
          ·
            refine ⟨75484726512505107312159155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201292604033346952832424413 75484726512505107312159155)
            ·
              refine ⟨113227089768757660968238733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75484726512505107312159155 113227089768757660968238733)
              ·
                refine ⟨42460158663284122863089525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113227089768757660968238733 42460158663284122863089525)
                ·
                  refine ⟨3980639874682886518414643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42460158663284122863089525 3980639874682886518414643)
                  ·
                    refine ⟨5970959812024329777621965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3980639874682886518414643 5970959812024329777621965)
                    ·
                      refine ⟨2239109929509123666608237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5970959812024329777621965 2239109929509123666608237)
                      ·
                        rfl

theorem cell23_4360651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 1, 3].length) (baseStart_4360651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360651 prefixEnd_4360651 := by exact prefixLift 4360651
  have htrace : WordTrace (prefixWord ++ tailWord_4360651) baseStart_4360651 baseEnd_4360651 := by
    simpa [prefixWord, tailWord_4360651, baseEnd_4360651] using wordTrace_append hprefix tailTrace_4360651
  have hstable : (prefixWord ++ tailWord_4360651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360651).length < 2 ^ (prefixWord ++ tailWord_4360651).sum := by decide
  have hdescent : baseEnd_4360651 < baseStart_4360651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360684 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_4360684 : Nat := 118140960795 + 4360684 * 2 ^ 59
def prefixEnd_4360684 : Nat := 4983230072969 + 3 ^ 40 * 4360684 * 2
def baseEnd_4360684 : Nat := 746375624790240679165195

theorem tailTrace_4360684 : CollatzResearch.WordTrace tailWord_4360684 prefixEnd_4360684 746375624790240679165195 := by
  unfold tailWord_4360684
  simp only [CollatzResearch.WordTrace]
  refine ⟨79523605866997044190044553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106031474489329392253392737 79523605866997044190044553)
  ·
    refine ⟨59642704400247783142533415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79523605866997044190044553 59642704400247783142533415)
    ·
      refine ⟨89464056600371674713800123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59642704400247783142533415 89464056600371674713800123)
      ·
        refine ⟨134196084900557512070700185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89464056600371674713800123 134196084900557512070700185)
        ·
          refine ⟨100647063675418134053025139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134196084900557512070700185 100647063675418134053025139)
          ·
            refine ⟨150970595513127201079537709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100647063675418134053025139 150970595513127201079537709)
            ·
              refine ⟨56613973317422700404826641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150970595513127201079537709 56613973317422700404826641)
              ·
                refine ⟨42460479988067025303619981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56613973317422700404826641 42460479988067025303619981)
                ·
                  refine ⟨15922679995525134488857493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42460479988067025303619981 15922679995525134488857493)
                  ·
                    refine ⟨746375624790240679165195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15922679995525134488857493 746375624790240679165195)
                    ·
                      rfl

theorem cell23_4360684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_4360684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360684 prefixEnd_4360684 := by exact prefixLift 4360684
  have htrace : WordTrace (prefixWord ++ tailWord_4360684) baseStart_4360684 baseEnd_4360684 := by
    simpa [prefixWord, tailWord_4360684, baseEnd_4360684] using wordTrace_append hprefix tailTrace_4360684
  have hstable : (prefixWord ++ tailWord_4360684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360684).length < 2 ^ (prefixWord ++ tailWord_4360684).sum := by decide
  have hdescent : baseEnd_4360684 < baseStart_4360684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360701 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_4360701 : Nat := 118140960795 + 4360701 * 2 ^ 59
def prefixEnd_4360701 : Nat := 4983230072969 + 3 ^ 40 * 4360701 * 2
def baseEnd_4360701 : Nat := 746378534513949490327669

theorem tailTrace_4360701 : CollatzResearch.WordTrace tailWord_4360701 prefixEnd_4360701 746378534513949490327669 := by
  unfold tailWord_4360701
  simp only [CollatzResearch.WordTrace]
  refine ⟨159047831774932500283457957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106031887849955000188971971 159047831774932500283457957)
  ·
    refine ⟨29821468457799843803148367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159047831774932500283457957 29821468457799843803148367)
    ·
      refine ⟨44732202686699765704722551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29821468457799843803148367 44732202686699765704722551)
      ·
        refine ⟨67098304030049648557083827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44732202686699765704722551 67098304030049648557083827)
        ·
          refine ⟨100647456045074472835625741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67098304030049648557083827 100647456045074472835625741)
          ·
            refine ⟨37742796016902927313359653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100647456045074472835625741 37742796016902927313359653)
            ·
              refine ⟨7076774253169298871254935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37742796016902927313359653 7076774253169298871254935)
              ·
                refine ⟨10615161379753948306882403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7076774253169298871254935 10615161379753948306882403)
                ·
                  refine ⟨15922742069630922460323605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10615161379753948306882403 15922742069630922460323605)
                  ·
                    refine ⟨746378534513949490327669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15922742069630922460323605 746378534513949490327669)
                    ·
                      rfl

theorem cell23_4360701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_4360701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360701 prefixEnd_4360701 := by exact prefixLift 4360701
  have htrace : WordTrace (prefixWord ++ tailWord_4360701) baseStart_4360701 baseEnd_4360701 := by
    simpa [prefixWord, tailWord_4360701, baseEnd_4360701] using wordTrace_append hprefix tailTrace_4360701
  have hstable : (prefixWord ++ tailWord_4360701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360701).length < 2 ^ (prefixWord ++ tailWord_4360701).sum := by decide
  have hdescent : baseEnd_4360701 < baseStart_4360701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360708 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4360708 : Nat := 118140960795 + 4360708 * 2 ^ 59
def prefixEnd_4360708 : Nat := 4983230072969 + 3 ^ 40 * 4360708 * 2
def baseEnd_4360708 : Nat := 2239139197906429943595475

theorem tailTrace_4360708 : CollatzResearch.WordTrace tailWord_4360708 prefixEnd_4360708 2239139197906429943595475 := by
  unfold tailWord_4360708
  simp only [CollatzResearch.WordTrace]
  refine ⟨79524043542953570239481389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106032058057271426985975185 79524043542953570239481389)
  ·
    refine ⟨29821516328607588839805521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79524043542953570239481389 29821516328607588839805521)
    ·
      refine ⟨22366137246455691629854141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29821516328607588839805521 22366137246455691629854141)
      ·
        refine ⟨8387301467420884361195303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22366137246455691629854141 8387301467420884361195303)
        ·
          refine ⟨12580952201131326541792955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387301467420884361195303 12580952201131326541792955)
          ·
            refine ⟨18871428301696989812689433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12580952201131326541792955 18871428301696989812689433)
            ·
              refine ⟨14153571226272742359517075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18871428301696989812689433 14153571226272742359517075)
              ·
                refine ⟨21230356839409113539275613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14153571226272742359517075 21230356839409113539275613)
                ·
                  refine ⟨7961383814778417577228355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21230356839409113539275613 7961383814778417577228355)
                  ·
                    refine ⟨11942075722167626365842533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7961383814778417577228355 11942075722167626365842533)
                    ·
                      refine ⟨2239139197906429943595475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11942075722167626365842533 2239139197906429943595475)
                      ·
                        rfl

theorem cell23_4360708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4360708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360708 prefixEnd_4360708 := by exact prefixLift 4360708
  have htrace : WordTrace (prefixWord ++ tailWord_4360708) baseStart_4360708 baseEnd_4360708 := by
    simpa [prefixWord, tailWord_4360708, baseEnd_4360708] using wordTrace_append hprefix tailTrace_4360708
  have hstable : (prefixWord ++ tailWord_4360708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360708).length < 2 ^ (prefixWord ++ tailWord_4360708).sum := by decide
  have hdescent : baseEnd_4360708 < baseStart_4360708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360741 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_4360741 : Nat := 118140960795 + 4360741 * 2 ^ 59
def prefixEnd_4360741 : Nat := 4983230072969 + 3 ^ 40 * 4360741 * 2
def baseEnd_4360741 : Nat := 2239156142768028314482823

theorem tailTrace_4360741 : CollatzResearch.WordTrace tailWord_4360741 prefixEnd_4360741 2239156142768028314482823 := by
  unfold tailWord_4360741
  simp only [CollatzResearch.WordTrace]
  refine ⟨159049290694787587114914077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106032860463191724743276051 159049290694787587114914077)
  ·
    refine ⟨59643484010545345168092779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159049290694787587114914077 59643484010545345168092779)
    ·
      refine ⟨89465226015818017752139169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59643484010545345168092779 89465226015818017752139169)
      ·
        refine ⟨67098919511863513314104377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89465226015818017752139169 67098919511863513314104377)
        ·
          refine ⟨50324189633897634985578283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67098919511863513314104377 50324189633897634985578283)
          ·
            refine ⟨75486284450846452478367425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50324189633897634985578283 75486284450846452478367425)
            ·
              refine ⟨56614713338134839358775569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75486284450846452478367425 56614713338134839358775569)
              ·
                refine ⟨42461035003601129519081677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56614713338134839358775569 42461035003601129519081677)
                ·
                  refine ⟨15922888126350423569655629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42461035003601129519081677 15922888126350423569655629)
                  ·
                    refine ⟨5971083047381408838620861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15922888126350423569655629 5971083047381408838620861)
                    ·
                      refine ⟨2239156142768028314482823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971083047381408838620861 2239156142768028314482823)
                      ·
                        rfl

theorem cell23_4360741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_4360741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360741 prefixEnd_4360741 := by exact prefixLift 4360741
  have htrace : WordTrace (prefixWord ++ tailWord_4360741) baseStart_4360741 baseEnd_4360741 := by
    simpa [prefixWord, tailWord_4360741, baseEnd_4360741] using wordTrace_append hprefix tailTrace_4360741
  have hstable : (prefixWord ++ tailWord_4360741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360741).length < 2 ^ (prefixWord ++ tailWord_4360741).sum := by decide
  have hdescent : baseEnd_4360741 < baseStart_4360741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360768 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2]
def baseStart_4360768 : Nat := 118140960795 + 4360768 * 2 ^ 59
def prefixEnd_4360768 : Nat := 4983230072969 + 3 ^ 40 * 4360768 * 2
def baseEnd_4360768 : Nat := 2239170006745699708845199

theorem tailTrace_4360768 : CollatzResearch.WordTrace tailWord_4360768 prefixEnd_4360768 2239170006745699708845199 := by
  unfold tailWord_4360768
  simp only [CollatzResearch.WordTrace]
  refine ⟨79525137732844885363073479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106033516977126513817431305 79525137732844885363073479)
  ·
    refine ⟨119287706599267328044610219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79525137732844885363073479 119287706599267328044610219)
    ·
      refine ⟨178931559898900992066915329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119287706599267328044610219 178931559898900992066915329)
      ·
        refine ⟨134198669924175744050186497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178931559898900992066915329 134198669924175744050186497)
        ·
          refine ⟨100649002443131808037639873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134198669924175744050186497 100649002443131808037639873)
          ·
            refine ⟨75486751832348856028229905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100649002443131808037639873 75486751832348856028229905)
            ·
              refine ⟨56615063874261642021172429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75486751832348856028229905 56615063874261642021172429)
              ·
                refine ⟨21230648952848115757939661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56615063874261642021172429 21230648952848115757939661)
                ·
                  refine ⟨7961493357318043409227373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21230648952848115757939661 7961493357318043409227373)
                  ·
                    refine ⟨2985560008994266278460265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7961493357318043409227373 2985560008994266278460265)
                    ·
                      refine ⟨2239170006745699708845199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985560008994266278460265 2239170006745699708845199)
                      ·
                        rfl

theorem cell23_4360768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_4360768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360768 prefixEnd_4360768 := by exact prefixLift 4360768
  have htrace : WordTrace (prefixWord ++ tailWord_4360768) baseStart_4360768 baseEnd_4360768 := by
    simpa [prefixWord, tailWord_4360768, baseEnd_4360768] using wordTrace_append hprefix tailTrace_4360768
  have hstable : (prefixWord ++ tailWord_4360768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360768).length < 2 ^ (prefixWord ++ tailWord_4360768).sum := by decide
  have hdescent : baseEnd_4360768 < baseStart_4360768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360785 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_4360785 : Nat := 118140960795 + 4360785 * 2 ^ 59
def prefixEnd_4360785 : Nat := 4983230072969 + 3 ^ 40 * 4360785 * 2
def baseEnd_4360785 : Nat := 2239178735916826142332621

theorem tailTrace_4360785 : CollatzResearch.WordTrace tailWord_4360785 prefixEnd_4360785 2239178735916826142332621 := by
  unfold tailWord_4360785
  simp only [CollatzResearch.WordTrace]
  refine ⟨159050895506628182629515809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106033930337752121753010539 159050895506628182629515809)
  ·
    refine ⟨119288171629971136972136857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159050895506628182629515809 119288171629971136972136857)
    ·
      refine ⟨89466128722478352729102643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119288171629971136972136857 89466128722478352729102643)
      ·
        refine ⟨134199193083717529093653965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89466128722478352729102643 134199193083717529093653965)
        ·
          refine ⟨50324697406394073410120237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134199193083717529093653965 50324697406394073410120237)
          ·
            refine ⟨18871761527397777528795089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50324697406394073410120237 18871761527397777528795089)
            ·
              refine ⟨14153821145548333146596317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18871761527397777528795089 14153821145548333146596317)
              ·
                refine ⟨5307682929580624929973619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14153821145548333146596317 5307682929580624929973619)
                ·
                  refine ⟨7961524394370937394960429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5307682929580624929973619 7961524394370937394960429)
                  ·
                    refine ⟨2985571647889101523110161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7961524394370937394960429 2985571647889101523110161)
                    ·
                      refine ⟨2239178735916826142332621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985571647889101523110161 2239178735916826142332621)
                      ·
                        rfl

theorem cell23_4360785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_4360785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360785 prefixEnd_4360785 := by exact prefixLift 4360785
  have htrace : WordTrace (prefixWord ++ tailWord_4360785) baseStart_4360785 baseEnd_4360785 := by
    simpa [prefixWord, tailWord_4360785, baseEnd_4360785] using wordTrace_append hprefix tailTrace_4360785
  have hstable : (prefixWord ++ tailWord_4360785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360785).length < 2 ^ (prefixWord ++ tailWord_4360785).sum := by decide
  have hdescent : baseEnd_4360785 < baseStart_4360785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360831 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_4360831 : Nat := 118140960795 + 4360831 * 2 ^ 59
def prefixEnd_4360831 : Nat := 4983230072969 + 3 ^ 40 * 4360831 * 2
def baseEnd_4360831 : Nat := 2239202356026932962357409

theorem tailTrace_4360831 : CollatzResearch.WordTrace tailWord_4360831 prefixEnd_4360831 2239202356026932962357409 := by
  unfold tailWord_4360831
  simp only [CollatzResearch.WordTrace]
  refine ⟨159052573264461532485690347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106035048842974354990460231 159052573264461532485690347)
  ·
    refine ⟨238578859896692298728535521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159052573264461532485690347 238578859896692298728535521)
    ·
      refine ⟨178934144922519224046401641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238578859896692298728535521 178934144922519224046401641)
      ·
        refine ⟨134200608691889418034801231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178934144922519224046401641 134200608691889418034801231)
        ·
          refine ⟨201300913037834127052201847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134200608691889418034801231 201300913037834127052201847)
          ·
            refine ⟨301951369556751190578302771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201300913037834127052201847 301951369556751190578302771)
            ·
              refine ⟨452927054335126785867454157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301951369556751190578302771 452927054335126785867454157)
              ·
                refine ⟨169847645375672544700295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452927054335126785867454157 169847645375672544700295309)
                ·
                  refine ⟨63692867015877204262610741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169847645375672544700295309 63692867015877204262610741)
                  ·
                    refine ⟨5971206282738487899619757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63692867015877204262610741 5971206282738487899619757)
                    ·
                      refine ⟨2239202356026932962357409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971206282738487899619757 2239202356026932962357409)
                      ·
                        rfl

theorem cell23_4360831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_4360831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360831 prefixEnd_4360831 := by exact prefixLift 4360831
  have htrace : WordTrace (prefixWord ++ tailWord_4360831) baseStart_4360831 baseEnd_4360831 := by
    simpa [prefixWord, tailWord_4360831, baseEnd_4360831] using wordTrace_append hprefix tailTrace_4360831
  have hstable : (prefixWord ++ tailWord_4360831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360831).length < 2 ^ (prefixWord ++ tailWord_4360831).sum := by decide
  have hdescent : baseEnd_4360831 < baseStart_4360831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360865 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4360865 : Nat := 118140960795 + 4360865 * 2 ^ 59
def prefixEnd_4360865 : Nat := 4983230072969 + 3 ^ 40 * 4360865 * 2
def baseEnd_4360865 : Nat := 2239219814369185829332253

theorem tailTrace_4360865 : CollatzResearch.WordTrace tailWord_4360865 prefixEnd_4360865 2239219814369185829332253 := by
  unfold tailWord_4360865
  simp only [CollatzResearch.WordTrace]
  refine ⟨159053813346338356292428049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106035875564225570861618699 159053813346338356292428049)
  ·
    refine ⟨119290360009753767219321037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159053813346338356292428049 119290360009753767219321037)
    ·
      refine ⟨44733885003657662707245389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119290360009753767219321037 44733885003657662707245389)
      ·
        refine ⟨16775206876371623515217021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44733885003657662707245389 16775206876371623515217021)
        ·
          refine ⟨6290702578639358818206383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16775206876371623515217021 6290702578639358818206383)
          ·
            refine ⟨9436053867959038227309575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290702578639358818206383 9436053867959038227309575)
            ·
              refine ⟨14154080801938557340964363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9436053867959038227309575 14154080801938557340964363)
              ·
                refine ⟨21231121202907836011446545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154080801938557340964363 21231121202907836011446545)
                ·
                  refine ⟨15923340902180877008584909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21231121202907836011446545 15923340902180877008584909)
                  ·
                    refine ⟨5971252838317828878219341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15923340902180877008584909 5971252838317828878219341)
                    ·
                      refine ⟨2239219814369185829332253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971252838317828878219341 2239219814369185829332253)
                      ·
                        rfl

theorem cell23_4360865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4360865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360865 prefixEnd_4360865 := by exact prefixLift 4360865
  have htrace : WordTrace (prefixWord ++ tailWord_4360865) baseStart_4360865 baseEnd_4360865 := by
    simpa [prefixWord, tailWord_4360865, baseEnd_4360865] using wordTrace_append hprefix tailTrace_4360865
  have hstable : (prefixWord ++ tailWord_4360865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360865).length < 2 ^ (prefixWord ++ tailWord_4360865).sum := by decide
  have hdescent : baseEnd_4360865 < baseStart_4360865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360885 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4360885 : Nat := 118140960795 + 4360885 * 2 ^ 59
def prefixEnd_4360885 : Nat := 4983230072969 + 3 ^ 40 * 4360885 * 2
def baseEnd_4360885 : Nat := 746410027994091917027387

theorem tailTrace_4360885 : CollatzResearch.WordTrace tailWord_4360885 prefixEnd_4360885 746410027994091917027387 := by
  unfold tailWord_4360885
  simp only [CollatzResearch.WordTrace]
  refine ⟨159054542806265899708156109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106036361870843933138770739 159054542806265899708156109)
  ·
    refine ⟨59645453552349712390558541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159054542806265899708156109 59645453552349712390558541)
    ·
      refine ⟨22367045082131142146459453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59645453552349712390558541 22367045082131142146459453)
      ·
        refine ⟨8387641905799178304922295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22367045082131142146459453 8387641905799178304922295)
        ·
          refine ⟨12581462858698767457383443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387641905799178304922295 12581462858698767457383443)
          ·
            refine ⟨18872194288048151186075165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12581462858698767457383443 18872194288048151186075165)
            ·
              refine ⟨7077072858018056694778187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18872194288048151186075165 7077072858018056694778187)
              ·
                refine ⟨10615609287027085042167281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077072858018056694778187 10615609287027085042167281)
                ·
                  refine ⟨7961706965270313781625461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10615609287027085042167281 7961706965270313781625461)
                  ·
                    refine ⟨746410027994091917027387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7961706965270313781625461 746410027994091917027387)
                    ·
                      rfl

theorem cell23_4360885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4360885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360885 prefixEnd_4360885 := by exact prefixLift 4360885
  have htrace : WordTrace (prefixWord ++ tailWord_4360885) baseStart_4360885 baseEnd_4360885 := by
    simpa [prefixWord, tailWord_4360885, baseEnd_4360885] using wordTrace_append hprefix tailTrace_4360885
  have hstable : (prefixWord ++ tailWord_4360885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360885).length < 2 ^ (prefixWord ++ tailWord_4360885).sum := by decide
  have hdescent : baseEnd_4360885 < baseStart_4360885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360938 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_4360938 : Nat := 118140960795 + 4360938 * 2 ^ 59
def prefixEnd_4360938 : Nat := 4983230072969 + 3 ^ 40 * 4360938 * 2
def baseEnd_4360938 : Nat := 2239257298456964043719417

theorem tailTrace_4360938 : CollatzResearch.WordTrace tailWord_4360938 prefixEnd_4360938 2239257298456964043719417 := by
  unfold tailWord_4360938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39764118968768472439958867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106037650583382593173223645 39764118968768472439958867)
  ·
    refine ⟨59646178453152708659938301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39764118968768472439958867 59646178453152708659938301)
    ·
      refine ⟨22367316919932265747476863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59646178453152708659938301 22367316919932265747476863)
      ·
        refine ⟨33550975379898398621215295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22367316919932265747476863 33550975379898398621215295)
        ·
          refine ⟨50326463069847597931822943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33550975379898398621215295 50326463069847597931822943)
          ·
            refine ⟨75489694604771396897734415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50326463069847597931822943 75489694604771396897734415)
            ·
              refine ⟨113234541907157095346601623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75489694604771396897734415 113234541907157095346601623)
              ·
                refine ⟨169851812860735643019902435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113234541907157095346601623 169851812860735643019902435)
                ·
                  refine ⟨254777719291103464529853653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169851812860735643019902435 254777719291103464529853653)
                  ·
                    refine ⟨5971352795885237449918445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 254777719291103464529853653 5971352795885237449918445)
                    ·
                      refine ⟨2239257298456964043719417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971352795885237449918445 2239257298456964043719417)
                      ·
                        rfl

theorem cell23_4360938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_4360938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360938 prefixEnd_4360938 := by exact prefixLift 4360938
  have htrace : WordTrace (prefixWord ++ tailWord_4360938) baseStart_4360938 baseEnd_4360938 := by
    simpa [prefixWord, tailWord_4360938, baseEnd_4360938] using wordTrace_append hprefix tailTrace_4360938
  have hstable : (prefixWord ++ tailWord_4360938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360938).length < 2 ^ (prefixWord ++ tailWord_4360938).sum := by decide
  have hdescent : baseEnd_4360938 < baseStart_4360938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4360992 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_4360992 : Nat := 118140960795 + 4360992 * 2 ^ 59
def prefixEnd_4360992 : Nat := 4983230072969 + 3 ^ 40 * 4360992 * 2
def baseEnd_4360992 : Nat := 746428342137435610814723

theorem tailTrace_4360992 : CollatzResearch.WordTrace tailWord_4360992 prefixEnd_4360992 746428342137435610814723 := by
  unfold tailWord_4360992
  simp only [CollatzResearch.WordTrace]
  refine ⟨79529222708439128491150615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106038963611252171321534153 79529222708439128491150615)
  ·
    refine ⟨119293834062658692736725923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79529222708439128491150615 119293834062658692736725923)
    ·
      refine ⟨178940751093988039105088885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119293834062658692736725923 178940751093988039105088885)
      ·
        refine ⟨16775695415061378666102083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178940751093988039105088885 16775695415061378666102083)
        ·
          refine ⟨25163543122592067999153125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16775695415061378666102083 25163543122592067999153125)
          ·
            refine ⟨4718164335486012749841211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25163543122592067999153125 4718164335486012749841211)
            ·
              refine ⟨7077246503229019124761817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718164335486012749841211 7077246503229019124761817)
              ·
                refine ⟨5307934877421764343571363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7077246503229019124761817 5307934877421764343571363)
                ·
                  refine ⟨7961902316132646515357045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5307934877421764343571363 7961902316132646515357045)
                  ·
                    refine ⟨746428342137435610814723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7961902316132646515357045 746428342137435610814723)
                    ·
                      rfl

theorem cell23_4360992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_4360992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4360992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4360992 prefixEnd_4360992 := by exact prefixLift 4360992
  have htrace : WordTrace (prefixWord ++ tailWord_4360992) baseStart_4360992 baseEnd_4360992 := by
    simpa [prefixWord, tailWord_4360992, baseEnd_4360992] using wordTrace_append hprefix tailTrace_4360992
  have hstable : (prefixWord ++ tailWord_4360992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4360992).length < 2 ^ (prefixWord ++ tailWord_4360992).sum := by decide
  have hdescent : baseEnd_4360992 < baseStart_4360992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4360992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361018 : List Nat := [3, 1, 1, 1, 6, 11]
def baseStart_4361018 : Nat := 118140960795 + 4361018 * 2 ^ 59
def prefixEnd_4361018 : Nat := 4983230072969 + 3 ^ 40 * 4361018 * 2
def baseEnd_4361018 : Nat := 9215219658063060620243

theorem tailTrace_4361018 : CollatzResearch.WordTrace tailWord_4361018 prefixEnd_4361018 9215219658063060620243 := by
  unfold tailWord_4361018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39764848428696015855686927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106039595809856042281831805 39764848428696015855686927)
  ·
    refine ⟨59647272643044023783530391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39764848428696015855686927 59647272643044023783530391)
    ·
      refine ⟨89470908964566035675295587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59647272643044023783530391 89470908964566035675295587)
      ·
        refine ⟨134206363446849053512943381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89470908964566035675295587 134206363446849053512943381)
        ·
          refine ⟨6290923286571049383419221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134206363446849053512943381 6290923286571049383419221)
          ·
            refine ⟨9215219658063060620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6290923286571049383419221 9215219658063060620243)
            ·
              rfl

theorem cell23_4361018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 11].length) (baseStart_4361018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361018 prefixEnd_4361018 := by exact prefixLift 4361018
  have htrace : WordTrace (prefixWord ++ tailWord_4361018) baseStart_4361018 baseEnd_4361018 := by
    simpa [prefixWord, tailWord_4361018, baseEnd_4361018] using wordTrace_append hprefix tailTrace_4361018
  have hstable : (prefixWord ++ tailWord_4361018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361018).length < 2 ^ (prefixWord ++ tailWord_4361018).sum := by decide
  have hdescent : baseEnd_4361018 < baseStart_4361018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361038 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4361038 : Nat := 118140960795 + 4361038 * 2 ^ 59
def prefixEnd_4361038 : Nat := 4983230072969 + 3 ^ 40 * 4361038 * 2
def baseEnd_4361038 : Nat := 2239308646522413652468957

theorem tailTrace_4361038 : CollatzResearch.WordTrace tailWord_4361038 prefixEnd_4361038 2239308646522413652468957 := by
  unfold tailWord_4361038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19882515396838950854809471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106040082116474404558983845 19882515396838950854809471)
  ·
    refine ⟨29823773095258426282214207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19882515396838950854809471 29823773095258426282214207)
    ·
      refine ⟨44735659642887639423321311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29823773095258426282214207 44735659642887639423321311)
      ·
        refine ⟨67103489464331459134981967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44735659642887639423321311 67103489464331459134981967)
        ·
          refine ⟨100655234196497188702472951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67103489464331459134981967 100655234196497188702472951)
          ·
            refine ⟨150982851294745783053709427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100655234196497188702472951 150982851294745783053709427)
            ·
              refine ⟨226474276942118674580564141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150982851294745783053709427 226474276942118674580564141)
              ·
                refine ⟨84927853853294502967711553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226474276942118674580564141 84927853853294502967711553)
                ·
                  refine ⟨63695890389970877225783665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84927853853294502967711553 63695890389970877225783665)
                  ·
                    refine ⟨47771917792478157919337749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63695890389970877225783665 47771917792478157919337749)
                    ·
                      refine ⟨2239308646522413652468957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47771917792478157919337749 2239308646522413652468957)
                      ·
                        rfl

theorem cell23_4361038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4361038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361038 prefixEnd_4361038 := by exact prefixLift 4361038
  have htrace : WordTrace (prefixWord ++ tailWord_4361038) baseStart_4361038 baseEnd_4361038 := by
    simpa [prefixWord, tailWord_4361038, baseEnd_4361038] using wordTrace_append hprefix tailTrace_4361038
  have hstable : (prefixWord ++ tailWord_4361038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361038).length < 2 ^ (prefixWord ++ tailWord_4361038).sum := by decide
  have hdescent : baseEnd_4361038 < baseStart_4361038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361052 : List Nat := [2, 2, 4, 2, 1, 2, 3, 7]
def baseStart_4361052 : Nat := 118140960795 + 4361052 * 2 ^ 59
def prefixEnd_4361052 : Nat := 4983230072969 + 3 ^ 40 * 4361052 * 2
def baseEnd_4361052 : Nat := 82937623527836170284959

theorem tailTrace_4361052 : CollatzResearch.WordTrace tailWord_4361052 prefixEnd_4361052 82937623527836170284959 := by
  unfold tailWord_4361052
  simp only [CollatzResearch.WordTrace]
  refine ⟨79530316898330443614742705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106040422531107258152990273 79530316898330443614742705)
  ·
    refine ⟨59647737673747832711057029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79530316898330443614742705 59647737673747832711057029)
    ·
      refine ⟨11183950813827718633323193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59647737673747832711057029 11183950813827718633323193)
      ·
        refine ⟨8387963110370788974992395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11183950813827718633323193 8387963110370788974992395)
        ·
          refine ⟨12581944665556183462488593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387963110370788974992395 12581944665556183462488593)
          ·
            refine ⟨9436458499167137596866445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12581944665556183462488593 9436458499167137596866445)
            ·
              refine ⟨3538671937187676598824917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9436458499167137596866445 3538671937187676598824917)
              ·
                refine ⟨82937623527836170284959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3538671937187676598824917 82937623527836170284959)
                ·
                  rfl

theorem cell23_4361052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 7].length) (baseStart_4361052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361052 prefixEnd_4361052 := by exact prefixLift 4361052
  have htrace : WordTrace (prefixWord ++ tailWord_4361052) baseStart_4361052 baseEnd_4361052 := by
    simpa [prefixWord, tailWord_4361052, baseEnd_4361052] using wordTrace_append hprefix tailTrace_4361052
  have hstable : (prefixWord ++ tailWord_4361052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361052).length < 2 ^ (prefixWord ++ tailWord_4361052).sum := by decide
  have hdescent : baseEnd_4361052 < baseStart_4361052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361088 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_4361088 : Nat := 118140960795 + 4361088 * 2 ^ 59
def prefixEnd_4361088 : Nat := 4983230072969 + 3 ^ 40 * 4361088 * 2
def baseEnd_4361088 : Nat := 2239334320555138456843727

theorem tailTrace_4361088 : CollatzResearch.WordTrace tailWord_4361088 prefixEnd_4361088 2239334320555138456843727 := by
  unfold tailWord_4361088
  simp only [CollatzResearch.WordTrace]
  refine ⟨79530973412265232688897959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106041297883020310251863945 79530973412265232688897959)
  ·
    refine ⟨119296460118397849033346939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79530973412265232688897959 119296460118397849033346939)
    ·
      refine ⟨178944690177596773550020409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119296460118397849033346939 178944690177596773550020409)
      ·
        refine ⟨134208517633197580162515307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178944690177596773550020409 134208517633197580162515307)
        ·
          refine ⟨201312776449796370243772961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134208517633197580162515307 201312776449796370243772961)
          ·
            refine ⟨150984582337347277682829721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201312776449796370243772961 150984582337347277682829721)
            ·
              refine ⟨113238436753010458262122291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150984582337347277682829721 113238436753010458262122291)
              ·
                refine ⟨169857655129515687393183437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113238436753010458262122291 169857655129515687393183437)
                ·
                  refine ⟨63696620673568382772443789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169857655129515687393183437 63696620673568382772443789)
                  ·
                    refine ⟨23886232752588143539666421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63696620673568382772443789 23886232752588143539666421)
                    ·
                      refine ⟨2239334320555138456843727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23886232752588143539666421 2239334320555138456843727)
                      ·
                        rfl

theorem cell23_4361088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_4361088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361088 prefixEnd_4361088 := by exact prefixLift 4361088
  have htrace : WordTrace (prefixWord ++ tailWord_4361088) baseStart_4361088 baseEnd_4361088 := by
    simpa [prefixWord, tailWord_4361088, baseEnd_4361088] using wordTrace_append hprefix tailTrace_4361088
  have hstable : (prefixWord ++ tailWord_4361088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361088).length < 2 ^ (prefixWord ++ tailWord_4361088).sum := by decide
  have hdescent : baseEnd_4361088 < baseStart_4361088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361095 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 6]
def baseStart_4361095 : Nat := 118140960795 + 4361095 * 2 ^ 59
def prefixEnd_4361095 : Nat := 4983230072969 + 3 ^ 40 * 4361095 * 2
def baseEnd_4361095 : Nat := 746445971639906643152065

theorem tailTrace_4361095 : CollatzResearch.WordTrace tailWord_4361095 prefixEnd_4361095 746445971639906643152065 := by
  unfold tailWord_4361095
  simp only [CollatzResearch.WordTrace]
  refine ⟨159062202135505105573300739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106041468090336737048867159 159062202135505105573300739)
  ·
    refine ⟨238593303203257658359951109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159062202135505105573300739 238593303203257658359951109)
    ·
      refine ⟨44736244350610810942490833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238593303203257658359951109 44736244350610810942490833)
      ·
        refine ⟨33552183262958108206868125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44736244350610810942490833 33552183262958108206868125)
        ·
          refine ⟨12582068723609290577575547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33552183262958108206868125 12582068723609290577575547)
          ·
            refine ⟨18873103085413935866363321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582068723609290577575547 18873103085413935866363321)
            ·
              refine ⟨14154827314060451899772491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18873103085413935866363321 14154827314060451899772491)
              ·
                refine ⟨21232240971090677849658737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154827314060451899772491 21232240971090677849658737)
                ·
                  refine ⟨15924180728318008387244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21232240971090677849658737 15924180728318008387244053)
                  ·
                    refine ⟨746445971639906643152065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15924180728318008387244053 746445971639906643152065)
                    ·
                      rfl

theorem cell23_4361095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_4361095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361095 prefixEnd_4361095 := by exact prefixLift 4361095
  have htrace : WordTrace (prefixWord ++ tailWord_4361095) baseStart_4361095 baseEnd_4361095 := by
    simpa [prefixWord, tailWord_4361095, baseEnd_4361095] using wordTrace_append hprefix tailTrace_4361095
  have hstable : (prefixWord ++ tailWord_4361095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361095).length < 2 ^ (prefixWord ++ tailWord_4361095).sum := by decide
  have hdescent : baseEnd_4361095 < baseStart_4361095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361096 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_4361096 : Nat := 118140960795 + 4361096 * 2 ^ 59
def prefixEnd_4361096 : Nat := 4983230072969 + 3 ^ 40 * 4361096 * 2
def baseEnd_4361096 : Nat := 2239338428400374425543691

theorem tailTrace_4361096 : CollatzResearch.WordTrace tailWord_4361096 prefixEnd_4361096 2239338428400374425543691 := by
  unfold tailWord_4361096
  simp only [CollatzResearch.WordTrace]
  refine ⟨79531119304250741372043571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106041492405667655162724761 79531119304250741372043571)
  ·
    refine ⟨119296678956376112058065357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79531119304250741372043571 119296678956376112058065357)
    ·
      refine ⟨44736254608641042021774509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119296678956376112058065357 44736254608641042021774509)
      ·
        refine ⟨16776095478240390758165441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44736254608641042021774509 16776095478240390758165441)
        ·
          refine ⟨12582071608680293068624081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16776095478240390758165441 12582071608680293068624081)
          ·
            refine ⟨9436553706510219801468061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12582071608680293068624081 9436553706510219801468061)
            ·
              refine ⟨3538707639941332425550523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9436553706510219801468061 3538707639941332425550523)
              ·
                refine ⟨5308061459911998638325785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538707639941332425550523 5308061459911998638325785)
                ·
                  refine ⟨3981046094933998978744339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5308061459911998638325785 3981046094933998978744339)
                  ·
                    refine ⟨5971569142400998468116509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981046094933998978744339 5971569142400998468116509)
                    ·
                      refine ⟨2239338428400374425543691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971569142400998468116509 2239338428400374425543691)
                      ·
                        rfl

theorem cell23_4361096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_4361096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361096 prefixEnd_4361096 := by exact prefixLift 4361096
  have htrace : WordTrace (prefixWord ++ tailWord_4361096) baseStart_4361096 baseEnd_4361096 := by
    simpa [prefixWord, tailWord_4361096, baseEnd_4361096] using wordTrace_append hprefix tailTrace_4361096
  have hstable : (prefixWord ++ tailWord_4361096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361096).length < 2 ^ (prefixWord ++ tailWord_4361096).sum := by decide
  have hdescent : baseEnd_4361096 < baseStart_4361096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361119 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4361119 : Nat := 118140960795 + 4361119 * 2 ^ 59
def prefixEnd_4361119 : Nat := 4983230072969 + 3 ^ 40 * 4361119 * 2
def baseEnd_4361119 : Nat := 2239350238455427835556085

theorem tailTrace_4361119 : CollatzResearch.WordTrace tailWord_4361119 prefixEnd_4361119 2239350238455427835556085 := by
  unfold tailWord_4361119
  simp only [CollatzResearch.WordTrace]
  refine ⟨159063077487418157672174411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106042051658278771781449607 159063077487418157672174411)
  ·
    refine ⟨238594616231127236508261617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159063077487418157672174411 238594616231127236508261617)
    ·
      refine ⟨178945962173345427381196213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238594616231127236508261617 178945962173345427381196213)
      ·
        refine ⟨16776183953751133816987145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178945962173345427381196213 16776183953751133816987145)
        ·
          refine ⟨12582137965313350362740359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16776183953751133816987145 12582137965313350362740359)
          ·
            refine ⟨18873206947970025544110539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582137965313350362740359 18873206947970025544110539)
            ·
              refine ⟨28309810421955038316165809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18873206947970025544110539 28309810421955038316165809)
              ·
                refine ⟨21232357816466278737124357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28309810421955038316165809 21232357816466278737124357)
                ·
                  refine ⟨3981067090587427263210817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21232357816466278737124357 3981067090587427263210817)
                  ·
                    refine ⟨2985800317940570447408113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981067090587427263210817 2985800317940570447408113)
                    ·
                      refine ⟨2239350238455427835556085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985800317940570447408113 2239350238455427835556085)
                      ·
                        rfl

theorem cell23_4361119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4361119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361119 prefixEnd_4361119 := by exact prefixLift 4361119
  have htrace : WordTrace (prefixWord ++ tailWord_4361119) baseStart_4361119 baseEnd_4361119 := by
    simpa [prefixWord, tailWord_4361119, baseEnd_4361119] using wordTrace_append hprefix tailTrace_4361119
  have hstable : (prefixWord ++ tailWord_4361119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361119).length < 2 ^ (prefixWord ++ tailWord_4361119).sum := by decide
  have hdescent : baseEnd_4361119 < baseStart_4361119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361122 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4361122 : Nat := 118140960795 + 4361122 * 2 ^ 59
def prefixEnd_4361122 : Nat := 4983230072969 + 3 ^ 40 * 4361122 * 2
def baseEnd_4361122 : Nat := 2239351778897391323818571

theorem tailTrace_4361122 : CollatzResearch.WordTrace tailWord_4361122 prefixEnd_4361122 2239351778897391323818571 := by
  unfold tailWord_4361122
  simp only [CollatzResearch.WordTrace]
  refine ⟨39765796726601822296133405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106042124604271526123022413 39765796726601822296133405)
  ·
    refine ⟨14912173772475683361050027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39765796726601822296133405 14912173772475683361050027)
    ·
      refine ⟨22368260658713525041575041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14912173772475683361050027 22368260658713525041575041)
      ·
        refine ⟨16776195494035143781181281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22368260658713525041575041 16776195494035143781181281)
        ·
          refine ⟨12582146620526357835885961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16776195494035143781181281 12582146620526357835885961)
          ·
            refine ⟨9436609965394768376914471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12582146620526357835885961 9436609965394768376914471)
            ·
              refine ⟨14154914948092152565371707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9436609965394768376914471 14154914948092152565371707)
              ·
                refine ⟨21232372422138228848057561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154914948092152565371707 21232372422138228848057561)
                ·
                  refine ⟨15924279316603671636043171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21232372422138228848057561 15924279316603671636043171)
                  ·
                    refine ⟨23886418974905507454064757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15924279316603671636043171 23886418974905507454064757)
                    ·
                      refine ⟨2239351778897391323818571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23886418974905507454064757 2239351778897391323818571)
                      ·
                        rfl

theorem cell23_4361122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4361122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361122 prefixEnd_4361122 := by exact prefixLift 4361122
  have htrace : WordTrace (prefixWord ++ tailWord_4361122) baseStart_4361122 baseEnd_4361122 := by
    simpa [prefixWord, tailWord_4361122, baseEnd_4361122] using wordTrace_append hprefix tailTrace_4361122
  have hstable : (prefixWord ++ tailWord_4361122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361122).length < 2 ^ (prefixWord ++ tailWord_4361122).sum := by decide
  have hdescent : baseEnd_4361122 < baseStart_4361122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361135 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_4361135 : Nat := 118140960795 + 4361135 * 2 ^ 59
def prefixEnd_4361135 : Nat := 4983230072969 + 3 ^ 40 * 4361135 * 2
def baseEnd_4361135 : Nat := 2239358454145899772956011

theorem tailTrace_4361135 : CollatzResearch.WordTrace tailWord_4361135 prefixEnd_4361135 2239358454145899772956011 := by
  unfold tailWord_4361135
  simp only [CollatzResearch.WordTrace]
  refine ⟨159063661055360192404756859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106042440703573461603171239 159063661055360192404756859)
  ·
    refine ⟨238595491583040288607135289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159063661055360192404756859 238595491583040288607135289)
    ·
      refine ⟨178946618687280216455351467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238595491583040288607135289 178946618687280216455351467)
      ·
        refine ⟨268419928030920324683027201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178946618687280216455351467 268419928030920324683027201)
        ·
          refine ⟨201314946023190243512270401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268419928030920324683027201 201314946023190243512270401)
          ·
            refine ⟨150986209517392682634202801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201314946023190243512270401 150986209517392682634202801)
            ·
              refine ⟨113239657138044511975652101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150986209517392682634202801 113239657138044511975652101)
              ·
                refine ⟨21232435713383345995434769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113239657138044511975652101 21232435713383345995434769)
                ·
                  refine ⟨15924326785037509496576077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21232435713383345995434769 15924326785037509496576077)
                  ·
                    refine ⟨5971622544389066061216029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15924326785037509496576077 5971622544389066061216029)
                    ·
                      refine ⟨2239358454145899772956011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971622544389066061216029 2239358454145899772956011)
                      ·
                        rfl

theorem cell23_4361135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_4361135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361135 prefixEnd_4361135 := by exact prefixLift 4361135
  have htrace : WordTrace (prefixWord ++ tailWord_4361135) baseStart_4361135 baseEnd_4361135 := by
    simpa [prefixWord, tailWord_4361135, baseEnd_4361135] using wordTrace_append hprefix tailTrace_4361135
  have hstable : (prefixWord ++ tailWord_4361135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361135).length < 2 ^ (prefixWord ++ tailWord_4361135).sum := by decide
  have hdescent : baseEnd_4361135 < baseStart_4361135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361172 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4361172 : Nat := 118140960795 + 4361172 * 2 ^ 59
def prefixEnd_4361172 : Nat := 4983230072969 + 3 ^ 40 * 4361172 * 2
def baseEnd_4361172 : Nat := 746459150976705376064447

theorem tailTrace_4361172 : CollatzResearch.WordTrace tailWord_4361172 prefixEnd_4361172 746459150976705376064447 := by
  unfold tailWord_4361172
  simp only [CollatzResearch.WordTrace]
  refine ⟨79532505278113073861926885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106043340370817431815902513 79532505278113073861926885)
  ·
    refine ⟨14912344739646201349111291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79532505278113073861926885 14912344739646201349111291)
    ·
      refine ⟨22368517109469302023666937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14912344739646201349111291 22368517109469302023666937)
      ·
        refine ⟨16776387832101976517750203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22368517109469302023666937 16776387832101976517750203)
        ·
          refine ⟨25164581748152964776625305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16776387832101976517750203 25164581748152964776625305)
          ·
            refine ⟨18873436311114723582468979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25164581748152964776625305 18873436311114723582468979)
            ·
              refine ⟨28310154466672085373703469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18873436311114723582468979 28310154466672085373703469)
              ·
                refine ⟨10616307925002032015138801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28310154466672085373703469 10616307925002032015138801)
                ·
                  refine ⟨7962230943751524011354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10616307925002032015138801 7962230943751524011354101)
                  ·
                    refine ⟨746459150976705376064447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7962230943751524011354101 746459150976705376064447)
                    ·
                      rfl

theorem cell23_4361172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4361172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361172 prefixEnd_4361172 := by exact prefixLift 4361172
  have htrace : WordTrace (prefixWord ++ tailWord_4361172) baseStart_4361172 baseEnd_4361172 := by
    simpa [prefixWord, tailWord_4361172, baseEnd_4361172] using wordTrace_append hprefix tailTrace_4361172
  have hstable : (prefixWord ++ tailWord_4361172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361172).length < 2 ^ (prefixWord ++ tailWord_4361172).sum := by decide
  have hdescent : baseEnd_4361172 < baseStart_4361172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361192 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4361192 : Nat := 118140960795 + 4361192 * 2 ^ 59
def prefixEnd_4361192 : Nat := 4983230072969 + 3 ^ 40 * 4361192 * 2
def baseEnd_4361192 : Nat := 2239387722543206049943249

theorem tailTrace_4361192 : CollatzResearch.WordTrace tailWord_4361192 prefixEnd_4361192 2239387722543206049943249 := by
  unfold tailWord_4361192
  simp only [CollatzResearch.WordTrace]
  refine ⟨79532870008076845569790915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106043826677435794093054553 79532870008076845569790915)
  ·
    refine ⟨119299305012115268354686373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79532870008076845569790915 119299305012115268354686373)
    ·
      refine ⟨22368619689771612816503695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119299305012115268354686373 22368619689771612816503695)
      ·
        refine ⟨33552929534657419224755543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22368619689771612816503695 33552929534657419224755543)
        ·
          refine ⟨50329394301986128837133315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33552929534657419224755543 50329394301986128837133315)
          ·
            refine ⟨75494091452979193255699973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50329394301986128837133315 75494091452979193255699973)
            ·
              refine ⟨14155142147433598735443745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75494091452979193255699973 14155142147433598735443745)
              ·
                refine ⟨10616356610575199051582809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14155142147433598735443745 10616356610575199051582809)
                ·
                  refine ⟨7962267457931399288687107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10616356610575199051582809 7962267457931399288687107)
                  ·
                    refine ⟨11943401186897098933030661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7962267457931399288687107 11943401186897098933030661)
                    ·
                      refine ⟨2239387722543206049943249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11943401186897098933030661 2239387722543206049943249)
                      ·
                        rfl

theorem cell23_4361192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4361192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361192 prefixEnd_4361192 := by exact prefixLift 4361192
  have htrace : WordTrace (prefixWord ++ tailWord_4361192) baseStart_4361192 baseEnd_4361192 := by
    simpa [prefixWord, tailWord_4361192, baseEnd_4361192] using wordTrace_append hprefix tailTrace_4361192
  have hstable : (prefixWord ++ tailWord_4361192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361192).length < 2 ^ (prefixWord ++ tailWord_4361192).sum := by decide
  have hdescent : baseEnd_4361192 < baseStart_4361192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361195 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3]
def baseStart_4361195 : Nat := 118140960795 + 4361195 * 2 ^ 59
def prefixEnd_4361195 : Nat := 4983230072969 + 3 ^ 40 * 4361195 * 2
def baseEnd_4361195 : Nat := 2239389262985169538205735

theorem tailTrace_4361195 : CollatzResearch.WordTrace tailWord_4361195 prefixEnd_4361195 2239389262985169538205735 := by
  unfold tailWord_4361195
  simp only [CollatzResearch.WordTrace]
  refine ⟨159065849435142822651941039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106043899623428548434627359 159065849435142822651941039)
  ·
    refine ⟨238598774152714233977911559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159065849435142822651941039 238598774152714233977911559)
    ·
      refine ⟨357898161229071350966867339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238598774152714233977911559 357898161229071350966867339)
      ·
        refine ⟨536847241843607026450301009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357898161229071350966867339 536847241843607026450301009)
        ·
          refine ⟨402635431382705269837725757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536847241843607026450301009 402635431382705269837725757)
          ·
            refine ⟨150988286768514476189147159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402635431382705269837725757 150988286768514476189147159)
            ·
              refine ⟨226482430152771714283720739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150988286768514476189147159 226482430152771714283720739)
              ·
                refine ⟨339723645229157571425581109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226482430152771714283720739 339723645229157571425581109)
                ·
                  refine ⟨31849091740233522321148229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339723645229157571425581109 31849091740233522321148229)
                  ·
                    refine ⟨5971704701293785435215293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31849091740233522321148229 5971704701293785435215293)
                    ·
                      refine ⟨2239389262985169538205735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971704701293785435215293 2239389262985169538205735)
                      ·
                        rfl

theorem cell23_4361195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].length) (baseStart_4361195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361195 prefixEnd_4361195 := by exact prefixLift 4361195
  have htrace : WordTrace (prefixWord ++ tailWord_4361195) baseStart_4361195 baseEnd_4361195 := by
    simpa [prefixWord, tailWord_4361195, baseEnd_4361195] using wordTrace_append hprefix tailTrace_4361195
  have hstable : (prefixWord ++ tailWord_4361195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361195).length < 2 ^ (prefixWord ++ tailWord_4361195).sum := by decide
  have hdescent : baseEnd_4361195 < baseStart_4361195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361249 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 6]
def baseStart_4361249 : Nat := 118140960795 + 4361249 * 2 ^ 59
def prefixEnd_4361249 : Nat := 4983230072969 + 3 ^ 40 * 4361249 * 2
def baseEnd_4361249 : Nat := 248824110104501369658943

theorem tailTrace_4361249 : CollatzResearch.WordTrace tailWord_4361249 prefixEnd_4361249 248824110104501369658943 := by
  unfold tailWord_4361249
  simp only [CollatzResearch.WordTrace]
  refine ⟨159067818976947189874406801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106045212651298126582937867 159067818976947189874406801)
  ·
    refine ⟨119300864232710392405805101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159067818976947189874406801 119300864232710392405805101)
    ·
      refine ⟨44737824087266397152176913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119300864232710392405805101 44737824087266397152176913)
      ·
        refine ⟨33553368065449797864132685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44737824087266397152176913 33553368065449797864132685)
        ·
          refine ⟨12582513024543674199049757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33553368065449797864132685 12582513024543674199049757)
          ·
            refine ⟨4718442384203877824643659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12582513024543674199049757 4718442384203877824643659)
            ·
              refine ⟨7077663576305816736965489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718442384203877824643659 7077663576305816736965489)
              ·
                refine ⟨5308247682229362552724117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7077663576305816736965489 5308247682229362552724117)
                ·
                  refine ⟨248824110104501369658943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5308247682229362552724117 248824110104501369658943)
                  ·
                    rfl

theorem cell23_4361249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_4361249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361249 prefixEnd_4361249 := by exact prefixLift 4361249
  have htrace : WordTrace (prefixWord ++ tailWord_4361249) baseStart_4361249 baseEnd_4361249 := by
    simpa [prefixWord, tailWord_4361249, baseEnd_4361249] using wordTrace_append hprefix tailTrace_4361249
  have hstable : (prefixWord ++ tailWord_4361249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361249).length < 2 ^ (prefixWord ++ tailWord_4361249).sum := by decide
  have hdescent : baseEnd_4361249 < baseStart_4361249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361252 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4361252 : Nat := 118140960795 + 4361252 * 2 ^ 59
def prefixEnd_4361252 : Nat := 4983230072969 + 3 ^ 40 * 4361252 * 2
def baseEnd_4361252 : Nat := 2239418531382475815192973

theorem tailTrace_4361252 : CollatzResearch.WordTrace tailWord_4361252 prefixEnd_4361252 2239418531382475815192973 := by
  unfold tailWord_4361252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79533964197968160693383005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106045285597290880924510673 79533964197968160693383005)
  ·
    refine ⟨29825236574238060260018627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79533964197968160693383005 29825236574238060260018627)
    ·
      refine ⟨44737854861357090390027941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29825236574238060260018627 44737854861357090390027941)
      ·
        refine ⟨8388347786504454448130239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44737854861357090390027941 8388347786504454448130239)
        ·
          refine ⟨12582521679756681672195359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388347786504454448130239 12582521679756681672195359)
          ·
            refine ⟨18873782519635022508293039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582521679756681672195359 18873782519635022508293039)
            ·
              refine ⟨28310673779452533762439559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18873782519635022508293039 28310673779452533762439559)
              ·
                refine ⟨42466010669178800643659339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28310673779452533762439559 42466010669178800643659339)
                ·
                  refine ⟨63699016003768200965489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42466010669178800643659339 63699016003768200965489009)
                  ·
                    refine ⟨47774262002826150724116757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63699016003768200965489009 47774262002826150724116757)
                    ·
                      refine ⟨2239418531382475815192973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47774262002826150724116757 2239418531382475815192973)
                      ·
                        rfl

theorem cell23_4361252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4361252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361252 prefixEnd_4361252 := by exact prefixLift 4361252
  have htrace : WordTrace (prefixWord ++ tailWord_4361252) baseStart_4361252 baseEnd_4361252 := by
    simpa [prefixWord, tailWord_4361252, baseEnd_4361252] using wordTrace_append hprefix tailTrace_4361252
  have hstable : (prefixWord ++ tailWord_4361252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361252).length < 2 ^ (prefixWord ++ tailWord_4361252).sum := by decide
  have hdescent : baseEnd_4361252 < baseStart_4361252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361259 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 3]
def baseStart_4361259 : Nat := 118140960795 + 4361259 * 2 ^ 59
def prefixEnd_4361259 : Nat := 4983230072969 + 3 ^ 40 * 4361259 * 2
def baseEnd_4361259 : Nat := 2239422125747057287805441

theorem tailTrace_4361259 : CollatzResearch.WordTrace tailWord_4361259 prefixEnd_4361259 2239422125747057287805441 := by
  unfold tailWord_4361259
  simp only [CollatzResearch.WordTrace]
  refine ⟨159068183706910961582270831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106045455804607307721513887 159068183706910961582270831)
  ·
    refine ⟨238602275560366442373406247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159068183706910961582270831 238602275560366442373406247)
    ·
      refine ⟨357903413340549663560109371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238602275560366442373406247 357903413340549663560109371)
      ·
        refine ⟨536855120010824495340164057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357903413340549663560109371 536855120010824495340164057)
        ·
          refine ⟨402641340008118371505123043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536855120010824495340164057 402641340008118371505123043)
          ·
            refine ⟨603962010012177557257684565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402641340008118371505123043 603962010012177557257684565)
            ·
              refine ⟨7077679804830205749113491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 603962010012177557257684565 7077679804830205749113491)
              ·
                refine ⟨10616519707245308623670237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077679804830205749113491 10616519707245308623670237)
                ·
                  refine ⟨3981194890216990733876339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10616519707245308623670237 3981194890216990733876339)
                  ·
                    refine ⟨5971792335325486100814509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981194890216990733876339 5971792335325486100814509)
                    ·
                      refine ⟨2239422125747057287805441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971792335325486100814509 2239422125747057287805441)
                      ·
                        rfl

theorem cell23_4361259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 1, 3].length) (baseStart_4361259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361259 prefixEnd_4361259 := by exact prefixLift 4361259
  have htrace : WordTrace (prefixWord ++ tailWord_4361259) baseStart_4361259 baseEnd_4361259 := by
    simpa [prefixWord, tailWord_4361259, baseEnd_4361259] using wordTrace_append hprefix tailTrace_4361259
  have hstable : (prefixWord ++ tailWord_4361259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361259).length < 2 ^ (prefixWord ++ tailWord_4361259).sum := by decide
  have hdescent : baseEnd_4361259 < baseStart_4361259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361295 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_4361295 : Nat := 118140960795 + 4361295 * 2 ^ 59
def prefixEnd_4361295 : Nat := 4983230072969 + 3 ^ 40 * 4361295 * 2
def baseEnd_4361295 : Nat := 2239440611050619146955275

theorem tailTrace_4361295 : CollatzResearch.WordTrace tailWord_4361295 prefixEnd_4361295 2239440611050619146955275 := by
  unfold tailWord_4361295
  simp only [CollatzResearch.WordTrace]
  refine ⟨159069496734780539730581339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106046331156520359820387559 159069496734780539730581339)
  ·
    refine ⟨238604245102170809595872009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159069496734780539730581339 238604245102170809595872009)
    ·
      refine ⟨178953183826628107196904007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238604245102170809595872009 178953183826628107196904007)
      ·
        refine ⟨268429775739942160795356011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178953183826628107196904007 268429775739942160795356011)
        ·
          refine ⟨402644663609913241193034017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268429775739942160795356011 402644663609913241193034017)
          ·
            refine ⟨301983497707434930894775513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402644663609913241193034017 301983497707434930894775513)
            ·
              refine ⟨226487623280576198171081635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301983497707434930894775513 226487623280576198171081635)
              ·
                refine ⟨339731434920864297256622453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226487623280576198171081635 339731434920864297256622453)
                ·
                  refine ⟨31849822023831027867808355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339731434920864297256622453 31849822023831027867808355)
                  ·
                    refine ⟨47774733035746541801712533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31849822023831027867808355 47774733035746541801712533)
                    ·
                      refine ⟨2239440611050619146955275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47774733035746541801712533 2239440611050619146955275)
                      ·
                        rfl

theorem cell23_4361295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_4361295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361295 prefixEnd_4361295 := by exact prefixLift 4361295
  have htrace : WordTrace (prefixWord ++ tailWord_4361295) baseStart_4361295 baseEnd_4361295 := by
    simpa [prefixWord, tailWord_4361295, baseEnd_4361295] using wordTrace_append hprefix tailTrace_4361295
  have hstable : (prefixWord ++ tailWord_4361295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361295).length < 2 ^ (prefixWord ++ tailWord_4361295).sum := by decide
  have hdescent : baseEnd_4361295 < baseStart_4361295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361299 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 7, 2, 2]
def baseStart_4361299 : Nat := 118140960795 + 4361299 * 2 ^ 59
def prefixEnd_4361299 : Nat := 4983230072969 + 3 ^ 40 * 4361299 * 2
def baseEnd_4361299 : Nat := 2239442664973237131305257

theorem tailTrace_4361299 : CollatzResearch.WordTrace tailWord_4361299 prefixEnd_4361299 2239442664973237131305257 := by
  unfold tailWord_4361299
  simp only [CollatzResearch.WordTrace]
  refine ⟨159069642626766048413726951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106046428417844032275817967 159069642626766048413726951)
  ·
    refine ⟨238604463940149072620590427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159069642626766048413726951 238604463940149072620590427)
    ·
      refine ⟨357906695910223608930885641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238604463940149072620590427 357906695910223608930885641)
      ·
        refine ⟨268430021932667706698164231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357906695910223608930885641 268430021932667706698164231)
        ·
          refine ⟨402645032899001560047246347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268430021932667706698164231 402645032899001560047246347)
          ·
            refine ⟨603967549348502340070869521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402645032899001560047246347 603967549348502340070869521)
            ·
              refine ⟨452975662011376755053152141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603967549348502340070869521 452975662011376755053152141)
              ·
                refine ⟨169865873254266283144932053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452975662011376755053152141 169865873254266283144932053)
                ·
                  refine ⟨3981231404396866011209345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169865873254266283144932053 3981231404396866011209345)
                  ·
                    refine ⟨2985923553297649508407009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981231404396866011209345 2985923553297649508407009)
                    ·
                      refine ⟨2239442664973237131305257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985923553297649508407009 2239442664973237131305257)
                      ·
                        rfl

theorem cell23_4361299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2, 2].length) (baseStart_4361299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361299 prefixEnd_4361299 := by exact prefixLift 4361299
  have htrace : WordTrace (prefixWord ++ tailWord_4361299) baseStart_4361299 baseEnd_4361299 := by
    simpa [prefixWord, tailWord_4361299, baseEnd_4361299] using wordTrace_append hprefix tailTrace_4361299
  have hstable : (prefixWord ++ tailWord_4361299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361299).length < 2 ^ (prefixWord ++ tailWord_4361299).sum := by decide
  have hdescent : baseEnd_4361299 < baseStart_4361299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361310 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4361310 : Nat := 118140960795 + 4361310 * 2 ^ 59
def prefixEnd_4361310 : Nat := 4983230072969 + 3 ^ 40 * 4361310 * 2
def baseEnd_4361310 : Nat := 2239448313260436588267707

theorem tailTrace_4361310 : CollatzResearch.WordTrace tailWord_4361310 prefixEnd_4361310 2239448313260436588267707 := by
  unfold tailWord_4361310
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883755478715774661547173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106046695886484131528251589 19883755478715774661547173)
  ·
    refine ⟨3728204152259207749040095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19883755478715774661547173 3728204152259207749040095)
    ·
      refine ⟨5592306228388811623560143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728204152259207749040095 5592306228388811623560143)
      ·
        refine ⟨8388459342583217435340215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592306228388811623560143 8388459342583217435340215)
        ·
          refine ⟨12582689013874826153010323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388459342583217435340215 12582689013874826153010323)
          ·
            refine ⟨18874033520812239229515485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582689013874826153010323 18874033520812239229515485)
            ·
              refine ⟨7077762570304589711068307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18874033520812239229515485 7077762570304589711068307)
              ·
                refine ⟨10616643855456884566602461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077762570304589711068307 10616643855456884566602461)
                ·
                  refine ⟨3981241445796331712475923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10616643855456884566602461 3981241445796331712475923)
                  ·
                    refine ⟨5971862168694497568713885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981241445796331712475923 5971862168694497568713885)
                    ·
                      refine ⟨2239448313260436588267707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971862168694497568713885 2239448313260436588267707)
                      ·
                        rfl

theorem cell23_4361310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4361310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361310 prefixEnd_4361310 := by exact prefixLift 4361310
  have htrace : WordTrace (prefixWord ++ tailWord_4361310) baseStart_4361310 baseEnd_4361310 := by
    simpa [prefixWord, tailWord_4361310, baseEnd_4361310] using wordTrace_append hprefix tailTrace_4361310
  have hstable : (prefixWord ++ tailWord_4361310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361310).length < 2 ^ (prefixWord ++ tailWord_4361310).sum := by decide
  have hdescent : baseEnd_4361310 < baseStart_4361310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361322 : List Nat := [3, 1, 3, 2, 2, 1, 1, 10]
def baseStart_4361322 : Nat := 118140960795 + 4361322 * 2 ^ 59
def prefixEnd_4361322 : Nat := 4983230072969 + 3 ^ 40 * 4361322 * 2
def baseEnd_4361322 : Nat := 82942758334381131159913

theorem tailTrace_4361322 : CollatzResearch.WordTrace tailWord_4361322 prefixEnd_4361322 82942758334381131159913 := by
  unfold tailWord_4361322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39767620376420680835453555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106046987670455148894542813 39767620376420680835453555)
  ·
    refine ⟨59651430564631021253180333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39767620376420680835453555 59651430564631021253180333)
    ·
      refine ⟨22369286461736632969942625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59651430564631021253180333 22369286461736632969942625)
      ·
        refine ⟨16776964846302474727456969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22369286461736632969942625 16776964846302474727456969)
        ·
          refine ⟨12582723634726856045592727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16776964846302474727456969 12582723634726856045592727)
          ·
            refine ⟨18874085452090284068389091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582723634726856045592727 18874085452090284068389091)
            ·
              refine ⟨28311128178135426102583637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18874085452090284068389091 28311128178135426102583637)
              ·
                refine ⟨82942758334381131159913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28311128178135426102583637 82942758334381131159913)
                ·
                  rfl

theorem cell23_4361322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_4361322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361322 prefixEnd_4361322 := by exact prefixLift 4361322
  have htrace : WordTrace (prefixWord ++ tailWord_4361322) baseStart_4361322 baseEnd_4361322 := by
    simpa [prefixWord, tailWord_4361322, baseEnd_4361322] using wordTrace_append hprefix tailTrace_4361322
  have hstable : (prefixWord ++ tailWord_4361322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361322).length < 2 ^ (prefixWord ++ tailWord_4361322).sum := by decide
  have hdescent : baseEnd_4361322 < baseStart_4361322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361326 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_4361326 : Nat := 118140960795 + 4361326 * 2 ^ 59
def prefixEnd_4361326 : Nat := 4983230072969 + 3 ^ 40 * 4361326 * 2
def baseEnd_4361326 : Nat := 746485509650302841889211

theorem tailTrace_4361326 : CollatzResearch.WordTrace tailWord_4361326 prefixEnd_4361326 746485509650302841889211 := by
  unfold tailWord_4361326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883828424708529003119979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106047084931778821349973221 19883828424708529003119979)
  ·
    refine ⟨29825742637062793504679969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883828424708529003119979 29825742637062793504679969)
    ·
      refine ⟨22369306977797095128509977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29825742637062793504679969 22369306977797095128509977)
      ·
        refine ⟨16776980233347821346382483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22369306977797095128509977 16776980233347821346382483)
        ·
          refine ⟨25165470350021732019573725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16776980233347821346382483 25165470350021732019573725)
          ·
            refine ⟨9437051381258149507340147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25165470350021732019573725 9437051381258149507340147)
            ·
              refine ⟨14155577071887224261010221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9437051381258149507340147 14155577071887224261010221)
              ·
                refine ⟨5308341401957709097878833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14155577071887224261010221 5308341401957709097878833)
                ·
                  refine ⟨3981256051468281823409125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5308341401957709097878833 3981256051468281823409125)
                  ·
                    refine ⟨746485509650302841889211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3981256051468281823409125 746485509650302841889211)
                    ·
                      rfl

theorem cell23_4361326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_4361326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361326 prefixEnd_4361326 := by exact prefixLift 4361326
  have htrace : WordTrace (prefixWord ++ tailWord_4361326) baseStart_4361326 baseEnd_4361326 := by
    simpa [prefixWord, tailWord_4361326, baseEnd_4361326] using wordTrace_append hprefix tailTrace_4361326
  have hstable : (prefixWord ++ tailWord_4361326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361326).length < 2 ^ (prefixWord ++ tailWord_4361326).sum := by decide
  have hdescent : baseEnd_4361326 < baseStart_4361326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361367 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_4361367 : Nat := 118140960795 + 4361367 * 2 ^ 59
def prefixEnd_4361367 : Nat := 4983230072969 + 3 ^ 40 * 4361367 * 2
def baseEnd_4361367 : Nat := 2239477581657742865254945

theorem tailTrace_4361367 : CollatzResearch.WordTrace tailWord_4361367 prefixEnd_4361367 2239477581657742865254945 := by
  unfold tailWord_4361367
  simp only [CollatzResearch.WordTrace]
  refine ⟨159072122790519696027202355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106048081860346464018134903 159072122790519696027202355)
  ·
    refine ⟨238608184185779544040803533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159072122790519696027202355 238608184185779544040803533)
    ·
      refine ⟨89478069069667329015301325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238608184185779544040803533 89478069069667329015301325)
      ·
        refine ⟨33554275901125248380737997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89478069069667329015301325 33554275901125248380737997)
        ·
          refine ⟨12582853462921968142776749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33554275901125248380737997 12582853462921968142776749)
          ·
            refine ⟨4718570048595738053541281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12582853462921968142776749 4718570048595738053541281)
            ·
              refine ⟨3538927536446803540155961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718570048595738053541281 3538927536446803540155961)
              ·
                refine ⟨2654195652335102655116971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538927536446803540155961 2654195652335102655116971)
                ·
                  refine ⟨3981293478502653982675457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654195652335102655116971 3981293478502653982675457)
                  ·
                    refine ⟨2985970108876990487006593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981293478502653982675457 2985970108876990487006593)
                    ·
                      refine ⟨2239477581657742865254945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2985970108876990487006593 2239477581657742865254945)
                      ·
                        rfl

theorem cell23_4361367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_4361367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361367 prefixEnd_4361367 := by exact prefixLift 4361367
  have htrace : WordTrace (prefixWord ++ tailWord_4361367) baseStart_4361367 baseEnd_4361367 := by
    simpa [prefixWord, tailWord_4361367, baseEnd_4361367] using wordTrace_append hprefix tailTrace_4361367
  have hstable : (prefixWord ++ tailWord_4361367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361367).length < 2 ^ (prefixWord ++ tailWord_4361367).sum := by decide
  have hdescent : baseEnd_4361367 < baseStart_4361367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361383 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4361383 : Nat := 118140960795 + 4361383 * 2 ^ 59
def prefixEnd_4361383 : Nat := 4983230072969 + 3 ^ 40 * 4361383 * 2
def baseEnd_4361383 : Nat := 2239485797348214802654871

theorem tailTrace_4361383 : CollatzResearch.WordTrace tailWord_4361383 prefixEnd_4361383 2239485797348214802654871 := by
  unfold tailWord_4361383
  simp only [CollatzResearch.WordTrace]
  refine ⟨159072706358461730759784803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106048470905641153839856535 159072706358461730759784803)
  ·
    refine ⟨238609059537692596139677205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159072706358461730759784803 238609059537692596139677205)
    ·
      refine ⟨11184799665829340444047369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 238609059537692596139677205 11184799665829340444047369)
      ·
        refine ⟨8388599749372005333035527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11184799665829340444047369 8388599749372005333035527)
        ·
          refine ⟨12582899624058007999553291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388599749372005333035527 12582899624058007999553291)
          ·
            refine ⟨18874349436087011999329937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12582899624058007999553291 18874349436087011999329937)
            ·
              refine ⟨14155762077065258999497453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18874349436087011999329937 14155762077065258999497453)
              ·
                refine ⟨5308410778899472124811545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14155762077065258999497453 5308410778899472124811545)
                ·
                  refine ⟨3981308084174604093608659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5308410778899472124811545 3981308084174604093608659)
                  ·
                    refine ⟨5971962126261906140412989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981308084174604093608659 5971962126261906140412989)
                    ·
                      refine ⟨2239485797348214802654871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5971962126261906140412989 2239485797348214802654871)
                      ·
                        rfl

theorem cell23_4361383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4361383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361383 prefixEnd_4361383 := by exact prefixLift 4361383
  have htrace : WordTrace (prefixWord ++ tailWord_4361383) baseStart_4361383 baseEnd_4361383 := by
    simpa [prefixWord, tailWord_4361383, baseEnd_4361383] using wordTrace_append hprefix tailTrace_4361383
  have hstable : (prefixWord ++ tailWord_4361383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361383).length < 2 ^ (prefixWord ++ tailWord_4361383).sum := by decide
  have hdescent : baseEnd_4361383 < baseStart_4361383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361402 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_4361402 : Nat := 118140960795 + 4361402 * 2 ^ 59
def prefixEnd_4361402 : Nat := 4983230072969 + 3 ^ 40 * 4361402 * 2
def baseEnd_4361402 : Nat := 2239495553480650228317283

theorem tailTrace_4361402 : CollatzResearch.WordTrace tailWord_4361402 prefixEnd_4361402 2239495553480650228317283 := by
  unfold tailWord_4361402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39768349836348224251181615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106048932896928598003150973 39768349836348224251181615)
  ·
    refine ⟨59652524754522336376772423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39768349836348224251181615 59652524754522336376772423)
    ·
      refine ⟨89478787131783504565158635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59652524754522336376772423 89478787131783504565158635)
      ·
        refine ⟨134218180697675256847737953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89478787131783504565158635 134218180697675256847737953)
        ·
          refine ⟨100663635523256442635803465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134218180697675256847737953 100663635523256442635803465)
          ·
            refine ⟨75497726642442331976852599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100663635523256442635803465 75497726642442331976852599)
            ·
              refine ⟨113246589963663497965278899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75497726642442331976852599 113246589963663497965278899)
              ·
                refine ⟨169869884945495246947918349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113246589963663497965278899 169869884945495246947918349)
                ·
                  refine ⟨63701206854560717605469381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169869884945495246947918349 63701206854560717605469381)
                  ·
                    refine ⟨11943976285230134551025509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63701206854560717605469381 11943976285230134551025509)
                    ·
                      refine ⟨2239495553480650228317283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11943976285230134551025509 2239495553480650228317283)
                      ·
                        rfl

theorem cell23_4361402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_4361402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361402 prefixEnd_4361402 := by exact prefixLift 4361402
  have htrace : WordTrace (prefixWord ++ tailWord_4361402) baseStart_4361402 baseEnd_4361402 := by
    simpa [prefixWord, tailWord_4361402, baseEnd_4361402] using wordTrace_append hprefix tailTrace_4361402
  have hstable : (prefixWord ++ tailWord_4361402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361402).length < 2 ^ (prefixWord ++ tailWord_4361402).sum := by decide
  have hdescent : baseEnd_4361402 < baseStart_4361402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361429 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 7]
def baseStart_4361429 : Nat := 118140960795 + 4361429 * 2 ^ 59
def prefixEnd_4361429 : Nat := 4983230072969 + 3 ^ 40 * 4361429 * 2
def baseEnd_4361429 : Nat := 248834379717591291408851

theorem tailTrace_4361429 : CollatzResearch.WordTrace tailWord_4361429 prefixEnd_4361429 248834379717591291408851 := by
  unfold tailWord_4361429
  simp only [CollatzResearch.WordTrace]
  refine ⟨159074384116295080615959341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106049589410863387077306227 159074384116295080615959341)
  ·
    refine ⟨59652894043610655230984753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159074384116295080615959341 59652894043610655230984753)
    ·
      refine ⟨44739670532707991423238565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59652894043610655230984753 44739670532707991423238565)
      ·
        refine ⟨8388688224882748391857231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44739670532707991423238565 8388688224882748391857231)
        ·
          refine ⟨12583032337324122587785847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8388688224882748391857231 12583032337324122587785847)
          ·
            refine ⟨18874548505986183881678771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583032337324122587785847 18874548505986183881678771)
            ·
              refine ⟨28311822758979275822518157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18874548505986183881678771 28311822758979275822518157)
              ·
                refine ⟨10616933534617228433444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28311822758979275822518157 10616933534617228433444309)
                ·
                  refine ⟨248834379717591291408851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10616933534617228433444309 248834379717591291408851)
                  ·
                    rfl

theorem cell23_4361429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_4361429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361429 prefixEnd_4361429 := by exact prefixLift 4361429
  have htrace : WordTrace (prefixWord ++ tailWord_4361429) baseStart_4361429 baseEnd_4361429 := by
    simpa [prefixWord, tailWord_4361429, baseEnd_4361429] using wordTrace_append hprefix tailTrace_4361429
  have hstable : (prefixWord ++ tailWord_4361429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361429).length < 2 ^ (prefixWord ++ tailWord_4361429).sum := by decide
  have hdescent : baseEnd_4361429 < baseStart_4361429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361439 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_4361439 : Nat := 118140960795 + 4361439 * 2 ^ 59
def prefixEnd_4361439 : Nat := 4983230072969 + 3 ^ 40 * 4361439 * 2
def baseEnd_4361439 : Nat := 2239514552264866583554613

theorem tailTrace_4361439 : CollatzResearch.WordTrace tailWord_4361439 prefixEnd_4361439 2239514552264866583554613 := by
  unfold tailWord_4361439
  simp only [CollatzResearch.WordTrace]
  refine ⟨159074748846258852323823371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106049832564172568215882247 159074748846258852323823371)
  ·
    refine ⟨238612123269388278485735057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159074748846258852323823371 238612123269388278485735057)
    ·
      refine ⟨178959092452041208864301293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238612123269388278485735057 178959092452041208864301293)
      ·
        refine ⟨67109659669515453324112985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178959092452041208864301293 67109659669515453324112985)
        ·
          refine ⟨50332244752136589993084739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67109659669515453324112985 50332244752136589993084739)
          ·
            refine ⟨75498367128204884989627109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50332244752136589993084739 75498367128204884989627109)
            ·
              refine ⟨14155943836538415935555083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75498367128204884989627109 14155943836538415935555083)
              ·
                refine ⟨21233915754807623903332625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14155943836538415935555083 21233915754807623903332625)
                ·
                  refine ⟨15925436816105717927499469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21233915754807623903332625 15925436816105717927499469)
                  ·
                    refine ⟨5972038806039644222812301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15925436816105717927499469 5972038806039644222812301)
                    ·
                      refine ⟨2239514552264866583554613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972038806039644222812301 2239514552264866583554613)
                      ·
                        rfl

theorem cell23_4361439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_4361439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361439 prefixEnd_4361439 := by exact prefixLift 4361439
  have htrace : WordTrace (prefixWord ++ tailWord_4361439) baseStart_4361439 baseEnd_4361439 := by
    simpa [prefixWord, tailWord_4361439, baseEnd_4361439] using wordTrace_append hprefix tailTrace_4361439
  have hstable : (prefixWord ++ tailWord_4361439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361439).length < 2 ^ (prefixWord ++ tailWord_4361439).sum := by decide
  have hdescent : baseEnd_4361439 < baseStart_4361439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361440 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2]
def baseStart_4361440 : Nat := 118140960795 + 4361440 * 2 ^ 59
def prefixEnd_4361440 : Nat := 4983230072969 + 3 ^ 40 * 4361440 * 2
def baseEnd_4361440 : Nat := 2239515065745521079642109

theorem tailTrace_4361440 : CollatzResearch.WordTrace tailWord_4361440 prefixEnd_4361440 2239515065745521079642109 := by
  unfold tailWord_4361440
  simp only [CollatzResearch.WordTrace]
  refine ⟨79537392659627614747304887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106049856879503486329739849 79537392659627614747304887)
  ·
    refine ⟨119306088989441422120957331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79537392659627614747304887 119306088989441422120957331)
    ·
      refine ⟨178959133484162133181435997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119306088989441422120957331 178959133484162133181435997)
      ·
        refine ⟨67109675056560799943038499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178959133484162133181435997 67109675056560799943038499)
        ·
          refine ⟨100664512584841199914557749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67109675056560799943038499 100664512584841199914557749)
          ·
            refine ⟨9437298054828862491989789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100664512584841199914557749 9437298054828862491989789)
            ·
              refine ⟨3538986770560823434496171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9437298054828862491989789 3538986770560823434496171)
              ·
                refine ⟨5308480155841235151744257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3538986770560823434496171 5308480155841235151744257)
                ·
                  refine ⟨3981360116880926363808193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5308480155841235151744257 3981360116880926363808193)
                  ·
                    refine ⟨2986020087660694772856145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981360116880926363808193 2986020087660694772856145)
                    ·
                      refine ⟨2239515065745521079642109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986020087660694772856145 2239515065745521079642109)
                      ·
                        rfl

theorem cell23_4361440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_4361440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361440 prefixEnd_4361440 := by exact prefixLift 4361440
  have htrace : WordTrace (prefixWord ++ tailWord_4361440) baseStart_4361440 baseEnd_4361440 := by
    simpa [prefixWord, tailWord_4361440, baseEnd_4361440] using wordTrace_append hprefix tailTrace_4361440
  have hstable : (prefixWord ++ tailWord_4361440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361440).length < 2 ^ (prefixWord ++ tailWord_4361440).sum := by decide
  have hdescent : baseEnd_4361440 < baseStart_4361440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361460 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4361460 : Nat := 118140960795 + 4361460 * 2 ^ 59
def prefixEnd_4361460 : Nat := 4983230072969 + 3 ^ 40 * 4361460 * 2
def baseEnd_4361460 : Nat := 2239525335358611001392017

theorem tailTrace_4361460 : CollatzResearch.WordTrace tailWord_4361460 prefixEnd_4361460 2239525335358611001392017 := by
  unfold tailWord_4361460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79537757389591386455168917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106050343186121848606891889 79537757389591386455168917)
  ·
    refine ⟨3728332377637096240086043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79537757389591386455168917 3728332377637096240086043)
    ·
      refine ⟨5592498566455644360129065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728332377637096240086043 5592498566455644360129065)
      ·
        refine ⟨4194373924841733270096799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592498566455644360129065 4194373924841733270096799)
        ·
          refine ⟨6291560887262599905145199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194373924841733270096799 6291560887262599905145199)
          ·
            refine ⟨9437341330893899857717799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291560887262599905145199 9437341330893899857717799)
            ·
              refine ⟨14156011996340849786576699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9437341330893899857717799 14156011996340849786576699)
              ·
                refine ⟨21234017994511274679865049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14156011996340849786576699 21234017994511274679865049)
                ·
                  refine ⟨15925513495883456009898787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21234017994511274679865049 15925513495883456009898787)
                  ·
                    refine ⟨23888270243825184014848181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15925513495883456009898787 23888270243825184014848181)
                    ·
                      refine ⟨2239525335358611001392017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23888270243825184014848181 2239525335358611001392017)
                      ·
                        rfl

theorem cell23_4361460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4361460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361460 prefixEnd_4361460 := by exact prefixLift 4361460
  have htrace : WordTrace (prefixWord ++ tailWord_4361460) baseStart_4361460 baseEnd_4361460 := by
    simpa [prefixWord, tailWord_4361460, baseEnd_4361460] using wordTrace_append hprefix tailTrace_4361460
  have hstable : (prefixWord ++ tailWord_4361460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361460).length < 2 ^ (prefixWord ++ tailWord_4361460).sum := by decide
  have hdescent : baseEnd_4361460 < baseStart_4361460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361476 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_4361476 : Nat := 118140960795 + 4361476 * 2 ^ 59
def prefixEnd_4361476 : Nat := 4983230072969 + 3 ^ 40 * 4361476 * 2
def baseEnd_4361476 : Nat := 746511183683027646263981

theorem tailTrace_4361476 : CollatzResearch.WordTrace tailWord_4361476 prefixEnd_4361476 746511183683027646263981 := by
  unfold tailWord_4361476
  simp only [CollatzResearch.WordTrace]
  refine ⟨79538049173562403821460141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106050732231416538428613521 79538049173562403821460141)
  ·
    refine ⟨29826768440085901433047553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79538049173562403821460141 29826768440085901433047553)
    ·
      refine ⟨22370076330064426074785665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29826768440085901433047553 22370076330064426074785665)
      ·
        refine ⟨16777557247548319556089249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22370076330064426074785665 16777557247548319556089249)
        ·
          refine ⟨12583167935661239667066937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16777557247548319556089249 12583167935661239667066937)
          ·
            refine ⟨9437375951745929750300203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12583167935661239667066937 9437375951745929750300203)
            ·
              refine ⟨14156063927618894625450305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9437375951745929750300203 14156063927618894625450305)
              ·
                refine ⟨10617047945714170969087729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14156063927618894625450305 10617047945714170969087729)
                ·
                  refine ⟨7962785959285628226815797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10617047945714170969087729 7962785959285628226815797)
                  ·
                    refine ⟨746511183683027646263981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7962785959285628226815797 746511183683027646263981)
                    ·
                      rfl

theorem cell23_4361476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_4361476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361476 prefixEnd_4361476 := by exact prefixLift 4361476
  have htrace : WordTrace (prefixWord ++ tailWord_4361476) baseStart_4361476 baseEnd_4361476 := by
    simpa [prefixWord, tailWord_4361476, baseEnd_4361476] using wordTrace_append hprefix tailTrace_4361476
  have hstable : (prefixWord ++ tailWord_4361476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361476).length < 2 ^ (prefixWord ++ tailWord_4361476).sum := by decide
  have hdescent : baseEnd_4361476 < baseStart_4361476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361499 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3]
def baseStart_4361499 : Nat := 118140960795 + 4361499 * 2 ^ 59
def prefixEnd_4361499 : Nat := 4983230072969 + 3 ^ 40 * 4361499 * 2
def baseEnd_4361499 : Nat := 2239545361104136348804337

theorem tailTrace_4361499 : CollatzResearch.WordTrace tailWord_4361499 prefixEnd_4361499 2239545361104136348804337 := by
  unfold tailWord_4361499
  simp only [CollatzResearch.WordTrace]
  refine ⟨159076937226041482571007551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106051291484027655047338367 159076937226041482571007551)
  ·
    refine ⟨238615405839062223856511327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159076937226041482571007551 238615405839062223856511327)
    ·
      refine ⟨357923108758593335784766991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238615405839062223856511327 357923108758593335784766991)
      ·
        refine ⟨536884663137890003677150487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357923108758593335784766991 536884663137890003677150487)
        ·
          refine ⟨805326994706835005515725731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536884663137890003677150487 805326994706835005515725731)
          ·
            refine ⟨1207990492060252508273588597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805326994706835005515725731 1207990492060252508273588597)
            ·
              refine ⟨113249108630648672650648931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1207990492060252508273588597 113249108630648672650648931)
              ·
                refine ⟨169873662945973008975973397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113249108630648672650648931 169873662945973008975973397)
                ·
                  refine ⟨7962827950592484795748753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169873662945973008975973397 7962827950592484795748753)
                  ·
                    refine ⟨5972120962944363596811565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7962827950592484795748753 5972120962944363596811565)
                    ·
                      refine ⟨2239545361104136348804337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972120962944363596811565 2239545361104136348804337)
                      ·
                        rfl

theorem cell23_4361499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].length) (baseStart_4361499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361499 prefixEnd_4361499 := by exact prefixLift 4361499
  have htrace : WordTrace (prefixWord ++ tailWord_4361499) baseStart_4361499 baseEnd_4361499 := by
    simpa [prefixWord, tailWord_4361499, baseEnd_4361499] using wordTrace_append hprefix tailTrace_4361499
  have hstable : (prefixWord ++ tailWord_4361499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361499).length < 2 ^ (prefixWord ++ tailWord_4361499).sum := by decide
  have hdescent : baseEnd_4361499 < baseStart_4361499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361546 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_4361546 : Nat := 118140960795 + 4361546 * 2 ^ 59
def prefixEnd_4361546 : Nat := 4983230072969 + 3 ^ 40 * 4361546 * 2
def baseEnd_4361546 : Nat := 2239569494694897664916621

theorem tailTrace_4361546 : CollatzResearch.WordTrace tailWord_4361546 prefixEnd_4361546 2239569494694897664916621 := by
  unfold tailWord_4361546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39769662864217802399492123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106052434304580806398645661 39769662864217802399492123)
  ·
    refine ⟨59654494296326703599238185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39769662864217802399492123 59654494296326703599238185)
    ·
      refine ⟨44740870722245027699428639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59654494296326703599238185 44740870722245027699428639)
      ·
        refine ⟨67111306083367541549142959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44740870722245027699428639 67111306083367541549142959)
        ·
          refine ⟨100666959125051312323714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67111306083367541549142959 100666959125051312323714439)
          ·
            refine ⟨151000438687576968485571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100666959125051312323714439 151000438687576968485571659)
            ·
              refine ⟨226500658031365452728357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151000438687576968485571659 226500658031365452728357489)
              ·
                refine ⟨169875493523524089546268117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226500658031365452728357489 169875493523524089546268117)
                ·
                  refine ⟨3981456879457595848740659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169875493523524089546268117 3981456879457595848740659)
                  ·
                    refine ⟨5972185319186393773110989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981456879457595848740659 5972185319186393773110989)
                    ·
                      refine ⟨2239569494694897664916621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972185319186393773110989 2239569494694897664916621)
                      ·
                        rfl

theorem cell23_4361546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_4361546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361546 prefixEnd_4361546 := by exact prefixLift 4361546
  have htrace : WordTrace (prefixWord ++ tailWord_4361546) baseStart_4361546 baseEnd_4361546 := by
    simpa [prefixWord, tailWord_4361546, baseEnd_4361546] using wordTrace_append hprefix tailTrace_4361546
  have hstable : (prefixWord ++ tailWord_4361546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361546).length < 2 ^ (prefixWord ++ tailWord_4361546).sum := by decide
  have hdescent : baseEnd_4361546 < baseStart_4361546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361580 : List Nat := [2, 2, 1, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_4361580 : Nat := 118140960795 + 4361580 * 2 ^ 59
def prefixEnd_4361580 : Nat := 4983230072969 + 3 ^ 40 * 4361580 * 2
def baseEnd_4361580 : Nat := 2239586953037150531891465

theorem tailTrace_4361580 : CollatzResearch.WordTrace tailWord_4361580 prefixEnd_4361580 2239586953037150531891465 := by
  unfold tailWord_4361580
  simp only [CollatzResearch.WordTrace]
  refine ⟨79539945769374016702353097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106053261025832022269804129 79539945769374016702353097)
  ·
    refine ⟨59654959327030512526764823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79539945769374016702353097 59654959327030512526764823)
    ·
      refine ⟨89482438990545768790147235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59654959327030512526764823 89482438990545768790147235)
      ·
        refine ⟨134223658485818653185220853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89482438990545768790147235 134223658485818653185220853)
        ·
          refine ⟨12583467983045498736114455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134223658485818653185220853 12583467983045498736114455)
          ·
            refine ⟨18875201974568248104171683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12583467983045498736114455 18875201974568248104171683)
            ·
              refine ⟨28312802961852372156257525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18875201974568248104171683 28312802961852372156257525)
              ·
                refine ⟨2654325277673659889649143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28312802961852372156257525 2654325277673659889649143)
                ·
                  refine ⟨3981487916510489834473715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654325277673659889649143 3981487916510489834473715)
                  ·
                    refine ⟨5972231874765734751710573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981487916510489834473715 5972231874765734751710573)
                    ·
                      refine ⟨2239586953037150531891465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972231874765734751710573 2239586953037150531891465)
                      ·
                        rfl

theorem cell23_4361580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_4361580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361580 prefixEnd_4361580 := by exact prefixLift 4361580
  have htrace : WordTrace (prefixWord ++ tailWord_4361580) baseStart_4361580 baseEnd_4361580 := by
    simpa [prefixWord, tailWord_4361580, baseEnd_4361580] using wordTrace_append hprefix tailTrace_4361580
  have hstable : (prefixWord ++ tailWord_4361580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361580).length < 2 ^ (prefixWord ++ tailWord_4361580).sum := by decide
  have hdescent : baseEnd_4361580 < baseStart_4361580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361596 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_4361596 : Nat := 118140960795 + 4361596 * 2 ^ 59
def prefixEnd_4361596 : Nat := 4983230072969 + 3 ^ 40 * 4361596 * 2
def baseEnd_4361596 : Nat := 746531722909207489763797

theorem tailTrace_4361596 : CollatzResearch.WordTrace tailWord_4361596 prefixEnd_4361596 746531722909207489763797 := by
  unfold tailWord_4361596
  simp only [CollatzResearch.WordTrace]
  refine ⟨79540237553345034068644321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106053650071126712091525761 79540237553345034068644321)
  ·
    refine ⟨59655178165008775551483241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79540237553345034068644321 59655178165008775551483241)
    ·
      refine ⟨44741383623756581663612431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59655178165008775551483241 44741383623756581663612431)
      ·
        refine ⟨67112075435634872495418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44741383623756581663612431 67112075435634872495418647)
        ·
          refine ⟨100668113153452308743127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67112075435634872495418647 100668113153452308743127971)
          ·
            refine ⟨151002169730178463114691957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100668113153452308743127971 151002169730178463114691957)
            ·
              refine ⟨14156453412204230917002371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151002169730178463114691957 14156453412204230917002371)
              ·
                refine ⟨21234680118306346375503557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14156453412204230917002371 21234680118306346375503557)
                ·
                  refine ⟨3981502522182439945406917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21234680118306346375503557 3981502522182439945406917)
                  ·
                    refine ⟨746531722909207489763797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3981502522182439945406917 746531722909207489763797)
                    ·
                      rfl

theorem cell23_4361596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_4361596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361596 prefixEnd_4361596 := by exact prefixLift 4361596
  have htrace : WordTrace (prefixWord ++ tailWord_4361596) baseStart_4361596 baseEnd_4361596 := by
    simpa [prefixWord, tailWord_4361596, baseEnd_4361596] using wordTrace_append hprefix tailTrace_4361596
  have hstable : (prefixWord ++ tailWord_4361596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361596).length < 2 ^ (prefixWord ++ tailWord_4361596).sum := by decide
  have hdescent : baseEnd_4361596 < baseStart_4361596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361620 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4361620 : Nat := 118140960795 + 4361620 * 2 ^ 59
def prefixEnd_4361620 : Nat := 4983230072969 + 3 ^ 40 * 4361620 * 2
def baseEnd_4361620 : Nat := 2239607492263330375391281

theorem tailTrace_4361620 : CollatzResearch.WordTrace tailWord_4361620 prefixEnd_4361620 2239607492263330375391281 := by
  unfold tailWord_4361620
  simp only [CollatzResearch.WordTrace]
  refine ⟨79540675229301560118081157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106054233639068746824108209 79540675229301560118081157)
  ·
    refine ⟨14913876605494042522140217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79540675229301560118081157 14913876605494042522140217)
    ·
      refine ⟨11185407454120531891605163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14913876605494042522140217 11185407454120531891605163)
      ·
        refine ⟨16778111181180797837407745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11185407454120531891605163 16778111181180797837407745)
        ·
          refine ⟨12583583385885598378055809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16778111181180797837407745 12583583385885598378055809)
          ·
            refine ⟨9437687539414198783541857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12583583385885598378055809 9437687539414198783541857)
            ·
              refine ⟨7078265654560649087656393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9437687539414198783541857 7078265654560649087656393)
              ·
                refine ⟨5308699240920486815742295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7078265654560649087656393 5308699240920486815742295)
                ·
                  refine ⟨7963048861380730223613443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308699240920486815742295 7963048861380730223613443)
                  ·
                    refine ⟨11944573292071095335420165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7963048861380730223613443 11944573292071095335420165)
                    ·
                      refine ⟨2239607492263330375391281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11944573292071095335420165 2239607492263330375391281)
                      ·
                        rfl

theorem cell23_4361620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4361620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361620 prefixEnd_4361620 := by exact prefixLift 4361620
  have htrace : WordTrace (prefixWord ++ tailWord_4361620) baseStart_4361620 baseEnd_4361620 := by
    simpa [prefixWord, tailWord_4361620, baseEnd_4361620] using wordTrace_append hprefix tailTrace_4361620
  have hstable : (prefixWord ++ tailWord_4361620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361620).length < 2 ^ (prefixWord ++ tailWord_4361620).sum := by decide
  have hdescent : baseEnd_4361620 < baseStart_4361620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361636 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_4361636 : Nat := 118140960795 + 4361636 * 2 ^ 59
def prefixEnd_4361636 : Nat := 4983230072969 + 3 ^ 40 * 4361636 * 2
def baseEnd_4361636 : Nat := 2239615707953802312791207

theorem tailTrace_4361636 : CollatzResearch.WordTrace tailWord_4361636 prefixEnd_4361636 2239615707953802312791207 := by
  unfold tailWord_4361636
  simp only [CollatzResearch.WordTrace]
  refine ⟨79540967013272577484372381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106054622684363436645829841 79540967013272577484372381)
  ·
    refine ⟨29827862629977216556639643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79540967013272577484372381 29827862629977216556639643)
    ·
      refine ⟨44741793944965824834959465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29827862629977216556639643 44741793944965824834959465)
      ·
        refine ⟨33556345458724368626219599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44741793944965824834959465 33556345458724368626219599)
        ·
          refine ⟨50334518188086552939329399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33556345458724368626219599 50334518188086552939329399)
          ·
            refine ⟨75501777282129829408994099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50334518188086552939329399 75501777282129829408994099)
            ·
              refine ⟨113252665923194744113491149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75501777282129829408994099 113252665923194744113491149)
              ·
                refine ⟨42469749721198029042559181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113252665923194744113491149 42469749721198029042559181)
                ·
                  refine ⟨15926156145449260890959693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42469749721198029042559181 15926156145449260890959693)
                  ·
                    refine ⟨5972308554543472834109885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15926156145449260890959693 5972308554543472834109885)
                    ·
                      refine ⟨2239615707953802312791207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972308554543472834109885 2239615707953802312791207)
                      ·
                        rfl

theorem cell23_4361636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_4361636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361636 prefixEnd_4361636 := by exact prefixLift 4361636
  have htrace : WordTrace (prefixWord ++ tailWord_4361636) baseStart_4361636 baseEnd_4361636 := by
    simpa [prefixWord, tailWord_4361636, baseEnd_4361636] using wordTrace_append hprefix tailTrace_4361636
  have hstable : (prefixWord ++ tailWord_4361636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361636).length < 2 ^ (prefixWord ++ tailWord_4361636).sum := by decide
  have hdescent : baseEnd_4361636 < baseStart_4361636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361640 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4361640 : Nat := 118140960795 + 4361640 * 2 ^ 59
def prefixEnd_4361640 : Nat := 4983230072969 + 3 ^ 40 * 4361640 * 2
def baseEnd_4361640 : Nat := 2239617761876420297141189

theorem tailTrace_4361640 : CollatzResearch.WordTrace tailWord_4361640 prefixEnd_4361640 2239617761876420297141189 := by
  unfold tailWord_4361640
  simp only [CollatzResearch.WordTrace]
  refine ⟨79541039959265331825945187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106054719945687109101260249 79541039959265331825945187)
  ·
    refine ⟨119311559938897997738917781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79541039959265331825945187 119311559938897997738917781)
    ·
      refine ⟨5592729372135843644011771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119311559938897997738917781 5592729372135843644011771)
      ·
        refine ⟨8389094058203765466017657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592729372135843644011771 8389094058203765466017657)
        ·
          refine ⟨6291820543652824099513243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8389094058203765466017657 6291820543652824099513243)
          ·
            refine ⟨9437730815479236149269865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6291820543652824099513243 9437730815479236149269865)
            ·
              refine ⟨7078298111609427111952399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9437730815479236149269865 7078298111609427111952399)
              ·
                refine ⟨10617447167414140667928599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7078298111609427111952399 10617447167414140667928599)
                ·
                  refine ⟨15926170751121211001892899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10617447167414140667928599 15926170751121211001892899)
                  ·
                    refine ⟨23889256126681816502839349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15926170751121211001892899 23889256126681816502839349)
                    ·
                      refine ⟨2239617761876420297141189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23889256126681816502839349 2239617761876420297141189)
                      ·
                        rfl

theorem cell23_4361640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4361640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361640 prefixEnd_4361640 := by exact prefixLift 4361640
  have htrace : WordTrace (prefixWord ++ tailWord_4361640) baseStart_4361640 baseEnd_4361640 := by
    simpa [prefixWord, tailWord_4361640, baseEnd_4361640] using wordTrace_append hprefix tailTrace_4361640
  have hstable : (prefixWord ++ tailWord_4361640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361640).length < 2 ^ (prefixWord ++ tailWord_4361640).sum := by decide
  have hdescent : baseEnd_4361640 < baseStart_4361640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361697 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_4361697 : Nat := 118140960795 + 4361697 * 2 ^ 59
def prefixEnd_4361697 : Nat := 4983230072969 + 3 ^ 40 * 4361697 * 2
def baseEnd_4361697 : Nat := 2239647030273726574128427

theorem tailTrace_4361697 : CollatzResearch.WordTrace tailWord_4361697 prefixEnd_4361697 2239647030273726574128427 := by
  unfold tailWord_4361697
  simp only [CollatzResearch.WordTrace]
  refine ⟨159084158879324162386715345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106056105919549441591143563 159084158879324162386715345)
  ·
    refine ⟨119313119159493121790036509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159084158879324162386715345 119313119159493121790036509)
    ·
      refine ⟨44742419684809920671263691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119313119159493121790036509 44742419684809920671263691)
      ·
        refine ⟨67113629527214881006895537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44742419684809920671263691 67113629527214881006895537)
        ·
          refine ⟨50335222145411160755171653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67113629527214881006895537 50335222145411160755171653)
          ·
            refine ⟨9437854152264592641594685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50335222145411160755171653 9437854152264592641594685)
            ·
              refine ⟨3539195307099222240598007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9437854152264592641594685 3539195307099222240598007)
              ·
                refine ⟨5308792960648833360897011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539195307099222240598007 5308792960648833360897011)
                ·
                  refine ⟨7963189440973250041345517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308792960648833360897011 7963189440973250041345517)
                  ·
                    refine ⟨2986196040364968765504569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7963189440973250041345517 2986196040364968765504569)
                    ·
                      refine ⟨2239647030273726574128427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986196040364968765504569 2239647030273726574128427)
                      ·
                        rfl

theorem cell23_4361697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_4361697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361697 prefixEnd_4361697 := by exact prefixLift 4361697
  have htrace : WordTrace (prefixWord ++ tailWord_4361697) baseStart_4361697 baseEnd_4361697 := by
    simpa [prefixWord, tailWord_4361697, baseEnd_4361697] using wordTrace_append hprefix tailTrace_4361697
  have hstable : (prefixWord ++ tailWord_4361697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361697).length < 2 ^ (prefixWord ++ tailWord_4361697).sum := by decide
  have hdescent : baseEnd_4361697 < baseStart_4361697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361748 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4361748 : Nat := 118140960795 + 4361748 * 2 ^ 59
def prefixEnd_4361748 : Nat := 4983230072969 + 3 ^ 40 * 4361748 * 2
def baseEnd_4361748 : Nat := 2239673217787105874590693

theorem tailTrace_4361748 : CollatzResearch.WordTrace tailWord_4361748 prefixEnd_4361748 2239673217787105874590693 := by
  unfold tailWord_4361748
  simp only [CollatzResearch.WordTrace]
  refine ⟨79543009501069699048410949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106057346001426265397881265 79543009501069699048410949)
  ·
    refine ⟨14914314281450568571577053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79543009501069699048410949 14914314281450568571577053)
    ·
      refine ⟨5592867855543963214341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14914314281450568571577053 5592867855543963214341395)
      ·
        refine ⟨8389301783315944821512093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5592867855543963214341395 8389301783315944821512093)
        ·
          refine ⟨3145988168743479308067035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8389301783315944821512093 3145988168743479308067035)
          ·
            refine ⟨4718982253115218962100553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145988168743479308067035 4718982253115218962100553)
            ·
              refine ⟨3539236689836414221575415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718982253115218962100553 3539236689836414221575415)
              ·
                refine ⟨5308855034754621332363123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539236689836414221575415 5308855034754621332363123)
                ·
                  refine ⟨7963282552131931998544685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308855034754621332363123 7963282552131931998544685)
                  ·
                    refine ⟨2986230957049474499454257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7963282552131931998544685 2986230957049474499454257)
                    ·
                      refine ⟨2239673217787105874590693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986230957049474499454257 2239673217787105874590693)
                      ·
                        rfl

theorem cell23_4361748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4361748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361748 prefixEnd_4361748 := by exact prefixLift 4361748
  have htrace : WordTrace (prefixWord ++ tailWord_4361748) baseStart_4361748 baseEnd_4361748 := by
    simpa [prefixWord, tailWord_4361748, baseEnd_4361748] using wordTrace_append hprefix tailTrace_4361748
  have hstable : (prefixWord ++ tailWord_4361748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361748).length < 2 ^ (prefixWord ++ tailWord_4361748).sum := by decide
  have hdescent : baseEnd_4361748 < baseStart_4361748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361803 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3]
def baseStart_4361803 : Nat := 118140960795 + 4361803 * 2 ^ 59
def prefixEnd_4361803 : Nat := 4983230072969 + 3 ^ 40 * 4361803 * 2
def baseEnd_4361803 : Nat := 2239701459223103159402939

theorem tailTrace_4361803 : CollatzResearch.WordTrace tailWord_4361803 prefixEnd_4361803 2239701459223103159402939 := by
  unfold tailWord_4361803
  simp only [CollatzResearch.WordTrace]
  refine ⟨159088025016940142490074063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106058683344626761660049375 159088025016940142490074063)
  ·
    refine ⟨238632037525410213735111095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159088025016940142490074063 238632037525410213735111095)
    ·
      refine ⟨357948056288115320602666643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238632037525410213735111095 357948056288115320602666643)
      ·
        refine ⟨536922084432172980903999965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357948056288115320602666643 536922084432172980903999965)
        ·
          refine ⟨201345781662064867838999987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536922084432172980903999965 201345781662064867838999987)
          ·
            refine ⟨302018672493097301758499981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201345781662064867838999987 302018672493097301758499981)
            ·
              refine ⟨113257002184911488159437493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302018672493097301758499981 113257002184911488159437493)
              ·
                refine ⟨10617843954835452014947265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113257002184911488159437493 10617843954835452014947265)
                ·
                  refine ⟨7963382966126589011210449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10617843954835452014947265 7963382966126589011210449)
                  ·
                    refine ⟨5972537224594941758407837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7963382966126589011210449 5972537224594941758407837)
                    ·
                      refine ⟨2239701459223103159402939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972537224594941758407837 2239701459223103159402939)
                      ·
                        rfl

theorem cell23_4361803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].length) (baseStart_4361803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361803 prefixEnd_4361803 := by exact prefixLift 4361803
  have htrace : WordTrace (prefixWord ++ tailWord_4361803) baseStart_4361803 baseEnd_4361803 := by
    simpa [prefixWord, tailWord_4361803, baseEnd_4361803] using wordTrace_append hprefix tailTrace_4361803
  have hstable : (prefixWord ++ tailWord_4361803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361803).length < 2 ^ (prefixWord ++ tailWord_4361803).sum := by decide
  have hdescent : baseEnd_4361803 < baseStart_4361803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361814 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4361814 : Nat := 118140960795 + 4361814 * 2 ^ 59
def prefixEnd_4361814 : Nat := 4983230072969 + 3 ^ 40 * 4361814 * 2
def baseEnd_4361814 : Nat := 746569035836767538788463

theorem tailTrace_4361814 : CollatzResearch.WordTrace tailWord_4361814 prefixEnd_4361814 746569035836767538788463 := by
  unfold tailWord_4361814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9943026638743768210545281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106058950813266860912482997 9943026638743768210545281)
  ·
    refine ⟨7457269979057826157908961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9943026638743768210545281 7457269979057826157908961)
    ·
      refine ⟨5592952484293369618431721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7457269979057826157908961 5592952484293369618431721)
      ·
        refine ⟨4194714363220027213823791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592952484293369618431721 4194714363220027213823791)
        ·
          refine ⟨6292071544830040820735687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194714363220027213823791 6292071544830040820735687)
          ·
            refine ⟨9438107317245061231103531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292071544830040820735687 9438107317245061231103531)
            ·
              refine ⟨14157160975867591846655297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9438107317245061231103531 14157160975867591846655297)
              ·
                refine ⟨10617870731900693884991473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14157160975867591846655297 10617870731900693884991473)
                ·
                  refine ⟨7963403048925520413743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10617870731900693884991473 7963403048925520413743605)
                  ·
                    refine ⟨746569035836767538788463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7963403048925520413743605 746569035836767538788463)
                    ·
                      rfl

theorem cell23_4361814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4361814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361814 prefixEnd_4361814 := by exact prefixLift 4361814
  have htrace : WordTrace (prefixWord ++ tailWord_4361814) baseStart_4361814 baseEnd_4361814 := by
    simpa [prefixWord, tailWord_4361814, baseEnd_4361814] using wordTrace_append hprefix tailTrace_4361814
  have hstable : (prefixWord ++ tailWord_4361814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361814).length < 2 ^ (prefixWord ++ tailWord_4361814).sum := by decide
  have hdescent : baseEnd_4361814 < baseStart_4361814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361820 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4361820 : Nat := 118140960795 + 4361820 * 2 ^ 59
def prefixEnd_4361820 : Nat := 4983230072969 + 3 ^ 40 * 4361820 * 2
def baseEnd_4361820 : Nat := 2239710188394229592890361

theorem tailTrace_4361820 : CollatzResearch.WordTrace tailWord_4361820 prefixEnd_4361820 2239710188394229592890361 := by
  unfold tailWord_4361820
  simp only [CollatzResearch.WordTrace]
  refine ⟨79544322528939277196721457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106059096705252369595628609 79544322528939277196721457)
  ·
    refine ⟨59658241896704457897541093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79544322528939277196721457 59658241896704457897541093)
    ·
      refine ⟨11185920355632085855788955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59658241896704457897541093 11185920355632085855788955)
      ·
        refine ⟨16778880533448128783683433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11185920355632085855788955 16778880533448128783683433)
        ·
          refine ⟨12584160400086096587762575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16778880533448128783683433 12584160400086096587762575)
          ·
            refine ⟨18876240600129144881643863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12584160400086096587762575 18876240600129144881643863)
            ·
              refine ⟨28314360900193717322465795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18876240600129144881643863 28314360900193717322465795)
              ·
                refine ⟨42471541350290575983698693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28314360900193717322465795 42471541350290575983698693)
                ·
                  refine ⟨7963414003179482996943505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42471541350290575983698693 7963414003179482996943505)
                  ·
                    refine ⟨5972560502384612247707629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7963414003179482996943505 5972560502384612247707629)
                    ·
                      refine ⟨2239710188394229592890361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972560502384612247707629 2239710188394229592890361)
                      ·
                        rfl

theorem cell23_4361820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4361820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361820 prefixEnd_4361820 := by exact prefixLift 4361820
  have htrace : WordTrace (prefixWord ++ tailWord_4361820) baseStart_4361820 baseEnd_4361820 := by
    simpa [prefixWord, tailWord_4361820, baseEnd_4361820] using wordTrace_append hprefix tailTrace_4361820
  have hstable : (prefixWord ++ tailWord_4361820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361820).length < 2 ^ (prefixWord ++ tailWord_4361820).sum := by decide
  have hdescent : baseEnd_4361820 < baseStart_4361820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361836 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_4361836 : Nat := 118140960795 + 4361836 * 2 ^ 59
def prefixEnd_4361836 : Nat := 4983230072969 + 3 ^ 40 * 4361836 * 2
def baseEnd_4361836 : Nat := 746572801361567176763429

theorem tailTrace_4361836 : CollatzResearch.WordTrace tailWord_4361836 prefixEnd_4361836 746572801361567176763429 := by
  unfold tailWord_4361836
  simp only [CollatzResearch.WordTrace]
  refine ⟨79544614312910294563012681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106059485750547059417350241 79544614312910294563012681)
  ·
    refine ⟨59658460734682720922259511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79544614312910294563012681 59658460734682720922259511)
    ·
      refine ⟨89487691102024081383389267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59658460734682720922259511 89487691102024081383389267)
      ·
        refine ⟨134231536653036122075083901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89487691102024081383389267 134231536653036122075083901)
        ·
          refine ⟨50336826244888545778156463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134231536653036122075083901 50336826244888545778156463)
          ·
            refine ⟨75505239367332818667234695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50336826244888545778156463 75505239367332818667234695)
            ·
              refine ⟨113257859050999228000852043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75505239367332818667234695 113257859050999228000852043)
              ·
                refine ⟨169886788576498842001278065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113257859050999228000852043 169886788576498842001278065)
                ·
                  refine ⟨127415091432374131500958549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169886788576498842001278065 127415091432374131500958549)
                  ·
                    refine ⟨746572801361567176763429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127415091432374131500958549 746572801361567176763429)
                    ·
                      rfl

theorem cell23_4361836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_4361836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361836 prefixEnd_4361836 := by exact prefixLift 4361836
  have htrace : WordTrace (prefixWord ++ tailWord_4361836) baseStart_4361836 baseEnd_4361836 := by
    simpa [prefixWord, tailWord_4361836, baseEnd_4361836] using wordTrace_append hprefix tailTrace_4361836
  have hstable : (prefixWord ++ tailWord_4361836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361836).length < 2 ^ (prefixWord ++ tailWord_4361836).sum := by decide
  have hdescent : baseEnd_4361836 < baseStart_4361836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361840 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 6]
def baseStart_4361840 : Nat := 118140960795 + 4361840 * 2 ^ 59
def prefixEnd_4361840 : Nat := 4983230072969 + 3 ^ 40 * 4361840 * 2
def baseEnd_4361840 : Nat := 248857828667479946071141

theorem tailTrace_4361840 : CollatzResearch.WordTrace tailWord_4361840 prefixEnd_4361840 248857828667479946071141 := by
  unfold tailWord_4361840
  simp only [CollatzResearch.WordTrace]
  refine ⟨79544687258903048904585487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106059583011870731872780649 79544687258903048904585487)
  ·
    refine ⟨119317030888354573356878231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79544687258903048904585487 119317030888354573356878231)
    ·
      refine ⟨178975546332531860035317347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119317030888354573356878231 178975546332531860035317347)
      ·
        refine ⟨268463319498797790052976021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178975546332531860035317347 268463319498797790052976021)
        ·
          refine ⟨12584218101506146408733251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 268463319498797790052976021 12584218101506146408733251)
          ·
            refine ⟨18876327152259219613099877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12584218101506146408733251 18876327152259219613099877)
            ·
              refine ⟨3539311341048603677456227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18876327152259219613099877 3539311341048603677456227)
              ·
                refine ⟨5308967011572905516184341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539311341048603677456227 5308967011572905516184341)
                ·
                  refine ⟨248857828667479946071141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5308967011572905516184341 248857828667479946071141)
                  ·
                    rfl

theorem cell23_4361840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_4361840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361840 prefixEnd_4361840 := by exact prefixLift 4361840
  have htrace : WordTrace (prefixWord ++ tailWord_4361840) baseStart_4361840 baseEnd_4361840 := by
    simpa [prefixWord, tailWord_4361840, baseEnd_4361840] using wordTrace_append hprefix tailTrace_4361840
  have hstable : (prefixWord ++ tailWord_4361840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361840).length < 2 ^ (prefixWord ++ tailWord_4361840).sum := by decide
  have hdescent : baseEnd_4361840 < baseStart_4361840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361867 : List Nat := [1, 1, 1, 1, 4, 1, 4, 5, 1, 1, 3]
def baseStart_4361867 : Nat := 118140960795 + 4361867 * 2 ^ 59
def prefixEnd_4361867 : Nat := 4983230072969 + 3 ^ 40 * 4361867 * 2
def baseEnd_4361867 : Nat := 2239734321984990909002645

theorem tailTrace_4361867 : CollatzResearch.WordTrace tailWord_4361867 prefixEnd_4361867 2239734321984990909002645 := by
  unfold tailWord_4361867
  simp only [CollatzResearch.WordTrace]
  refine ⟨159090359288708281420403855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106060239525805520946935903 159090359288708281420403855)
  ·
    refine ⟨238635538933062422130605783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159090359288708281420403855 238635538933062422130605783)
    ·
      refine ⟨357953308399593633195908675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238635538933062422130605783 357953308399593633195908675)
      ·
        refine ⟨536929962599390449793863013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357953308399593633195908675 536929962599390449793863013)
        ·
          refine ⟨100674367987385709336349315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 536929962599390449793863013 100674367987385709336349315)
          ·
            refine ⟨151011551981078564004523973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100674367987385709336349315 151011551981078564004523973)
            ·
              refine ⟨28314665996452230750848245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151011551981078564004523973 28314665996452230750848245)
              ·
                refine ⟨2654499937167396632892023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28314665996452230750848245 2654499937167396632892023)
                ·
                  refine ⟨3981749905751094949338035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654499937167396632892023 3981749905751094949338035)
                  ·
                    refine ⟨5972624858626642424007053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3981749905751094949338035 5972624858626642424007053)
                    ·
                      refine ⟨2239734321984990909002645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5972624858626642424007053 2239734321984990909002645)
                      ·
                        rfl

theorem cell23_4361867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 1, 3].length) (baseStart_4361867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361867 prefixEnd_4361867 := by exact prefixLift 4361867
  have htrace : WordTrace (prefixWord ++ tailWord_4361867) baseStart_4361867 baseEnd_4361867 := by
    simpa [prefixWord, tailWord_4361867, baseEnd_4361867] using wordTrace_append hprefix tailTrace_4361867
  have hstable : (prefixWord ++ tailWord_4361867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361867).length < 2 ^ (prefixWord ++ tailWord_4361867).sum := by decide
  have hdescent : baseEnd_4361867 < baseStart_4361867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361893 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_4361893 : Nat := 118140960795 + 4361893 * 2 ^ 59
def prefixEnd_4361893 : Nat := 4983230072969 + 3 ^ 40 * 4361893 * 2
def baseEnd_4361893 : Nat := 2239747672482007807277525

theorem tailTrace_4361893 : CollatzResearch.WordTrace tailWord_4361893 prefixEnd_4361893 2239747672482007807277525 := by
  unfold tailWord_4361893
  simp only [CollatzResearch.WordTrace]
  refine ⟨159091307586614087860850333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106060871724409391907233555 159091307586614087860850333)
  ·
    refine ⟨59659240344980282947818875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159091307586614087860850333 59659240344980282947818875)
    ·
      refine ⟨89488860517470424421728313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59659240344980282947818875 89488860517470424421728313)
      ·
        refine ⟨67116645388102818316296235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89488860517470424421728313 67116645388102818316296235)
        ·
          refine ⟨100674968082154227474444353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67116645388102818316296235 100674968082154227474444353)
          ·
            refine ⟨75506226061615670605833265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100674968082154227474444353 75506226061615670605833265)
            ·
              refine ⟨56629669546211752954374949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75506226061615670605833265 56629669546211752954374949)
              ·
                refine ⟨10618063039914703678945303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56629669546211752954374949 10618063039914703678945303)
                ·
                  refine ⟨15927094559872055518417955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10618063039914703678945303 15927094559872055518417955)
                  ·
                    refine ⟨23890641839808083277626933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15927094559872055518417955 23890641839808083277626933)
                    ·
                      refine ⟨2239747672482007807277525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23890641839808083277626933 2239747672482007807277525)
                      ·
                        rfl

theorem cell23_4361893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_4361893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361893 prefixEnd_4361893 := by exact prefixLift 4361893
  have htrace : WordTrace (prefixWord ++ tailWord_4361893) baseStart_4361893 baseEnd_4361893 := by
    simpa [prefixWord, tailWord_4361893, baseEnd_4361893] using wordTrace_append hprefix tailTrace_4361893
  have hstable : (prefixWord ++ tailWord_4361893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361893).length < 2 ^ (prefixWord ++ tailWord_4361893).sum := by decide
  have hdescent : baseEnd_4361893 < baseStart_4361893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361907 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 3, 2, 2]
def baseStart_4361907 : Nat := 118140960795 + 4361907 * 2 ^ 59
def prefixEnd_4361907 : Nat := 4983230072969 + 3 ^ 40 * 4361907 * 2
def baseEnd_4361907 : Nat := 2239754861211170752502461

theorem tailTrace_4361907 : CollatzResearch.WordTrace tailWord_4361907 prefixEnd_4361907 2239754861211170752502461 := by
  unfold tailWord_4361907
  simp only [CollatzResearch.WordTrace]
  refine ⟨159091818208563368251859975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106061212139042245501239983 159091818208563368251859975)
  ·
    refine ⟨238637727312845052377789963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159091818208563368251859975 238637727312845052377789963)
    ·
      refine ⟨357956590969267578566684945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238637727312845052377789963 357956590969267578566684945)
      ·
        refine ⟨268467443226950683925013709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357956590969267578566684945 268467443226950683925013709)
        ·
          refine ⟨100675291210106506471880141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268467443226950683925013709 100675291210106506471880141)
          ·
            refine ⟨37753234203789939926955053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100675291210106506471880141 37753234203789939926955053)
            ·
              refine ⟨14157462826421227472608145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37753234203789939926955053 14157462826421227472608145)
              ·
                refine ⟨10618097119815920604456109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14157462826421227472608145 10618097119815920604456109)
                ·
                  refine ⟨3981786419930970226671041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10618097119815920604456109 3981786419930970226671041)
                  ·
                    refine ⟨2986339814948227670003281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3981786419930970226671041 2986339814948227670003281)
                    ·
                      refine ⟨2239754861211170752502461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986339814948227670003281 2239754861211170752502461)
                      ·
                        rfl

theorem cell23_4361907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2, 2].length) (baseStart_4361907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361907 prefixEnd_4361907 := by exact prefixLift 4361907
  have htrace : WordTrace (prefixWord ++ tailWord_4361907) baseStart_4361907 baseEnd_4361907 := by
    simpa [prefixWord, tailWord_4361907, baseEnd_4361907] using wordTrace_append hprefix tailTrace_4361907
  have hstable : (prefixWord ++ tailWord_4361907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361907).length < 2 ^ (prefixWord ++ tailWord_4361907).sum := by decide
  have hdescent : baseEnd_4361907 < baseStart_4361907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361963 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_4361963 : Nat := 118140960795 + 4361963 * 2 ^ 59
def prefixEnd_4361963 : Nat := 4983230072969 + 3 ^ 40 * 4361963 * 2
def baseEnd_4361963 : Nat := 2239783616127822533402203

theorem tailTrace_4361963 : CollatzResearch.WordTrace tailWord_4361963 prefixEnd_4361963 2239783616127822533402203 := by
  unfold tailWord_4361963
  simp only [CollatzResearch.WordTrace]
  refine ⟨159093860696360489815898543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106062573797573659877265695 159093860696360489815898543)
  ·
    refine ⟨238640791044540734723847815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159093860696360489815898543 238640791044540734723847815)
    ·
      refine ⟨357961186566811102085771723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238640791044540734723847815 357961186566811102085771723)
      ·
        refine ⟨536941779850216653128657585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357961186566811102085771723 536941779850216653128657585)
        ·
          refine ⟨402706334887662489846493189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536941779850216653128657585 402706334887662489846493189)
          ·
            refine ⟨75507437791436716846217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 402706334887662489846493189 75507437791436716846217473)
            ·
              refine ⟨56630578343577537634663105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75507437791436716846217473 56630578343577537634663105)
              ·
                refine ⟨42472933757683153225997329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56630578343577537634663105 42472933757683153225997329)
                ·
                  refine ⟨31854700318262364919497997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42472933757683153225997329 31854700318262364919497997)
                  ·
                    refine ⟨11945512619348386844811749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31854700318262364919497997 11945512619348386844811749)
                    ·
                      refine ⟨2239783616127822533402203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11945512619348386844811749 2239783616127822533402203)
                      ·
                        rfl

theorem cell23_4361963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_4361963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361963 prefixEnd_4361963 := by exact prefixLift 4361963
  have htrace : WordTrace (prefixWord ++ tailWord_4361963) baseStart_4361963 baseEnd_4361963 := by
    simpa [prefixWord, tailWord_4361963, baseEnd_4361963] using wordTrace_append hprefix tailTrace_4361963
  have hstable : (prefixWord ++ tailWord_4361963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361963).length < 2 ^ (prefixWord ++ tailWord_4361963).sum := by decide
  have hdescent : baseEnd_4361963 < baseStart_4361963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4361983 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_4361983 : Nat := 118140960795 + 4361983 * 2 ^ 59
def prefixEnd_4361983 : Nat := 4983230072969 + 3 ^ 40 * 4361983 * 2
def baseEnd_4361983 : Nat := 2239793885740912455152111

theorem tailTrace_4361983 : CollatzResearch.WordTrace tailWord_4361983 prefixEnd_4361983 2239793885740912455152111 := by
  unfold tailWord_4361983
  simp only [CollatzResearch.WordTrace]
  refine ⟨159094590156288033231626603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106063060104192022154417735 159094590156288033231626603)
  ·
    refine ⟨238641885234432049847439905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159094590156288033231626603 238641885234432049847439905)
    ·
      refine ⟨178981413925824037385579929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238641885234432049847439905 178981413925824037385579929)
      ·
        refine ⟨134236060444368028039184947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178981413925824037385579929 134236060444368028039184947)
        ·
          refine ⟨201354090666552042058777421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134236060444368028039184947 201354090666552042058777421)
          ·
            refine ⟨75507783999957015772041533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201354090666552042058777421 75507783999957015772041533)
            ·
              refine ⟨28315418999983880914515575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75507783999957015772041533 28315418999983880914515575)
              ·
                refine ⟨42473128499975821371773363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28315418999983880914515575 42473128499975821371773363)
                ·
                  refine ⟨63709692749963732057660045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42473128499975821371773363 63709692749963732057660045)
                  ·
                    refine ⟨23891134781236399521622517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63709692749963732057660045 23891134781236399521622517)
                    ·
                      refine ⟨2239793885740912455152111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23891134781236399521622517 2239793885740912455152111)
                      ·
                        rfl

theorem cell23_4361983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_4361983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4361983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4361983 prefixEnd_4361983 := by exact prefixLift 4361983
  have htrace : WordTrace (prefixWord ++ tailWord_4361983) baseStart_4361983 baseEnd_4361983 := by
    simpa [prefixWord, tailWord_4361983, baseEnd_4361983] using wordTrace_append hprefix tailTrace_4361983
  have hstable : (prefixWord ++ tailWord_4361983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4361983).length < 2 ^ (prefixWord ++ tailWord_4361983).sum := by decide
  have hdescent : baseEnd_4361983 < baseStart_4361983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4361983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362003 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 7]
def baseStart_4362003 : Nat := 118140960795 + 4362003 * 2 ^ 59
def prefixEnd_4362003 : Nat := 4983230072969 + 3 ^ 40 * 4362003 * 2
def baseEnd_4362003 : Nat := 248867128372666930766891

theorem tailTrace_4362003 : CollatzResearch.WordTrace tailWord_4362003 prefixEnd_4362003 248867128372666930766891 := by
  unfold tailWord_4362003
  simp only [CollatzResearch.WordTrace]
  refine ⟨159095319616215576647354663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106063546410810384431569775 159095319616215576647354663)
  ·
    refine ⟨238642979424323364971031995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159095319616215576647354663 238642979424323364971031995)
    ·
      refine ⟨357964469136485047456547993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238642979424323364971031995 357964469136485047456547993)
      ·
        refine ⟨268473351852363785592410995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357964469136485047456547993 268473351852363785592410995)
        ·
          refine ⟨402710027778545678388616493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268473351852363785592410995 402710027778545678388616493)
          ·
            refine ⟨151016260416954629395731185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402710027778545678388616493 151016260416954629395731185)
            ·
              refine ⟨113262195312715972046798389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151016260416954629395731185 113262195312715972046798389)
              ·
                refine ⟨10618330810567122379387349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113262195312715972046798389 10618330810567122379387349)
                ·
                  refine ⟨248867128372666930766891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10618330810567122379387349 248867128372666930766891)
                  ·
                    rfl

theorem cell23_4362003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 7].length) (baseStart_4362003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362003 prefixEnd_4362003 := by exact prefixLift 4362003
  have htrace : WordTrace (prefixWord ++ tailWord_4362003) baseStart_4362003 baseEnd_4362003 := by
    simpa [prefixWord, tailWord_4362003, baseEnd_4362003] using wordTrace_append hprefix tailTrace_4362003
  have hstable : (prefixWord ++ tailWord_4362003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362003).length < 2 ^ (prefixWord ++ tailWord_4362003).sum := by decide
  have hdescent : baseEnd_4362003 < baseStart_4362003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362084 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_4362084 : Nat := 118140960795 + 4362084 * 2 ^ 59
def prefixEnd_4362084 : Nat := 4983230072969 + 3 ^ 40 * 4362084 * 2
def baseEnd_4362084 : Nat := 746615249095672186663049

theorem tailTrace_4362084 : CollatzResearch.WordTrace tailWord_4362084 prefixEnd_4362084 746615249095672186663049 := by
  unfold tailWord_4362084
  simp only [CollatzResearch.WordTrace]
  refine ⟨79549136964461063740526653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106065515952614751654035537 79549136964461063740526653)
  ·
    refine ⟨29830926361672898902697495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79549136964461063740526653 29830926361672898902697495)
    ·
      refine ⟨44746389542509348354046243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29830926361672898902697495 44746389542509348354046243)
      ·
        refine ⟨67119584313764022531069365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44746389542509348354046243 67119584313764022531069365)
        ·
          refine ⟨6292461029415377112287753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67119584313764022531069365 6292461029415377112287753)
          ·
            refine ⟨4719345772061532834215815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292461029415377112287753 4719345772061532834215815)
            ·
              refine ⟨7079018658092299251323723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719345772061532834215815 7079018658092299251323723)
              ·
                refine ⟨10618527987138448876985585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7079018658092299251323723 10618527987138448876985585)
                ·
                  refine ⟨7963895990353836657739189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10618527987138448876985585 7963895990353836657739189)
                  ·
                    refine ⟨746615249095672186663049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7963895990353836657739189 746615249095672186663049)
                    ·
                      rfl

theorem cell23_4362084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_4362084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362084 prefixEnd_4362084 := by exact prefixLift 4362084
  have htrace : WordTrace (prefixWord ++ tailWord_4362084) baseStart_4362084 baseEnd_4362084 := by
    simpa [prefixWord, tailWord_4362084, baseEnd_4362084] using wordTrace_append hprefix tailTrace_4362084
  have hstable : (prefixWord ++ tailWord_4362084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362084).length < 2 ^ (prefixWord ++ tailWord_4362084).sum := by decide
  have hdescent : baseEnd_4362084 < baseStart_4362084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362087 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_4362087 : Nat := 118140960795 + 4362087 * 2 ^ 59
def prefixEnd_4362087 : Nat := 4983230072969 + 3 ^ 40 * 4362087 * 2
def baseEnd_4362087 : Nat := 2239847287728980048251633

theorem tailTrace_4362087 : CollatzResearch.WordTrace tailWord_4362087 prefixEnd_4362087 2239847287728980048251633 := by
  unfold tailWord_4362087
  simp only [CollatzResearch.WordTrace]
  refine ⟨159098383347911258993412515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106065588898607505995608343 159098383347911258993412515)
  ·
    refine ⟨238647575021866888490118773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159098383347911258993412515 238647575021866888490118773)
    ·
      refine ⟨22373210158300020795948635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 238647575021866888490118773 22373210158300020795948635)
      ·
        refine ⟨33559815237450031193922953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22373210158300020795948635 33559815237450031193922953)
        ·
          refine ⟨25169861428087523395442215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33559815237450031193922953 25169861428087523395442215)
          ·
            refine ⟨37754792142131285093163323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25169861428087523395442215 37754792142131285093163323)
            ·
              refine ⟨56632188213196927639744985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37754792142131285093163323 56632188213196927639744985)
              ·
                refine ⟨42474141159897695729808739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56632188213196927639744985 42474141159897695729808739)
                ·
                  refine ⟨63711211739846543594713109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42474141159897695729808739 63711211739846543594713109)
                  ·
                    refine ⟨2986463050305306731002177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63711211739846543594713109 2986463050305306731002177)
                    ·
                      refine ⟨2239847287728980048251633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986463050305306731002177 2239847287728980048251633)
                      ·
                        rfl

theorem cell23_4362087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_4362087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362087 prefixEnd_4362087 := by exact prefixLift 4362087
  have htrace : WordTrace (prefixWord ++ tailWord_4362087) baseStart_4362087 baseEnd_4362087 := by
    simpa [prefixWord, tailWord_4362087, baseEnd_4362087] using wordTrace_append hprefix tailTrace_4362087
  have hstable : (prefixWord ++ tailWord_4362087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362087).length < 2 ^ (prefixWord ++ tailWord_4362087).sum := by decide
  have hdescent : baseEnd_4362087 < baseStart_4362087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362170 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_4362170 : Nat := 118140960795 + 4362170 * 2 ^ 59
def prefixEnd_4362170 : Nat := 4983230072969 + 3 ^ 40 * 4362170 * 2
def baseEnd_4362170 : Nat := 746629968874434407837917

theorem tailTrace_4362170 : CollatzResearch.WordTrace tailWord_4362170 prefixEnd_4362170 746629968874434407837917 := by
  unfold tailWord_4362170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39775352651652641042170991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106067607071073709445789309 39775352651652641042170991)
  ·
    refine ⟨59663028977478961563256487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39775352651652641042170991 59663028977478961563256487)
    ·
      refine ⟨89494543466218442344884731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59663028977478961563256487 89494543466218442344884731)
      ·
        refine ⟨134241815199327663517327097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89494543466218442344884731 134241815199327663517327097)
        ·
          refine ⟨100681361399495747637995323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134241815199327663517327097 100681361399495747637995323)
          ·
            refine ⟨151022042099243621456992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100681361399495747637995323 151022042099243621456992985)
            ·
              refine ⟨113266531574432716092744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151022042099243621456992985 113266531574432716092744739)
              ·
                refine ⟨169899797361649074139117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113266531574432716092744739 169899797361649074139117109)
                ·
                  refine ⟨15928106002654600700542229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169899797361649074139117109 15928106002654600700542229)
                  ·
                    refine ⟨746629968874434407837917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15928106002654600700542229 746629968874434407837917)
                    ·
                      rfl

theorem cell23_4362170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_4362170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362170 prefixEnd_4362170 := by exact prefixLift 4362170
  have htrace : WordTrace (prefixWord ++ tailWord_4362170) baseStart_4362170 baseEnd_4362170 := by
    simpa [prefixWord, tailWord_4362170, baseEnd_4362170] using wordTrace_append hprefix tailTrace_4362170
  have hstable : (prefixWord ++ tailWord_4362170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362170).length < 2 ^ (prefixWord ++ tailWord_4362170).sum := by decide
  have hdescent : baseEnd_4362170 < baseStart_4362170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362200 : List Nat := [2, 1, 2, 2, 2, 2, 1, 11]
def baseStart_4362200 : Nat := 118140960795 + 4362200 * 2 ^ 59
def prefixEnd_4362200 : Nat := 4983230072969 + 3 ^ 40 * 4362200 * 2
def baseEnd_4362200 : Nat := 82959455964553263190319

theorem tailTrace_4362200 : CollatzResearch.WordTrace tailWord_4362200 prefixEnd_4362200 82959455964553263190319 := by
  unfold tailWord_4362200
  simp only [CollatzResearch.WordTrace]
  refine ⟨79551252398250939646138027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106068336531001252861517369 79551252398250939646138027)
  ·
    refine ⟨119326878597376409469207041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79551252398250939646138027 119326878597376409469207041)
    ·
      refine ⟨89495158948032307101905281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119326878597376409469207041 89495158948032307101905281)
      ·
        refine ⟨67121369211024230326428961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89495158948032307101905281 67121369211024230326428961)
        ·
          refine ⟨50341026908268172744821721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67121369211024230326428961 50341026908268172744821721)
          ·
            refine ⟨37755770181201129558616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50341026908268172744821721 37755770181201129558616291)
            ·
              refine ⟨56633655271801694337924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37755770181201129558616291 56633655271801694337924437)
              ·
                refine ⟨82959455964553263190319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56633655271801694337924437 82959455964553263190319)
                ·
                  rfl

theorem cell23_4362200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 11].length) (baseStart_4362200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362200 prefixEnd_4362200 := by exact prefixLift 4362200
  have htrace : WordTrace (prefixWord ++ tailWord_4362200) baseStart_4362200 baseEnd_4362200 := by
    simpa [prefixWord, tailWord_4362200, baseEnd_4362200] using wordTrace_append hprefix tailTrace_4362200
  have hstable : (prefixWord ++ tailWord_4362200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362200).length < 2 ^ (prefixWord ++ tailWord_4362200).sum := by decide
  have hdescent : baseEnd_4362200 < baseStart_4362200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362207 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_4362207 : Nat := 118140960795 + 4362207 * 2 ^ 59
def prefixEnd_4362207 : Nat := 4983230072969 + 3 ^ 40 * 4362207 * 2
def baseEnd_4362207 : Nat := 2239908905407519578751081

theorem tailTrace_4362207 : CollatzResearch.WordTrace tailWord_4362207 prefixEnd_4362207 2239908905407519578751081 := by
  unfold tailWord_4362207
  simp only [CollatzResearch.WordTrace]
  refine ⟨159102760107476519487780875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106068506738317679658520583 159102760107476519487780875)
  ·
    refine ⟨238654140161214779231671313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159102760107476519487780875 238654140161214779231671313)
    ·
      refine ⟨178990605120911084423753485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238654140161214779231671313 178990605120911084423753485)
      ·
        refine ⟨67121476920341656658907557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178990605120911084423753485 67121476920341656658907557)
        ·
          refine ⟨12585276922564060623545167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67121476920341656658907557 12585276922564060623545167)
          ·
            refine ⟨18877915383846090935317751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12585276922564060623545167 18877915383846090935317751)
            ·
              refine ⟨28316873075769136402976627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18877915383846090935317751 28316873075769136402976627)
              ·
                refine ⟨42475309613653704604464941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28316873075769136402976627 42475309613653704604464941)
                ·
                  refine ⟨15928241105120139226674353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42475309613653704604464941 15928241105120139226674353)
                  ·
                    refine ⟨11946180828840104420005765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15928241105120139226674353 11946180828840104420005765)
                    ·
                      refine ⟨2239908905407519578751081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11946180828840104420005765 2239908905407519578751081)
                      ·
                        rfl

theorem cell23_4362207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_4362207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362207 prefixEnd_4362207 := by exact prefixLift 4362207
  have htrace : WordTrace (prefixWord ++ tailWord_4362207) baseStart_4362207 baseEnd_4362207 := by
    simpa [prefixWord, tailWord_4362207, baseEnd_4362207] using wordTrace_append hprefix tailTrace_4362207
  have hstable : (prefixWord ++ tailWord_4362207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362207).length < 2 ^ (prefixWord ++ tailWord_4362207).sum := by decide
  have hdescent : baseEnd_4362207 < baseStart_4362207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362211 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 1, 1, 4]
def baseStart_4362211 : Nat := 118140960795 + 4362211 * 2 ^ 59
def prefixEnd_4362211 : Nat := 4983230072969 + 3 ^ 40 * 4362211 * 2
def baseEnd_4362211 : Nat := 2239910959330137563101063

theorem tailTrace_4362211 : CollatzResearch.WordTrace tailWord_4362211 prefixEnd_4362211 2239910959330137563101063 := by
  unfold tailWord_4362211
  simp only [CollatzResearch.WordTrace]
  refine ⟨159102905999462028170926487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106068603999641352113950991 159102905999462028170926487)
  ·
    refine ⟨238654358999193042256389731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159102905999462028170926487 238654358999193042256389731)
    ·
      refine ⟨357981538498789563384584597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238654358999193042256389731 357981538498789563384584597)
      ·
        refine ⟨16780384617130760783652403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 357981538498789563384584597 16780384617130760783652403)
        ·
          refine ⟨25170576925696141175478605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16780384617130760783652403 25170576925696141175478605)
          ·
            refine ⟨9438966347136052940804477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25170576925696141175478605 9438966347136052940804477)
            ·
              refine ⟨3539612380176019852801679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9438966347136052940804477 3539612380176019852801679)
              ·
                refine ⟨5309418570264029779202519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539612380176019852801679 5309418570264029779202519)
                ·
                  refine ⟨7964127855396044668803779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5309418570264029779202519 7964127855396044668803779)
                  ·
                    refine ⟨11946191783094067003205669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7964127855396044668803779 11946191783094067003205669)
                    ·
                      refine ⟨2239910959330137563101063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11946191783094067003205669 2239910959330137563101063)
                      ·
                        rfl

theorem cell23_4362211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_4362211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362211 prefixEnd_4362211 := by exact prefixLift 4362211
  have htrace : WordTrace (prefixWord ++ tailWord_4362211) baseStart_4362211 baseEnd_4362211 := by
    simpa [prefixWord, tailWord_4362211, baseEnd_4362211] using wordTrace_append hprefix tailTrace_4362211
  have hstable : (prefixWord ++ tailWord_4362211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362211).length < 2 ^ (prefixWord ++ tailWord_4362211).sum := by decide
  have hdescent : baseEnd_4362211 < baseStart_4362211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362271 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 1, 3, 2]
def baseStart_4362271 : Nat := 118140960795 + 4362271 * 2 ^ 59
def prefixEnd_4362271 : Nat := 4983230072969 + 3 ^ 40 * 4362271 * 2
def baseEnd_4362271 : Nat := 2239941768169407328350787

theorem tailTrace_4362271 : CollatzResearch.WordTrace tailWord_4362271 prefixEnd_4362271 2239941768169407328350787 := by
  unfold tailWord_4362271
  simp only [CollatzResearch.WordTrace]
  refine ⟨159105094379244658418110667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106070062919496438945407111 159105094379244658418110667)
  ·
    refine ⟨238657641568866987627166001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159105094379244658418110667 238657641568866987627166001)
    ·
      refine ⟨178993231176650240720374501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238657641568866987627166001 178993231176650240720374501)
      ·
        refine ⟨33561230845621920135070219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178993231176650240720374501 33561230845621920135070219)
        ·
          refine ⟨50341846268432880202605329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33561230845621920135070219 50341846268432880202605329)
          ·
            refine ⟨37756384701324660151953997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50341846268432880202605329 37756384701324660151953997)
            ·
              refine ⟨14158644262996747556982749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37756384701324660151953997 14158644262996747556982749)
              ·
                refine ⟨5309491598623780333868531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14158644262996747556982749 5309491598623780333868531)
                ·
                  refine ⟨7964237397935670500802797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5309491598623780333868531 7964237397935670500802797)
                  ·
                    refine ⟨2986589024225876437801049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7964237397935670500802797 2986589024225876437801049)
                    ·
                      refine ⟨2239941768169407328350787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986589024225876437801049 2239941768169407328350787)
                      ·
                        rfl

theorem cell23_4362271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_4362271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362271 prefixEnd_4362271 := by exact prefixLift 4362271
  have htrace : WordTrace (prefixWord ++ tailWord_4362271) baseStart_4362271 baseEnd_4362271 := by
    simpa [prefixWord, tailWord_4362271, baseEnd_4362271] using wordTrace_append hprefix tailTrace_4362271
  have hstable : (prefixWord ++ tailWord_4362271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362271).length < 2 ^ (prefixWord ++ tailWord_4362271).sum := by decide
  have hdescent : baseEnd_4362271 < baseStart_4362271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362277 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_4362277 : Nat := 118140960795 + 4362277 * 2 ^ 59
def prefixEnd_4362277 : Nat := 4983230072969 + 3 ^ 40 * 4362277 * 2
def baseEnd_4362277 : Nat := 746648283017778101625253

theorem tailTrace_4362277 : CollatzResearch.WordTrace tailWord_4362277 prefixEnd_4362277 746648283017778101625253 := by
  unfold tailWord_4362277
  simp only [CollatzResearch.WordTrace]
  refine ⟨159105313217222921442829085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106070208811481947628552723 159105313217222921442829085)
  ·
    refine ⟨59664492456458595541060907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159105313217222921442829085 59664492456458595541060907)
    ·
      refine ⟨89496738684687893311591361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59664492456458595541060907 89496738684687893311591361)
      ·
        refine ⟨67122554013515919983693521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89496738684687893311591361 67122554013515919983693521)
        ·
          refine ⟨50341915510136939987770141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67122554013515919983693521 50341915510136939987770141)
          ·
            refine ⟨18878218316301352495413803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50341915510136939987770141 18878218316301352495413803)
            ·
              refine ⟨28317327474452028743120705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18878218316301352495413803 28317327474452028743120705)
              ·
                refine ⟨21237995605839021557340529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28317327474452028743120705 21237995605839021557340529)
                ·
                  refine ⟨15928496704379266168005397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21237995605839021557340529 15928496704379266168005397)
                  ·
                    refine ⟨746648283017778101625253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15928496704379266168005397 746648283017778101625253)
                    ·
                      rfl

theorem cell23_4362277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_4362277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362277 prefixEnd_4362277 := by exact prefixLift 4362277
  have htrace : WordTrace (prefixWord ++ tailWord_4362277) baseStart_4362277 baseEnd_4362277 := by
    simpa [prefixWord, tailWord_4362277, baseEnd_4362277] using wordTrace_append hprefix tailTrace_4362277
  have hstable : (prefixWord ++ tailWord_4362277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362277).length < 2 ^ (prefixWord ++ tailWord_4362277).sum := by decide
  have hdescent : baseEnd_4362277 < baseStart_4362277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362287 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_4362287 : Nat := 118140960795 + 4362287 * 2 ^ 59
def prefixEnd_4362287 : Nat := 4983230072969 + 3 ^ 40 * 4362287 * 2
def baseEnd_4362287 : Nat := 2239949983859879265750713

theorem tailTrace_4362287 : CollatzResearch.WordTrace tailWord_4362287 prefixEnd_4362287 2239949983859879265750713 := by
  unfold tailWord_4362287
  simp only [CollatzResearch.WordTrace]
  refine ⟨159105677947186693150693115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106070451964791128767128743 159105677947186693150693115)
  ·
    refine ⟨238658516920780039726039673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159105677947186693150693115 238658516920780039726039673)
    ·
      refine ⟨178993887690585029794529755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238658516920780039726039673 178993887690585029794529755)
      ·
        refine ⟨268490831535877544691794633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178993887690585029794529755 268490831535877544691794633)
        ·
          refine ⟨201368123651908158518845975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268490831535877544691794633 201368123651908158518845975)
          ·
            refine ⟨302052185477862237778268963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201368123651908158518845975 302052185477862237778268963)
            ·
              refine ⟨453078278216793356667403445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302052185477862237778268963 453078278216793356667403445)
              ·
                refine ⟨42476088582824377187569073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453078278216793356667403445 42476088582824377187569073)
                ·
                  refine ⟨31857066437118282890676805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42476088582824377187569073 31857066437118282890676805)
                  ·
                    refine ⟨5973199956959678042001901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31857066437118282890676805 5973199956959678042001901)
                    ·
                      refine ⟨2239949983859879265750713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973199956959678042001901 2239949983859879265750713)
                      ·
                        rfl

theorem cell23_4362287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_4362287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362287 prefixEnd_4362287 := by exact prefixLift 4362287
  have htrace : WordTrace (prefixWord ++ tailWord_4362287) baseStart_4362287 baseEnd_4362287 := by
    simpa [prefixWord, tailWord_4362287, baseEnd_4362287] using wordTrace_append hprefix tailTrace_4362287
  have hstable : (prefixWord ++ tailWord_4362287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362287).length < 2 ^ (prefixWord ++ tailWord_4362287).sum := by decide
  have hdescent : baseEnd_4362287 < baseStart_4362287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362294 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4362294 : Nat := 118140960795 + 4362294 * 2 ^ 59
def prefixEnd_4362294 : Nat := 4983230072969 + 3 ^ 40 * 4362294 * 2
def baseEnd_4362294 : Nat := 746651192741486912787727

theorem tailTrace_4362294 : CollatzResearch.WordTrace tailWord_4362294 prefixEnd_4362294 746651192741486912787727 := by
  unfold tailWord_4362294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9944120828635083334137371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106070622172107555564131957 9944120828635083334137371)
  ·
    refine ⟨14916181242952625001206057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9944120828635083334137371 14916181242952625001206057)
    ·
      refine ⟨11187135932214468750904543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14916181242952625001206057 11187135932214468750904543)
      ·
        refine ⟨16780703898321703126356815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11187135932214468750904543 16780703898321703126356815)
        ·
          refine ⟨25171055847482554689535223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16780703898321703126356815 25171055847482554689535223)
          ·
            refine ⟨37756583771223832034302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25171055847482554689535223 37756583771223832034302835)
            ·
              refine ⟨56634875656835748051454253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37756583771223832034302835 56634875656835748051454253)
              ·
                refine ⟨21238078371313405519295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56634875656835748051454253 21238078371313405519295345)
                ·
                  refine ⟨15928558778485054139471509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21238078371313405519295345 15928558778485054139471509)
                  ·
                    refine ⟨746651192741486912787727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15928558778485054139471509 746651192741486912787727)
                    ·
                      rfl

theorem cell23_4362294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4362294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362294 prefixEnd_4362294 := by exact prefixLift 4362294
  have htrace : WordTrace (prefixWord ++ tailWord_4362294) baseStart_4362294 baseEnd_4362294 := by
    simpa [prefixWord, tailWord_4362294, baseEnd_4362294] using wordTrace_append hprefix tailTrace_4362294
  have hstable : (prefixWord ++ tailWord_4362294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362294).length < 2 ^ (prefixWord ++ tailWord_4362294).sum := by decide
  have hdescent : baseEnd_4362294 < baseStart_4362294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362387 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_4362387 : Nat := 118140960795 + 4362387 * 2 ^ 59
def prefixEnd_4362387 : Nat := 4983230072969 + 3 ^ 40 * 4362387 * 2
def baseEnd_4362387 : Nat := 2240001331925328874500253

theorem tailTrace_4362387 : CollatzResearch.WordTrace tailWord_4362387 prefixEnd_4362387 2240001331925328874500253 := by
  unfold tailWord_4362387
  simp only [CollatzResearch.WordTrace]
  refine ⟨159109325246824410229333415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106072883497882940152888943 159109325246824410229333415)
  ·
    refine ⟨238663987870236615344000123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159109325246824410229333415 238663987870236615344000123)
    ·
      refine ⟨357995981805354923016000185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238663987870236615344000123 357995981805354923016000185)
      ·
        refine ⟨268496986354016192262000139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357995981805354923016000185 268496986354016192262000139)
        ·
          refine ⟨402745479531024288393000209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268496986354016192262000139 402745479531024288393000209)
          ·
            refine ⟨302059109648268216294750157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402745479531024288393000209 302059109648268216294750157)
            ·
              refine ⟨113272166118100581110531309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302059109648268216294750157 113272166118100581110531309)
              ·
                refine ⟨42477062294287717916449241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113272166118100581110531309 42477062294287717916449241)
                ·
                  refine ⟨31857796720715788437336931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42477062294287717916449241 31857796720715788437336931)
                  ·
                    refine ⟨47786695081073682656005397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31857796720715788437336931 47786695081073682656005397)
                    ·
                      refine ⟨2240001331925328874500253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47786695081073682656005397 2240001331925328874500253)
                      ·
                        rfl

theorem cell23_4362387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_4362387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362387 prefixEnd_4362387 := by exact prefixLift 4362387
  have htrace : WordTrace (prefixWord ++ tailWord_4362387) baseStart_4362387 baseEnd_4362387 := by
    simpa [prefixWord, tailWord_4362387, baseEnd_4362387] using wordTrace_append hprefix tailTrace_4362387
  have hstable : (prefixWord ++ tailWord_4362387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362387).length < 2 ^ (prefixWord ++ tailWord_4362387).sum := by decide
  have hdescent : baseEnd_4362387 < baseStart_4362387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362481 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_4362481 : Nat := 118140960795 + 4362481 * 2 ^ 59
def prefixEnd_4362481 : Nat := 4983230072969 + 3 ^ 40 * 4362481 * 2
def baseEnd_4362481 : Nat := 2240049599106851506724821

theorem tailTrace_4362481 : CollatzResearch.WordTrace tailWord_4362481 prefixEnd_4362481 2240049599106851506724821 := by
  unfold tailWord_4362481
  simp only [CollatzResearch.WordTrace]
  refine ⟨159112753708483864283255297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106075169138989242855503531 159112753708483864283255297)
  ·
    refine ⟨119334565281362898212441473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159112753708483864283255297 119334565281362898212441473)
    ·
      refine ⟨89500923961022173659331105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119334565281362898212441473 89500923961022173659331105)
      ·
        refine ⟨67125692970766630244498329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89500923961022173659331105 67125692970766630244498329)
        ·
          refine ⟨50344269728074972683373747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67125692970766630244498329 50344269728074972683373747)
          ·
            refine ⟨75516404592112459025060621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50344269728074972683373747 75516404592112459025060621)
            ·
              refine ⟨28318651722042172134397733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75516404592112459025060621 28318651722042172134397733)
              ·
                refine ⟨5309747197882907275199575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28318651722042172134397733 5309747197882907275199575)
                ·
                  refine ⟨7964620796824360912799363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5309747197882907275199575 7964620796824360912799363)
                  ·
                    refine ⟨11946931195236541369199045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7964620796824360912799363 11946931195236541369199045)
                    ·
                      refine ⟨2240049599106851506724821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11946931195236541369199045 2240049599106851506724821)
                      ·
                        rfl

theorem cell23_4362481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_4362481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362481 prefixEnd_4362481 := by exact prefixLift 4362481
  have htrace : WordTrace (prefixWord ++ tailWord_4362481) baseStart_4362481 baseEnd_4362481 := by
    simpa [prefixWord, tailWord_4362481, baseEnd_4362481] using wordTrace_append hprefix tailTrace_4362481
  have hstable : (prefixWord ++ tailWord_4362481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362481).length < 2 ^ (prefixWord ++ tailWord_4362481).sum := by decide
  have hdescent : baseEnd_4362481 < baseStart_4362481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362492 : List Nat := [2, 2, 2, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_4362492 : Nat := 118140960795 + 4362492 * 2 ^ 59
def prefixEnd_4362492 : Nat := 4983230072969 + 3 ^ 40 * 4362492 * 2
def baseEnd_4362492 : Nat := 2240055247394050963687271

theorem tailTrace_4362492 : CollatzResearch.WordTrace tailWord_4362492 prefixEnd_4362492 2240055247394050963687271 := by
  unfold tailWord_4362492
  simp only [CollatzResearch.WordTrace]
  refine ⟨79556577455722006580952865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106075436607629342107937153 79556577455722006580952865)
  ·
    refine ⟨59667433091791504935714649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79556577455722006580952865 59667433091791504935714649)
    ·
      refine ⟨44750574818843628701785987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59667433091791504935714649 44750574818843628701785987)
      ·
        refine ⟨67125862228265443052678981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44750574818843628701785987 67125862228265443052678981)
        ·
          refine ⟨12586099167799770572377309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67125862228265443052678981 12586099167799770572377309)
          ·
            refine ⟨4719787187924913964641491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12586099167799770572377309 4719787187924913964641491)
            ·
              refine ⟨7079680781887370946962237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719787187924913964641491 7079680781887370946962237)
              ·
                refine ⟨2654880293207764105110839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7079680781887370946962237 2654880293207764105110839)
                ·
                  refine ⟨3982320439811646157666259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654880293207764105110839 3982320439811646157666259)
                  ·
                    refine ⟨5973480659717469236499389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3982320439811646157666259 5973480659717469236499389)
                    ·
                      refine ⟨2240055247394050963687271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973480659717469236499389 2240055247394050963687271)
                      ·
                        rfl

theorem cell23_4362492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_4362492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362492 prefixEnd_4362492 := by exact prefixLift 4362492
  have htrace : WordTrace (prefixWord ++ tailWord_4362492) baseStart_4362492 baseEnd_4362492 := by
    simpa [prefixWord, tailWord_4362492, baseEnd_4362492] using wordTrace_append hprefix tailTrace_4362492
  have hstable : (prefixWord ++ tailWord_4362492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362492).length < 2 ^ (prefixWord ++ tailWord_4362492).sum := by decide
  have hdescent : baseEnd_4362492 < baseStart_4362492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362504 : List Nat := [2, 1, 3, 2, 3, 1, 11]
def baseStart_4362504 : Nat := 118140960795 + 4362504 * 2 ^ 59
def prefixEnd_4362504 : Nat := 4983230072969 + 3 ^ 40 * 4362504 * 2
def baseEnd_4362504 : Nat := 27655079125455616256015

theorem tailTrace_4362504 : CollatzResearch.WordTrace tailWord_4362504 prefixEnd_4362504 27655079125455616256015 := by
  unfold tailWord_4362504
  simp only [CollatzResearch.WordTrace]
  refine ⟨79556796293700269605671283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106075728391600359474228377 79556796293700269605671283)
  ·
    refine ⟨119335194440550404408506925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79556796293700269605671283 119335194440550404408506925)
    ·
      refine ⟨44750697915206401653190097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119335194440550404408506925 44750697915206401653190097)
      ·
        refine ⟨33563023436404801239892573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44750697915206401653190097 33563023436404801239892573)
        ·
          refine ⟨12586133788651800464959715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33563023436404801239892573 12586133788651800464959715)
          ·
            refine ⟨18879200682977700697439573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12586133788651800464959715 18879200682977700697439573)
            ·
              refine ⟨27655079125455616256015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18879200682977700697439573 27655079125455616256015)
              ·
                rfl

theorem cell23_4362504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 11].length) (baseStart_4362504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362504 prefixEnd_4362504 := by exact prefixLift 4362504
  have htrace : WordTrace (prefixWord ++ tailWord_4362504) baseStart_4362504 baseEnd_4362504 := by
    simpa [prefixWord, tailWord_4362504, baseEnd_4362504] using wordTrace_append hprefix tailTrace_4362504
  have hstable : (prefixWord ++ tailWord_4362504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362504).length < 2 ^ (prefixWord ++ tailWord_4362504).sum := by decide
  have hdescent : baseEnd_4362504 < baseStart_4362504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362515 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 1, 2, 2]
def baseStart_4362515 : Nat := 118140960795 + 4362515 * 2 ^ 59
def prefixEnd_4362515 : Nat := 4983230072969 + 3 ^ 40 * 4362515 * 2
def baseEnd_4362515 : Nat := 2240067057449104373699665

theorem tailTrace_4362515 : CollatzResearch.WordTrace tailWord_4362515 prefixEnd_4362515 2240067057449104373699665 := by
  unfold tailWord_4362515
  simp only [CollatzResearch.WordTrace]
  refine ⟨159113993790360688089992999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106075995860240458726661999 159113993790360688089992999)
  ·
    refine ⟨238670990685541032134989499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159113993790360688089992999 238670990685541032134989499)
    ·
      refine ⟨358006486028311548202484249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238670990685541032134989499 358006486028311548202484249)
      ·
        refine ⟨268504864521233661151863187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358006486028311548202484249 268504864521233661151863187)
        ·
          refine ⟨402757296781850491727794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268504864521233661151863187 402757296781850491727794781)
          ·
            refine ⟨151033986293193934397923043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402757296781850491727794781 151033986293193934397923043)
            ·
              refine ⟨226550979439790901596884565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151033986293193934397923043 226550979439790901596884565)
              ·
                refine ⟨2654894290310049628088491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 226550979439790901596884565 2654894290310049628088491)
                ·
                  refine ⟨3982341435465074442132737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654894290310049628088491 3982341435465074442132737)
                  ·
                    refine ⟨2986756076598805831599553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982341435465074442132737 2986756076598805831599553)
                    ·
                      refine ⟨2240067057449104373699665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986756076598805831599553 2240067057449104373699665)
                      ·
                        rfl

theorem cell23_4362515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 2, 2].length) (baseStart_4362515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362515 prefixEnd_4362515 := by exact prefixLift 4362515
  have htrace : WordTrace (prefixWord ++ tailWord_4362515) baseStart_4362515 baseEnd_4362515 := by
    simpa [prefixWord, tailWord_4362515, baseEnd_4362515] using wordTrace_append hprefix tailTrace_4362515
  have hstable : (prefixWord ++ tailWord_4362515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362515).length < 2 ^ (prefixWord ++ tailWord_4362515).sum := by decide
  have hdescent : baseEnd_4362515 < baseStart_4362515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4362524 : Nat := 118140960795 + 4362524 * 2 ^ 59
def prefixEnd_4362524 : Nat := 4983230072969 + 3 ^ 40 * 4362524 * 2
def baseEnd_4362524 : Nat := 2240071678774994838487123

theorem tailTrace_4362524 : CollatzResearch.WordTrace tailWord_4362524 prefixEnd_4362524 2240071678774994838487123 := by
  unfold tailWord_4362524
  simp only [CollatzResearch.WordTrace]
  refine ⟨79557161023664041313535313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106076214698218721751380417 79557161023664041313535313)
  ·
    refine ⟨59667870767748030985151485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79557161023664041313535313 59667870767748030985151485)
    ·
      refine ⟨22375451537905511619431807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59667870767748030985151485 22375451537905511619431807)
      ·
        refine ⟨33563177306858267429147711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22375451537905511619431807 33563177306858267429147711)
        ·
          refine ⟨50344765960287401143721567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33563177306858267429147711 50344765960287401143721567)
          ·
            refine ⟨75517148940431101715582351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50344765960287401143721567 75517148940431101715582351)
            ·
              refine ⟨113275723410646652573373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75517148940431101715582351 113275723410646652573373527)
              ·
                refine ⟨169913585115969978860060291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113275723410646652573373527 169913585115969978860060291)
                ·
                  refine ⟨254870377673954968290090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169913585115969978860060291 254870377673954968290090437)
                  ·
                    refine ⟨47788195813866556554391957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254870377673954968290090437 47788195813866556554391957)
                    ·
                      refine ⟨2240071678774994838487123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47788195813866556554391957 2240071678774994838487123)
                      ·
                        rfl

theorem cell23_4362524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4362524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362524 prefixEnd_4362524 := by exact prefixLift 4362524
  have htrace : WordTrace (prefixWord ++ tailWord_4362524) baseStart_4362524 baseEnd_4362524 := by
    simpa [prefixWord, tailWord_4362524, baseEnd_4362524] using wordTrace_append hprefix tailTrace_4362524
  have hstable : (prefixWord ++ tailWord_4362524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362524).length < 2 ^ (prefixWord ++ tailWord_4362524).sum := by decide
  have hdescent : baseEnd_4362524 < baseStart_4362524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362525 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_4362525 : Nat := 118140960795 + 4362525 * 2 ^ 59
def prefixEnd_4362525 : Nat := 4983230072969 + 3 ^ 40 * 4362525 * 2
def baseEnd_4362525 : Nat := 746690730751883111524873

theorem tailTrace_4362525 : CollatzResearch.WordTrace tailWord_4362525 prefixEnd_4362525 746690730751883111524873 := by
  unfold tailWord_4362525
  simp only [CollatzResearch.WordTrace]
  refine ⟨159114358520324459797857029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106076239013549639865238019 159114358520324459797857029)
  ·
    refine ⟨29833942222560836212098193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159114358520324459797857029 29833942222560836212098193)
    ·
      refine ⟨22375456666920627159073645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29833942222560836212098193 22375456666920627159073645)
      ·
        refine ⟨8390796250095235184652617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22375456666920627159073645 8390796250095235184652617)
        ·
          refine ⟨6293097187571426388489463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8390796250095235184652617 6293097187571426388489463)
          ·
            refine ⟨9439645781357139582734195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293097187571426388489463 9439645781357139582734195)
            ·
              refine ⟨14159468672035709374101293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9439645781357139582734195 14159468672035709374101293)
              ·
                refine ⟨5309800752013391015287985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14159468672035709374101293 5309800752013391015287985)
                ·
                  refine ⟨3982350564010043261465989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5309800752013391015287985 3982350564010043261465989)
                  ·
                    refine ⟨746690730751883111524873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3982350564010043261465989 746690730751883111524873)
                    ·
                      rfl

theorem cell23_4362525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_4362525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362525 prefixEnd_4362525 := by exact prefixLift 4362525
  have htrace : WordTrace (prefixWord ++ tailWord_4362525) baseStart_4362525 baseEnd_4362525 := by
    simpa [prefixWord, tailWord_4362525, baseEnd_4362525] using wordTrace_append hprefix tailTrace_4362525
  have hstable : (prefixWord ++ tailWord_4362525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362525).length < 2 ^ (prefixWord ++ tailWord_4362525).sum := by decide
  have hdescent : baseEnd_4362525 < baseStart_4362525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362531 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3]
def baseStart_4362531 : Nat := 118140960795 + 4362531 * 2 ^ 59
def prefixEnd_4362531 : Nat := 4983230072969 + 3 ^ 40 * 4362531 * 2
def baseEnd_4362531 : Nat := 2240075273139576311099591

theorem tailTrace_4362531 : CollatzResearch.WordTrace tailWord_4362531 prefixEnd_4362531 2240075273139576311099591 := by
  unfold tailWord_4362531
  simp only [CollatzResearch.WordTrace]
  refine ⟨159114577358302722822575447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106076384905535148548383631 159114577358302722822575447)
  ·
    refine ⟨238671866037454084233863171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159114577358302722822575447 238671866037454084233863171)
    ·
      refine ⟨358007799056181126350794757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238671866037454084233863171 358007799056181126350794757)
      ·
        refine ⟨67126462323033961190774017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 358007799056181126350794757 67126462323033961190774017)
        ·
          refine ⟨50344846742275470893080513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67126462323033961190774017 50344846742275470893080513)
          ·
            refine ⟨37758635056706603169810385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50344846742275470893080513 37758635056706603169810385)
            ·
              refine ⟨28318976292529952377357789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37758635056706603169810385 28318976292529952377357789)
              ·
                refine ⟨10619616109698732141509171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28318976292529952377357789 10619616109698732141509171)
                ·
                  refine ⟨15929424164548098212263757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10619616109698732141509171 15929424164548098212263757)
                  ·
                    refine ⟨5973534061705536829598909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15929424164548098212263757 5973534061705536829598909)
                    ·
                      refine ⟨2240075273139576311099591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973534061705536829598909 2240075273139576311099591)
                      ·
                        rfl

theorem cell23_4362531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_4362531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362531 prefixEnd_4362531 := by exact prefixLift 4362531
  have htrace : WordTrace (prefixWord ++ tailWord_4362531) baseStart_4362531 baseEnd_4362531 := by
    simpa [prefixWord, tailWord_4362531, baseEnd_4362531] using wordTrace_append hprefix tailTrace_4362531
  have hstable : (prefixWord ++ tailWord_4362531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362531).length < 2 ^ (prefixWord ++ tailWord_4362531).sum := by decide
  have hdescent : baseEnd_4362531 < baseStart_4362531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362544 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_4362544 : Nat := 118140960795 + 4362544 * 2 ^ 59
def prefixEnd_4362544 : Nat := 4983230072969 + 3 ^ 40 * 4362544 * 2
def baseEnd_4362544 : Nat := 2240081948388084760237031

theorem tailTrace_4362544 : CollatzResearch.WordTrace tailWord_4362544 prefixEnd_4362544 2240081948388084760237031 := by
  unfold tailWord_4362544
  simp only [CollatzResearch.WordTrace]
  refine ⟨79557525753627813021399343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106076701004837084028532457 79557525753627813021399343)
  ·
    refine ⟨119336288630441719532099015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79557525753627813021399343 119336288630441719532099015)
    ·
      refine ⟨179004432945662579298148523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119336288630441719532099015 179004432945662579298148523)
      ·
        refine ⟨268506649418493868947222785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179004432945662579298148523 268506649418493868947222785)
        ·
          refine ⟨201379987063870401710417089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268506649418493868947222785 201379987063870401710417089)
          ·
            refine ⟨151034990297902801282812817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201379987063870401710417089 151034990297902801282812817)
            ·
              refine ⟨113276242723427100962109613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151034990297902801282812817 113276242723427100962109613)
              ·
                refine ⟨42478591021285162860791105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113276242723427100962109613 42478591021285162860791105)
                ·
                  refine ⟨31858943265963872145593329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42478591021285162860791105 31858943265963872145593329)
                  ·
                    refine ⟨23894207449472904109194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31858943265963872145593329 23894207449472904109194997)
                    ·
                      refine ⟨2240081948388084760237031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23894207449472904109194997 2240081948388084760237031)
                      ·
                        rfl

theorem cell23_4362544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_4362544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362544 prefixEnd_4362544 := by exact prefixLift 4362544
  have htrace : WordTrace (prefixWord ++ tailWord_4362544) baseStart_4362544 baseEnd_4362544 := by
    simpa [prefixWord, tailWord_4362544, baseEnd_4362544] using wordTrace_append hprefix tailTrace_4362544
  have hstable : (prefixWord ++ tailWord_4362544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362544).length < 2 ^ (prefixWord ++ tailWord_4362544).sum := by decide
  have hdescent : baseEnd_4362544 < baseStart_4362544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362548 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4362548 : Nat := 118140960795 + 4362548 * 2 ^ 59
def prefixEnd_4362548 : Nat := 4983230072969 + 3 ^ 40 * 4362548 * 2
def baseEnd_4362548 : Nat := 2240084002310702744587013

theorem tailTrace_4362548 : CollatzResearch.WordTrace tailWord_4362548 prefixEnd_4362548 2240084002310702744587013 := by
  unfold tailWord_4362548
  simp only [CollatzResearch.WordTrace]
  refine ⟨79557598699620567362972149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106076798266160756483962865 79557598699620567362972149)
  ·
    refine ⟨7458524878089428190278639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79557598699620567362972149 7458524878089428190278639)
    ·
      refine ⟨11187787317134142285417959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7458524878089428190278639 11187787317134142285417959)
      ·
        refine ⟨16781680975701213428126939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11187787317134142285417959 16781680975701213428126939)
        ·
          refine ⟨25172521463551820142190409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16781680975701213428126939 25172521463551820142190409)
          ·
            refine ⟨18879391097663865106642807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25172521463551820142190409 18879391097663865106642807)
            ·
              refine ⟨28319086646495797659964211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18879391097663865106642807 28319086646495797659964211)
              ·
                refine ⟨42478629969743696489946317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28319086646495797659964211 42478629969743696489946317)
                ·
                  refine ⟨15929486238653886183729869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42478629969743696489946317 15929486238653886183729869)
                  ·
                    refine ⟨5973557339495207318898701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15929486238653886183729869 5973557339495207318898701)
                    ·
                      refine ⟨2240084002310702744587013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973557339495207318898701 2240084002310702744587013)
                      ·
                        rfl

theorem cell23_4362548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4362548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362548 prefixEnd_4362548 := by exact prefixLift 4362548
  have htrace : WordTrace (prefixWord ++ tailWord_4362548) baseStart_4362548 baseEnd_4362548 := by
    simpa [prefixWord, tailWord_4362548, baseEnd_4362548] using wordTrace_append hprefix tailTrace_4362548
  have hstable : (prefixWord ++ tailWord_4362548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362548).length < 2 ^ (prefixWord ++ tailWord_4362548).sum := by decide
  have hdescent : baseEnd_4362548 < baseStart_4362548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362605 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4362605 : Nat := 118140960795 + 4362605 * 2 ^ 59
def prefixEnd_4362605 : Nat := 4983230072969 + 3 ^ 40 * 4362605 * 2
def baseEnd_4362605 : Nat := 2240113270708009021574251

theorem tailTrace_4362605 : CollatzResearch.WordTrace tailWord_4362605 prefixEnd_4362605 2240113270708009021574251 := by
  unfold tailWord_4362605
  simp only [CollatzResearch.WordTrace]
  refine ⟨159117276360034633460769269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106078184240023088973846179 159117276360034633460769269)
  ·
    refine ⟨14917244658753246886947119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159117276360034633460769269 14917244658753246886947119)
    ·
      refine ⟨22375866988129870330420679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14917244658753246886947119 22375866988129870330420679)
      ·
        refine ⟨33563800482194805495631019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22375866988129870330420679 33563800482194805495631019)
        ·
          refine ⟨50345700723292208243446529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33563800482194805495631019 50345700723292208243446529)
          ·
            refine ⟨37759275542469156182584897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50345700723292208243446529 37759275542469156182584897)
            ·
              refine ⟨28319456656851867136938673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37759275542469156182584897 28319456656851867136938673)
              ·
                refine ⟨21239592492638900352704005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28319456656851867136938673 21239592492638900352704005)
                ·
                  refine ⟨3982423592369793816132001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21239592492638900352704005 3982423592369793816132001)
                  ·
                    refine ⟨2986817694277345362099001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982423592369793816132001 2986817694277345362099001)
                    ·
                      refine ⟨2240113270708009021574251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986817694277345362099001 2240113270708009021574251)
                      ·
                        rfl

theorem cell23_4362605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4362605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362605 prefixEnd_4362605 := by exact prefixLift 4362605
  have htrace : WordTrace (prefixWord ++ tailWord_4362605) baseStart_4362605 baseEnd_4362605 := by
    simpa [prefixWord, tailWord_4362605, baseEnd_4362605] using wordTrace_append hprefix tailTrace_4362605
  have hstable : (prefixWord ++ tailWord_4362605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362605).length < 2 ^ (prefixWord ++ tailWord_4362605).sum := by decide
  have hdescent : baseEnd_4362605 < baseStart_4362605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362628 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 5]
def baseStart_4362628 : Nat := 118140960795 + 4362628 * 2 ^ 59
def prefixEnd_4362628 : Nat := 4983230072969 + 3 ^ 40 * 4362628 * 2
def baseEnd_4362628 : Nat := 248902786751451381287405

theorem tailTrace_4362628 : CollatzResearch.WordTrace tailWord_4362628 prefixEnd_4362628 248902786751451381287405 := by
  unfold tailWord_4362628
  simp only [CollatzResearch.WordTrace]
  refine ⟨79559057619475654194428269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106078743492634205592571025 79559057619475654194428269)
  ·
    refine ⟨29834646607303370322910601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79559057619475654194428269 29834646607303370322910601)
    ·
      refine ⟨22375984955477527742182951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29834646607303370322910601 22375984955477527742182951)
      ·
        refine ⟨33563977433216291613274427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22375984955477527742182951 33563977433216291613274427)
        ·
          refine ⟨50345966149824437419911641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33563977433216291613274427 50345966149824437419911641)
          ·
            refine ⟨37759474612368328064933731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50345966149824437419911641 37759474612368328064933731)
            ·
              refine ⟨56639211918552492097400597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37759474612368328064933731 56639211918552492097400597)
              ·
                refine ⟨2654963058682148067065653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56639211918552492097400597 2654963058682148067065653)
                ·
                  refine ⟨248902786751451381287405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2654963058682148067065653 248902786751451381287405)
                  ·
                    rfl

theorem cell23_4362628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_4362628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362628 prefixEnd_4362628 := by exact prefixLift 4362628
  have htrace : WordTrace (prefixWord ++ tailWord_4362628) baseStart_4362628 baseEnd_4362628 := by
    simpa [prefixWord, tailWord_4362628, baseEnd_4362628] using wordTrace_append hprefix tailTrace_4362628
  have hstable : (prefixWord ++ tailWord_4362628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362628).length < 2 ^ (prefixWord ++ tailWord_4362628).sum := by decide
  have hdescent : baseEnd_4362628 < baseStart_4362628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362658 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4362658 : Nat := 118140960795 + 4362658 * 2 ^ 59
def prefixEnd_4362658 : Nat := 4983230072969 + 3 ^ 40 * 4362658 * 2
def baseEnd_4362658 : Nat := 746713495060899104737169

theorem tailTrace_4362658 : CollatzResearch.WordTrace tailWord_4362658 prefixEnd_4362658 746713495060899104737169 := by
  unfold tailWord_4362658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39779802357210655878112157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106079472952561749008299085 39779802357210655878112157)
  ·
    refine ⟨14917425883953995954292059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39779802357210655878112157 14917425883953995954292059)
    ·
      refine ⟨22376138825930993931438089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14917425883953995954292059 22376138825930993931438089)
      ·
        refine ⟨16782104119448245448578567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22376138825930993931438089 16782104119448245448578567)
        ·
          refine ⟨25173156179172368172867851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16782104119448245448578567 25173156179172368172867851)
          ·
            refine ⟨37759734268758552259301777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25173156179172368172867851 37759734268758552259301777)
            ·
              refine ⟨28319800701568914194476333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37759734268758552259301777 28319800701568914194476333)
              ·
                refine ⟨10619925263088342822928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28319800701568914194476333 10619925263088342822928625)
                ·
                  refine ⟨7964943947316257117196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10619925263088342822928625 7964943947316257117196469)
                  ·
                    refine ⟨746713495060899104737169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7964943947316257117196469 746713495060899104737169)
                    ·
                      rfl

theorem cell23_4362658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4362658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362658 prefixEnd_4362658 := by exact prefixLift 4362658
  have htrace : WordTrace (prefixWord ++ tailWord_4362658) baseStart_4362658 baseEnd_4362658 := by
    simpa [prefixWord, tailWord_4362658, baseEnd_4362658] using wordTrace_append hprefix tailTrace_4362658
  have hstable : (prefixWord ++ tailWord_4362658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362658).length < 2 ^ (prefixWord ++ tailWord_4362658).sum := by decide
  have hdescent : baseEnd_4362658 < baseStart_4362658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362661 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_4362661 : Nat := 118140960795 + 4362661 * 2 ^ 59
def prefixEnd_4362661 : Nat := 4983230072969 + 3 ^ 40 * 4362661 * 2
def baseEnd_4362661 : Nat := 2240142025624660802473993

theorem tailTrace_4362661 : CollatzResearch.WordTrace tailWord_4362661 prefixEnd_4362661 2240142025624660802473993 := by
  unfold tailWord_4362661
  simp only [CollatzResearch.WordTrace]
  refine ⟨159119318847831755024807837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106079545898554503349871891 159119318847831755024807837)
  ·
    refine ⟨59669744567936908134302939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159119318847831755024807837 59669744567936908134302939)
    ·
      refine ⟨89504616851905362201454409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59669744567936908134302939 89504616851905362201454409)
      ·
        refine ⟨67128462638929021651090807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89504616851905362201454409 67128462638929021651090807)
        ·
          refine ⟨100692693958393532476636211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67128462638929021651090807 100692693958393532476636211)
          ·
            refine ⟨151039040937590298714954317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100692693958393532476636211 151039040937590298714954317)
            ·
              refine ⟨56639640351596362018107869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151039040937590298714954317 56639640351596362018107869)
              ·
                refine ⟨21239865131848635756790451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56639640351596362018107869 21239865131848635756790451)
                ·
                  refine ⟨31859797697772953635185677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21239865131848635756790451 31859797697772953635185677)
                  ·
                    refine ⟨11947424136664857613194629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31859797697772953635185677 11947424136664857613194629)
                    ·
                      refine ⟨2240142025624660802473993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11947424136664857613194629 2240142025624660802473993)
                      ·
                        rfl

theorem cell23_4362661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_4362661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362661 prefixEnd_4362661 := by exact prefixLift 4362661
  have htrace : WordTrace (prefixWord ++ tailWord_4362661) baseStart_4362661 baseEnd_4362661 := by
    simpa [prefixWord, tailWord_4362661, baseEnd_4362661] using wordTrace_append hprefix tailTrace_4362661
  have hstable : (prefixWord ++ tailWord_4362661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362661).length < 2 ^ (prefixWord ++ tailWord_4362661).sum := by decide
  have hdescent : baseEnd_4362661 < baseStart_4362661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362698 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_4362698 : Nat := 118140960795 + 4362698 * 2 ^ 59
def prefixEnd_4362698 : Nat := 4983230072969 + 3 ^ 40 * 4362698 * 2
def baseEnd_4362698 : Nat := 2240161024408877157711323

theorem tailTrace_4362698 : CollatzResearch.WordTrace tailWord_4362698 prefixEnd_4362698 2240161024408877157711323 := by
  unfold tailWord_4362698
  simp only [CollatzResearch.WordTrace]
  refine ⟨39780167087174427585976187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106080445565798473562603165 39780167087174427585976187)
  ·
    refine ⟨59670250630761641378964281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39780167087174427585976187 59670250630761641378964281)
    ·
      refine ⟨44752687973071231034223211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59670250630761641378964281 44752687973071231034223211)
      ·
        refine ⟨67129031959606846551334817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44752687973071231034223211 67129031959606846551334817)
        ·
          refine ⟨50346773969705134913501113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67129031959606846551334817 50346773969705134913501113)
          ·
            refine ⟨37760080477278851185125835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50346773969705134913501113 37760080477278851185125835)
            ·
              refine ⟨56640120715918276777688753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37760080477278851185125835 56640120715918276777688753)
              ·
                refine ⟨42480090536938707583266565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56640120715918276777688753 42480090536938707583266565)
                ·
                  refine ⟨7965016975676007671862481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42480090536938707583266565 7965016975676007671862481)
                  ·
                    refine ⟨5973762731757005753896861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7965016975676007671862481 5973762731757005753896861)
                    ·
                      refine ⟨2240161024408877157711323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973762731757005753896861 2240161024408877157711323)
                      ·
                        rfl

theorem cell23_4362698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_4362698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362698 prefixEnd_4362698 := by exact prefixLift 4362698
  have htrace : WordTrace (prefixWord ++ tailWord_4362698) baseStart_4362698 baseEnd_4362698 := by
    simpa [prefixWord, tailWord_4362698, baseEnd_4362698] using wordTrace_append hprefix tailTrace_4362698
  have hstable : (prefixWord ++ tailWord_4362698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362698).length < 2 ^ (prefixWord ++ tailWord_4362698).sum := by decide
  have hdescent : baseEnd_4362698 < baseStart_4362698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362778 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_4362778 : Nat := 118140960795 + 4362778 * 2 ^ 59
def prefixEnd_4362778 : Nat := 4983230072969 + 3 ^ 40 * 4362778 * 2
def baseEnd_4362778 : Nat := 746734034287078948236985

theorem tailTrace_4362778 : CollatzResearch.WordTrace tailWord_4362778 prefixEnd_4362778 746734034287078948236985 := by
  unfold tailWord_4362778
  simp only [CollatzResearch.WordTrace]
  refine ⟨39780896547101971001704247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106082390792271922671211325 39780896547101971001704247)
  ·
    refine ⟨59671344820652956502556371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39780896547101971001704247 59671344820652956502556371)
    ·
      refine ⟨89507017230979434753834557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59671344820652956502556371 89507017230979434753834557)
      ·
        refine ⟨33565131461617288032687959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89507017230979434753834557 33565131461617288032687959)
        ·
          refine ⟨50347697192425932049031939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33565131461617288032687959 50347697192425932049031939)
          ·
            refine ⟨75521545788638898073547909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50347697192425932049031939 75521545788638898073547909)
            ·
              refine ⟨14160289835369793388790233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75521545788638898073547909 14160289835369793388790233)
              ·
                refine ⟨10620217376527345041592675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14160289835369793388790233 10620217376527345041592675)
                ·
                  refine ⟨15930326064791017562389013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10620217376527345041592675 15930326064791017562389013)
                  ·
                    refine ⟨746734034287078948236985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15930326064791017562389013 746734034287078948236985)
                    ·
                      rfl

theorem cell23_4362778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_4362778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362778 prefixEnd_4362778 := by exact prefixLift 4362778
  have htrace : WordTrace (prefixWord ++ tailWord_4362778) baseStart_4362778 baseEnd_4362778 := by
    simpa [prefixWord, tailWord_4362778, baseEnd_4362778] using wordTrace_append hprefix tailTrace_4362778
  have hstable : (prefixWord ++ tailWord_4362778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362778).length < 2 ^ (prefixWord ++ tailWord_4362778).sum := by decide
  have hdescent : baseEnd_4362778 < baseStart_4362778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362785 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_4362785 : Nat := 118140960795 + 4362785 * 2 ^ 59
def prefixEnd_4362785 : Nat := 4983230072969 + 3 ^ 40 * 4362785 * 2
def baseEnd_4362785 : Nat := 2240205697225818317323423

theorem tailTrace_4362785 : CollatzResearch.WordTrace tailWord_4362785 prefixEnd_4362785 2240205697225818317323423 := by
  unfold tailWord_4362785
  simp only [CollatzResearch.WordTrace]
  refine ⟨159123841499382524202321809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106082560999588349468214539 159123841499382524202321809)
  ·
    refine ⟨119342881124536893151741357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159123841499382524202321809 119342881124536893151741357)
    ·
      refine ⟨44753580421701334931903009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119342881124536893151741357 44753580421701334931903009)
      ·
        refine ⟨33565185316276001198927257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44753580421701334931903009 33565185316276001198927257)
        ·
          refine ⟨25173888987207000899195443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33565185316276001198927257 25173888987207000899195443)
          ·
            refine ⟨37760833480810501348793165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25173888987207000899195443 37760833480810501348793165)
            ·
              refine ⟨14160312555303938005797437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37760833480810501348793165 14160312555303938005797437)
              ·
                refine ⟨5310117208238976752174039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14160312555303938005797437 5310117208238976752174039)
                ·
                  refine ⟨7965175812358465128261059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310117208238976752174039 7965175812358465128261059)
                  ·
                    refine ⟨11947763718537697692391589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7965175812358465128261059 11947763718537697692391589)
                    ·
                      refine ⟨2240205697225818317323423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11947763718537697692391589 2240205697225818317323423)
                      ·
                        rfl

theorem cell23_4362785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_4362785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362785 prefixEnd_4362785 := by exact prefixLift 4362785
  have htrace : WordTrace (prefixWord ++ tailWord_4362785) baseStart_4362785 baseEnd_4362785 := by
    simpa [prefixWord, tailWord_4362785, baseEnd_4362785] using wordTrace_append hprefix tailTrace_4362785
  have hstable : (prefixWord ++ tailWord_4362785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362785).length < 2 ^ (prefixWord ++ tailWord_4362785).sum := by decide
  have hdescent : baseEnd_4362785 < baseStart_4362785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362802 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_4362802 : Nat := 118140960795 + 4362802 * 2 ^ 59
def prefixEnd_4362802 : Nat := 4983230072969 + 3 ^ 40 * 4362802 * 2
def baseEnd_4362802 : Nat := 2240214426396944750810845

theorem tailTrace_4362802 : CollatzResearch.WordTrace tailWord_4362802 prefixEnd_4362802 2240214426396944750810845 := by
  unfold tailWord_4362802
  simp only [CollatzResearch.WordTrace]
  refine ⟨39781115385080234026422665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106082974360213957403793773 39781115385080234026422665)
  ·
    refine ⟨29835836538810175519816999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39781115385080234026422665 29835836538810175519816999)
    ·
      refine ⟨44753754808215263279725499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29835836538810175519816999 44753754808215263279725499)
      ·
        refine ⟨67130632212322894919588249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44753754808215263279725499 67130632212322894919588249)
        ·
          refine ⟨50347974159242171189691187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67130632212322894919588249 50347974159242171189691187)
          ·
            refine ⟨75521961238863256784536781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50347974159242171189691187 75521961238863256784536781)
            ·
              refine ⟨28320735464573721294201293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75521961238863256784536781 28320735464573721294201293)
              ·
                refine ⟨10620275799215145485325485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28320735464573721294201293 10620275799215145485325485)
                ·
                  refine ⟨3982603424705679556997057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10620275799215145485325485 3982603424705679556997057)
                  ·
                    refine ⟨2986952568529259667747793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982603424705679556997057 2986952568529259667747793)
                    ·
                      refine ⟨2240214426396944750810845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986952568529259667747793 2240214426396944750810845)
                      ·
                        rfl

theorem cell23_4362802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_4362802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362802 prefixEnd_4362802 := by exact prefixLift 4362802
  have htrace : WordTrace (prefixWord ++ tailWord_4362802) baseStart_4362802 baseEnd_4362802 := by
    simpa [prefixWord, tailWord_4362802, baseEnd_4362802] using wordTrace_append hprefix tailTrace_4362802
  have hstable : (prefixWord ++ tailWord_4362802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362802).length < 2 ^ (prefixWord ++ tailWord_4362802).sum := by decide
  have hdescent : baseEnd_4362802 < baseStart_4362802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362811 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_4362811 : Nat := 118140960795 + 4362811 * 2 ^ 59
def prefixEnd_4362811 : Nat := 4983230072969 + 3 ^ 40 * 4362811 * 2
def baseEnd_4362811 : Nat := 2240219047722835215598303

theorem tailTrace_4362811 : CollatzResearch.WordTrace tailWord_4362811 prefixEnd_4362811 2240219047722835215598303 := by
  unfold tailWord_4362811
  simp only [CollatzResearch.WordTrace]
  refine ⟨159124789797288330642768287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106083193198192220428512191 159124789797288330642768287)
  ·
    refine ⟨238687184695932495964152431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159124789797288330642768287 238687184695932495964152431)
    ·
      refine ⟨358030777043898743946228647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238687184695932495964152431 358030777043898743946228647)
      ·
        refine ⟨537046165565848115919342971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358030777043898743946228647 537046165565848115919342971)
        ·
          refine ⟨805569248348772173879014457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537046165565848115919342971 805569248348772173879014457)
          ·
            refine ⟨604176936261579130409260843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805569248348772173879014457 604176936261579130409260843)
            ·
              refine ⟨906265404392368695613891265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604176936261579130409260843 906265404392368695613891265)
              ·
                refine ⟨679699053294276521710418449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906265404392368695613891265 679699053294276521710418449)
                ·
                  refine ⟨509774289970707391282813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 679699053294276521710418449 509774289970707391282813837)
                  ·
                    refine ⟨191165358739015271731055189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509774289970707391282813837 191165358739015271731055189)
                    ·
                      refine ⟨2240219047722835215598303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191165358739015271731055189 2240219047722835215598303)
                      ·
                        rfl

theorem cell23_4362811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_4362811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362811 prefixEnd_4362811 := by exact prefixLift 4362811
  have htrace : WordTrace (prefixWord ++ tailWord_4362811) baseStart_4362811 baseEnd_4362811 := by
    simpa [prefixWord, tailWord_4362811, baseEnd_4362811] using wordTrace_append hprefix tailTrace_4362811
  have hstable : (prefixWord ++ tailWord_4362811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362811).length < 2 ^ (prefixWord ++ tailWord_4362811).sum := by decide
  have hdescent : baseEnd_4362811 < baseStart_4362811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362836 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_4362836 : Nat := 118140960795 + 4362836 * 2 ^ 59
def prefixEnd_4362836 : Nat := 4983230072969 + 3 ^ 40 * 4362836 * 2
def baseEnd_4362836 : Nat := 2240231884739197617785689

theorem tailTrace_4362836 : CollatzResearch.WordTrace tailWord_4362836 prefixEnd_4362836 2240231884739197617785689 := by
  unfold tailWord_4362836
  simp only [CollatzResearch.WordTrace]
  refine ⟨79562850811098879956214181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106083801081465173274952241 79562850811098879956214181)
  ·
    refine ⟨14918034527081039991790159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79562850811098879956214181 14918034527081039991790159)
    ·
      refine ⟨22377051790621559987685239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14918034527081039991790159 22377051790621559987685239)
      ·
        refine ⟨33565577685932339981527859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22377051790621559987685239 33565577685932339981527859)
        ·
          refine ⟨50348366528898509972291789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33565577685932339981527859 50348366528898509972291789)
          ·
            refine ⟨18880637448336941239609421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50348366528898509972291789 18880637448336941239609421)
            ·
              refine ⟨7080239043126352964853533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18880637448336941239609421 7080239043126352964853533)
              ·
                refine ⟨2655089641172382361820075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7080239043126352964853533 2655089641172382361820075)
                ·
                  refine ⟨3982634461758573542730113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655089641172382361820075 3982634461758573542730113)
                  ·
                    refine ⟨2986975846318930157047585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982634461758573542730113 2986975846318930157047585)
                    ·
                      refine ⟨2240231884739197617785689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986975846318930157047585 2240231884739197617785689)
                      ·
                        rfl

theorem cell23_4362836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_4362836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362836 prefixEnd_4362836 := by exact prefixLift 4362836
  have htrace : WordTrace (prefixWord ++ tailWord_4362836) baseStart_4362836 baseEnd_4362836 := by
    simpa [prefixWord, tailWord_4362836, baseEnd_4362836] using wordTrace_append hprefix tailTrace_4362836
  have hstable : (prefixWord ++ tailWord_4362836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362836).length < 2 ^ (prefixWord ++ tailWord_4362836).sum := by decide
  have hdescent : baseEnd_4362836 < baseStart_4362836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362852 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_4362852 : Nat := 118140960795 + 4362852 * 2 ^ 59
def prefixEnd_4362852 : Nat := 4983230072969 + 3 ^ 40 * 4362852 * 2
def baseEnd_4362852 : Nat := 2240240100429669555185615

theorem tailTrace_4362852 : CollatzResearch.WordTrace tailWord_4362852 prefixEnd_4362852 2240240100429669555185615 := by
  unfold tailWord_4362852
  simp only [CollatzResearch.WordTrace]
  refine ⟨79563142595069897322505405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106084190126759863096673873 79563142595069897322505405)
  ·
    refine ⟨29836178473151211495939527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79563142595069897322505405 29836178473151211495939527)
    ·
      refine ⟨44754267709726817243909291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29836178473151211495939527 44754267709726817243909291)
      ·
        refine ⟨67131401564590225865863937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44754267709726817243909291 67131401564590225865863937)
        ·
          refine ⟨50348551173442669399397953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67131401564590225865863937 50348551173442669399397953)
          ·
            refine ⟨37761413380082002049548465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50348551173442669399397953 37761413380082002049548465)
            ·
              refine ⟨28321060035061501537161349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37761413380082002049548465 28321060035061501537161349)
              ·
                refine ⟨5310198756574031538217753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28321060035061501537161349 5310198756574031538217753)
                ·
                  refine ⟨3982649067430523653663315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310198756574031538217753 3982649067430523653663315)
                  ·
                    refine ⟨5973973601145785480494973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3982649067430523653663315 5973973601145785480494973)
                    ·
                      refine ⟨2240240100429669555185615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5973973601145785480494973 2240240100429669555185615)
                      ·
                        rfl

theorem cell23_4362852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_4362852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362852 prefixEnd_4362852 := by exact prefixLift 4362852
  have htrace : WordTrace (prefixWord ++ tailWord_4362852) baseStart_4362852 baseEnd_4362852 := by
    simpa [prefixWord, tailWord_4362852, baseEnd_4362852] using wordTrace_append hprefix tailTrace_4362852
  have hstable : (prefixWord ++ tailWord_4362852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362852).length < 2 ^ (prefixWord ++ tailWord_4362852).sum := by decide
  have hdescent : baseEnd_4362852 < baseStart_4362852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362853 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_4362853 : Nat := 118140960795 + 4362853 * 2 ^ 59
def prefixEnd_4362853 : Nat := 4983230072969 + 3 ^ 40 * 4362853 * 2
def baseEnd_4362853 : Nat := 2240240613910324051273111

theorem tailTrace_4362853 : CollatzResearch.WordTrace tailWord_4362853 prefixEnd_4362853 2240240613910324051273111 := by
  unfold tailWord_4362853
  simp only [CollatzResearch.WordTrace]
  refine ⟨159126321663136171815797213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106084214442090781210531475 159126321663136171815797213)
  ·
    refine ⟨59672370623676064430923955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159126321663136171815797213 59672370623676064430923955)
    ·
      refine ⟨89508555935514096646385933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59672370623676064430923955 89508555935514096646385933)
      ·
        refine ⟨33565708475817786242394725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89508555935514096646385933 33565708475817786242394725)
        ·
          refine ⟨6293570339215834920449011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33565708475817786242394725 6293570339215834920449011)
          ·
            refine ⟨9440355508823752380673517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293570339215834920449011 9440355508823752380673517)
            ·
              refine ⟨3540133315808907142752569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9440355508823752380673517 3540133315808907142752569)
              ·
                refine ⟨2655099986856680357064427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540133315808907142752569 2655099986856680357064427)
                ·
                  refine ⟨3982649980285020535596641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655099986856680357064427 3982649980285020535596641)
                  ·
                    refine ⟨2986987485213765401697481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982649980285020535596641 2986987485213765401697481)
                    ·
                      refine ⟨2240240613910324051273111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2986987485213765401697481 2240240613910324051273111)
                      ·
                        rfl

theorem cell23_4362853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_4362853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362853 prefixEnd_4362853 := by exact prefixLift 4362853
  have htrace : WordTrace (prefixWord ++ tailWord_4362853) baseStart_4362853 baseEnd_4362853 := by
    simpa [prefixWord, tailWord_4362853, baseEnd_4362853] using wordTrace_append hprefix tailTrace_4362853
  have hstable : (prefixWord ++ tailWord_4362853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362853).length < 2 ^ (prefixWord ++ tailWord_4362853).sum := by decide
  have hdescent : baseEnd_4362853 < baseStart_4362853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362892 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4362892 : Nat := 118140960795 + 4362892 * 2 ^ 59
def prefixEnd_4362892 : Nat := 4983230072969 + 3 ^ 40 * 4362892 * 2
def baseEnd_4362892 : Nat := 2240260639655849398685431

theorem tailTrace_4362892 : CollatzResearch.WordTrace tailWord_4362892 prefixEnd_4362892 2240260639655849398685431 := by
  unfold tailWord_4362892
  simp only [CollatzResearch.WordTrace]
  refine ⟨79563872054997440738233465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106085162739996587650977953 79563872054997440738233465)
  ·
    refine ⟨59672904041248080553675099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79563872054997440738233465 59672904041248080553675099)
    ·
      refine ⟨89509356061872120830512649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59672904041248080553675099 89509356061872120830512649)
      ·
        refine ⟨67132017046404090622884487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89509356061872120830512649 67132017046404090622884487)
        ·
          refine ⟨100698025569606135934326731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67132017046404090622884487 100698025569606135934326731)
          ·
            refine ⟨151047038354409203901490097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100698025569606135934326731 151047038354409203901490097)
            ·
              refine ⟨113285278765806902926117573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151047038354409203901490097 113285278765806902926117573)
              ·
                refine ⟨21240989768588794298647045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113285278765806902926117573 21240989768588794298647045)
                ·
                  refine ⟨3982685581610398930996321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21240989768588794298647045 3982685581610398930996321)
                  ·
                    refine ⟨2987014186207799198247241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982685581610398930996321 2987014186207799198247241)
                    ·
                      refine ⟨2240260639655849398685431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987014186207799198247241 2240260639655849398685431)
                      ·
                        rfl

theorem cell23_4362892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4362892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362892 prefixEnd_4362892 := by exact prefixLift 4362892
  have htrace : WordTrace (prefixWord ++ tailWord_4362892) baseStart_4362892 baseEnd_4362892 := by
    simpa [prefixWord, tailWord_4362892, baseEnd_4362892] using wordTrace_append hprefix tailTrace_4362892
  have hstable : (prefixWord ++ tailWord_4362892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362892).length < 2 ^ (prefixWord ++ tailWord_4362892).sum := by decide
  have hdescent : baseEnd_4362892 < baseStart_4362892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362909 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_4362909 : Nat := 118140960795 + 4362909 * 2 ^ 59
def prefixEnd_4362909 : Nat := 4983230072969 + 3 ^ 40 * 4362909 * 2
def baseEnd_4362909 : Nat := 2240269368826975832172853

theorem tailTrace_4362909 : CollatzResearch.WordTrace tailWord_4362909 prefixEnd_4362909 2240269368826975832172853 := by
  unfold tailWord_4362909
  simp only [CollatzResearch.WordTrace]
  refine ⟨159128364150933293379835781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106085576100622195586557187 159128364150933293379835781)
  ·
    refine ⟨29836568278299992508719209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159128364150933293379835781 29836568278299992508719209)
    ·
      refine ⟨22377426208724994381539407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29836568278299992508719209 22377426208724994381539407)
      ·
        refine ⟨33566139313087491572309111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22377426208724994381539407 33566139313087491572309111)
        ·
          refine ⟨50349208969631237358463667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33566139313087491572309111 50349208969631237358463667)
          ·
            refine ⟨75523813454446856037695501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50349208969631237358463667 75523813454446856037695501)
            ·
              refine ⟨28321430045417571014135813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75523813454446856037695501 28321430045417571014135813)
              ·
                refine ⟨5310268133515794565150465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28321430045417571014135813 5310268133515794565150465)
                ·
                  refine ⟨3982701100136845923862849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310268133515794565150465 3982701100136845923862849)
                  ·
                    refine ⟨2987025825102634442897137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3982701100136845923862849 2987025825102634442897137)
                    ·
                      refine ⟨2240269368826975832172853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987025825102634442897137 2240269368826975832172853)
                      ·
                        rfl

theorem cell23_4362909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_4362909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362909 prefixEnd_4362909 := by exact prefixLift 4362909
  have htrace : WordTrace (prefixWord ++ tailWord_4362909) baseStart_4362909 baseEnd_4362909 := by
    simpa [prefixWord, tailWord_4362909, baseEnd_4362909] using wordTrace_append hprefix tailTrace_4362909
  have hstable : (prefixWord ++ tailWord_4362909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362909).length < 2 ^ (prefixWord ++ tailWord_4362909).sum := by decide
  have hdescent : baseEnd_4362909 < baseStart_4362909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362926 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4362926 : Nat := 118140960795 + 4362926 * 2 ^ 59
def prefixEnd_4362926 : Nat := 4983230072969 + 3 ^ 40 * 4362926 * 2
def baseEnd_4362926 : Nat := 2240278097998102265660275

theorem tailTrace_4362926 : CollatzResearch.WordTrace tailWord_4362926 prefixEnd_4362926 2240278097998102265660275 := by
  unfold tailWord_4362926
  simp only [CollatzResearch.WordTrace]
  refine ⟨19891123023983963160400579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106085989461247803522136421 19891123023983963160400579)
  ·
    refine ⟨29836684535975944740600869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19891123023983963160400579 29836684535975944740600869)
    ·
      refine ⟨5594378350495489638862663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29836684535975944740600869 5594378350495489638862663)
      ·
        refine ⟨8391567525743234458293995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594378350495489638862663 8391567525743234458293995)
        ·
          refine ⟨12587351288614851687440993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8391567525743234458293995 12587351288614851687440993)
          ·
            refine ⟨9440513466461138765580745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12587351288614851687440993 9440513466461138765580745)
            ·
              refine ⟨7080385099845854074185559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9440513466461138765580745 7080385099845854074185559)
              ·
                refine ⟨10620577649768781111278339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7080385099845854074185559 10620577649768781111278339)
                ·
                  refine ⟨15930866474653171666917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10620577649768781111278339 15930866474653171666917509)
                  ·
                    refine ⟨2987037463997469687547033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15930866474653171666917509 2987037463997469687547033)
                    ·
                      refine ⟨2240278097998102265660275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987037463997469687547033 2240278097998102265660275)
                      ·
                        rfl

theorem cell23_4362926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4362926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362926 prefixEnd_4362926 := by exact prefixLift 4362926
  have htrace : WordTrace (prefixWord ++ tailWord_4362926) baseStart_4362926 baseEnd_4362926 := by
    simpa [prefixWord, tailWord_4362926, baseEnd_4362926] using wordTrace_append hprefix tailTrace_4362926
  have hstable : (prefixWord ++ tailWord_4362926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362926).length < 2 ^ (prefixWord ++ tailWord_4362926).sum := by decide
  have hdescent : baseEnd_4362926 < baseStart_4362926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362928 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_4362928 : Nat := 118140960795 + 4362928 * 2 ^ 59
def prefixEnd_4362928 : Nat := 4983230072969 + 3 ^ 40 * 4362928 * 2
def baseEnd_4362928 : Nat := 746759708319803752611755

theorem tailTrace_4362928 : CollatzResearch.WordTrace tailWord_4362928 prefixEnd_4362928 746759708319803752611755 := by
  unfold tailWord_4362928
  simp only [CollatzResearch.WordTrace]
  refine ⟨79564528568932229812388719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106086038091909639749851625 79564528568932229812388719)
  ·
    refine ⟨119346792853398344718583079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79564528568932229812388719 119346792853398344718583079)
    ·
      refine ⟨179020189280097517077874619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119346792853398344718583079 179020189280097517077874619)
      ·
        refine ⟨268530283920146275616811929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179020189280097517077874619 268530283920146275616811929)
        ·
          refine ⟨201397712940109706712608947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268530283920146275616811929 201397712940109706712608947)
          ·
            refine ⟨302096569410164560068913421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201397712940109706712608947 302096569410164560068913421)
            ·
              refine ⟨113286213528811710025842533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302096569410164560068913421 113286213528811710025842533)
              ·
                refine ⟨21241165036652195629845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113286213528811710025842533 21241165036652195629845475)
                ·
                  refine ⟨31861747554978293444768213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21241165036652195629845475 31861747554978293444768213)
                  ·
                    refine ⟨746759708319803752611755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31861747554978293444768213 746759708319803752611755)
                    ·
                      rfl

theorem cell23_4362928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_4362928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362928 prefixEnd_4362928 := by exact prefixLift 4362928
  have htrace : WordTrace (prefixWord ++ tailWord_4362928) baseStart_4362928 baseEnd_4362928 := by
    simpa [prefixWord, tailWord_4362928, baseEnd_4362928] using wordTrace_append hprefix tailTrace_4362928
  have hstable : (prefixWord ++ tailWord_4362928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362928).length < 2 ^ (prefixWord ++ tailWord_4362928).sum := by decide
  have hdescent : baseEnd_4362928 < baseStart_4362928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4362985 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_4362985 : Nat := 118140960795 + 4362985 * 2 ^ 59
def prefixEnd_4362985 : Nat := 4983230072969 + 3 ^ 40 * 4362985 * 2
def baseEnd_4362985 : Nat := 2240308393356717534822503

theorem tailTrace_4362985 : CollatzResearch.WordTrace tailWord_4362985 prefixEnd_4362985 2240308393356717534822503 := by
  unfold tailWord_4362985
  simp only [CollatzResearch.WordTrace]
  refine ⟨159131136098657958359602409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106087424065771972239734939 159131136098657958359602409)
  ·
    refine ⟨119348352073993468769701807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159131136098657958359602409 119348352073993468769701807)
    ·
      refine ⟨179022528110990203154552711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119348352073993468769701807 179022528110990203154552711)
      ·
        refine ⟨268533792166485304731829067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179022528110990203154552711 268533792166485304731829067)
        ·
          refine ⟨402800688249727957097743601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268533792166485304731829067 402800688249727957097743601)
          ·
            refine ⟨302100516187295967823307701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402800688249727957097743601 302100516187295967823307701)
            ·
              refine ⟨28321923392558996983435097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302100516187295967823307701 28321923392558996983435097)
              ·
                refine ⟨21241442544419247737576323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28321923392558996983435097 21241442544419247737576323)
                ·
                  refine ⟨31862163816628871606364485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21241442544419247737576323 31862163816628871606364485)
                  ·
                    refine ⟨5974155715617913426193341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31862163816628871606364485 5974155715617913426193341)
                    ·
                      refine ⟨2240308393356717534822503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974155715617913426193341 2240308393356717534822503)
                      ·
                        rfl

theorem cell23_4362985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_4362985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4362985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4362985 prefixEnd_4362985 := by exact prefixLift 4362985
  have htrace : WordTrace (prefixWord ++ tailWord_4362985) baseStart_4362985 baseEnd_4362985 := by
    simpa [prefixWord, tailWord_4362985, baseEnd_4362985] using wordTrace_append hprefix tailTrace_4362985
  have hstable : (prefixWord ++ tailWord_4362985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4362985).length < 2 ^ (prefixWord ++ tailWord_4362985).sum := by decide
  have hdescent : baseEnd_4362985 < baseStart_4362985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4362985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363039 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 6]
def baseStart_4363039 : Nat := 118140960795 + 4363039 * 2 ^ 59
def prefixEnd_4363039 : Nat := 4983230072969 + 3 ^ 40 * 4363039 * 2
def baseEnd_4363039 : Nat := 248926235701340035949695

theorem tailTrace_4363039 : CollatzResearch.WordTrace tailWord_4363039 prefixEnd_4363039 248926235701340035949695 := by
  unfold tailWord_4363039
  simp only [CollatzResearch.WordTrace]
  refine ⟨159133105640462325582068171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106088737093641550388045447 159133105640462325582068171)
  ·
    refine ⟨238699658460693488373102257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159133105640462325582068171 238699658460693488373102257)
    ·
      refine ⟨179024743845520116279826693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238699658460693488373102257 179024743845520116279826693)
      ·
        refine ⟨33567139471035021802467505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179024743845520116279826693 33567139471035021802467505)
        ·
          refine ⟨25175354603276266351850629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33567139471035021802467505 25175354603276266351850629)
          ·
            refine ⟨4720378988114299940971993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25175354603276266351850629 4720378988114299940971993)
            ·
              refine ⟨3540284241085724955728995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4720378988114299940971993 3540284241085724955728995)
              ·
                refine ⟨5310426361628587433593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540284241085724955728995 5310426361628587433593493)
                ·
                  refine ⟨248926235701340035949695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5310426361628587433593493 248926235701340035949695)
                  ·
                    rfl

theorem cell23_4363039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 6].length) (baseStart_4363039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363039 prefixEnd_4363039 := by exact prefixLift 4363039
  have htrace : WordTrace (prefixWord ++ tailWord_4363039) baseStart_4363039 baseEnd_4363039 := by
    simpa [prefixWord, tailWord_4363039, baseEnd_4363039] using wordTrace_append hprefix tailTrace_4363039
  have hstable : (prefixWord ++ tailWord_4363039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363039).length < 2 ^ (prefixWord ++ tailWord_4363039).sum := by decide
  have hdescent : baseEnd_4363039 < baseStart_4363039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363053 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4363053 : Nat := 118140960795 + 4363053 * 2 ^ 59
def prefixEnd_4363053 : Nat := 4983230072969 + 3 ^ 40 * 4363053 * 2
def baseEnd_4363053 : Nat := 2240343310041223268772191

theorem tailTrace_4363053 : CollatzResearch.WordTrace tailWord_4363053 prefixEnd_4363053 2240343310041223268772191 := by
  unfold tailWord_4363053
  simp only [CollatzResearch.WordTrace]
  refine ⟨159133616262411605973077813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106089077508274403982051875 159133616262411605973077813)
  ·
    refine ⟨14918776524601088059976045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159133616262411605973077813 14918776524601088059976045)
    ·
      refine ⟨5594541196725408022491017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14918776524601088059976045 5594541196725408022491017)
      ·
        refine ⟨4195905897544056016868263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5594541196725408022491017 4195905897544056016868263)
        ·
          refine ⟨6293858846316084025302395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195905897544056016868263 6293858846316084025302395)
          ·
            refine ⟨9440788269474126037953593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293858846316084025302395 9440788269474126037953593)
            ·
              refine ⟨7080591202105594528465195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9440788269474126037953593 7080591202105594528465195)
              ·
                refine ⟨10620886803158391792697793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7080591202105594528465195 10620886803158391792697793)
                ·
                  refine ⟨7965665102368793844523345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10620886803158391792697793 7965665102368793844523345)
                  ·
                    refine ⟨5974248826776595383392509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7965665102368793844523345 5974248826776595383392509)
                    ·
                      refine ⟨2240343310041223268772191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974248826776595383392509 2240343310041223268772191)
                      ·
                        rfl

theorem cell23_4363053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4363053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363053 prefixEnd_4363053 := by exact prefixLift 4363053
  have htrace : WordTrace (prefixWord ++ tailWord_4363053) baseStart_4363053 baseEnd_4363053 := by
    simpa [prefixWord, tailWord_4363053, baseEnd_4363053] using wordTrace_append hprefix tailTrace_4363053
  have hstable : (prefixWord ++ tailWord_4363053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363053).length < 2 ^ (prefixWord ++ tailWord_4363053).sum := by decide
  have hdescent : baseEnd_4363053 < baseStart_4363053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363059 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 2, 3, 2]
def baseStart_4363059 : Nat := 118140960795 + 4363059 * 2 ^ 59
def prefixEnd_4363059 : Nat := 4983230072969 + 3 ^ 40 * 4363059 * 2
def baseEnd_4363059 : Nat := 2240346390925150245297163

theorem tailTrace_4363059 : CollatzResearch.WordTrace tailWord_4363059 prefixEnd_4363059 2240346390925150245297163 := by
  unfold tailWord_4363059
  simp only [CollatzResearch.WordTrace]
  refine ⟨159133835100389868997796231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106089223400259912665197487 159133835100389868997796231)
  ·
    refine ⟨238700752650584803496694347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159133835100389868997796231 238700752650584803496694347)
    ·
      refine ⟨358051128975877205245041521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238700752650584803496694347 358051128975877205245041521)
      ·
        refine ⟨268538346731907903933781141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358051128975877205245041521 268538346731907903933781141)
        ·
          refine ⟨12587735003058182996895991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 268538346731907903933781141 12587735003058182996895991)
          ·
            refine ⟨18881602504587274495343987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12587735003058182996895991 18881602504587274495343987)
            ·
              refine ⟨28322403756880911743015981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18881602504587274495343987 28322403756880911743015981)
              ·
                refine ⟨10620901408830341903630993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28322403756880911743015981 10620901408830341903630993)
                ·
                  refine ⟨7965676056622756427723245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10620901408830341903630993 7965676056622756427723245)
                  ·
                    refine ⟨2987128521233533660396217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7965676056622756427723245 2987128521233533660396217)
                    ·
                      refine ⟨2240346390925150245297163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987128521233533660396217 2240346390925150245297163)
                      ·
                        rfl

theorem cell23_4363059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3, 2].length) (baseStart_4363059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363059 prefixEnd_4363059 := by exact prefixLift 4363059
  have htrace : WordTrace (prefixWord ++ tailWord_4363059) baseStart_4363059 baseEnd_4363059 := by
    simpa [prefixWord, tailWord_4363059, baseEnd_4363059] using wordTrace_append hprefix tailTrace_4363059
  have hstable : (prefixWord ++ tailWord_4363059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363059).length < 2 ^ (prefixWord ++ tailWord_4363059).sum := by decide
  have hdescent : baseEnd_4363059 < baseStart_4363059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363072 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_4363072 : Nat := 118140960795 + 4363072 * 2 ^ 59
def prefixEnd_4363072 : Nat := 4983230072969 + 3 ^ 40 * 4363072 * 2
def baseEnd_4363072 : Nat := 2240353066173658694434603

theorem tailTrace_4363072 : CollatzResearch.WordTrace tailWord_4363072 prefixEnd_4363072 2240353066173658694434603 := by
  unfold tailWord_4363072
  simp only [CollatzResearch.WordTrace]
  refine ⟨79567154624671386109009735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106089539499561848145346313 79567154624671386109009735)
  ·
    refine ⟨119350731937007079163514603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79567154624671386109009735 119350731937007079163514603)
    ·
      refine ⟨179026097905510618745271905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119350731937007079163514603 179026097905510618745271905)
      ·
        refine ⟨134269573429132964058953929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179026097905510618745271905 134269573429132964058953929)
        ·
          refine ⟨100702180071849723044215447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134269573429132964058953929 100702180071849723044215447)
          ·
            refine ⟨151053270107774584566323171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100702180071849723044215447 151053270107774584566323171)
            ·
              refine ⟨226579905161661876849484757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151053270107774584566323171 226579905161661876849484757)
              ·
                refine ⟨5310466527226450238659799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226579905161661876849484757 5310466527226450238659799)
                ·
                  refine ⟨7965699790839675357989699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310466527226450238659799 7965699790839675357989699)
                  ·
                    refine ⟨11948549686259513036984549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7965699790839675357989699 11948549686259513036984549)
                    ·
                      refine ⟨2240353066173658694434603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11948549686259513036984549 2240353066173658694434603)
                      ·
                        rfl

theorem cell23_4363072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_4363072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363072 prefixEnd_4363072 := by exact prefixLift 4363072
  have htrace : WordTrace (prefixWord ++ tailWord_4363072) baseStart_4363072 baseEnd_4363072 := by
    simpa [prefixWord, tailWord_4363072, baseEnd_4363072] using wordTrace_append hprefix tailTrace_4363072
  have hstable : (prefixWord ++ tailWord_4363072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363072).length < 2 ^ (prefixWord ++ tailWord_4363072).sum := by decide
  have hdescent : baseEnd_4363072 < baseStart_4363072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363139 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 3]
def baseStart_4363139 : Nat := 118140960795 + 4363139 * 2 ^ 59
def prefixEnd_4363139 : Nat := 4983230072969 + 3 ^ 40 * 4363139 * 2
def baseEnd_4363139 : Nat := 2240387469377509932296795

theorem tailTrace_4363139 : CollatzResearch.WordTrace tailWord_4363139 prefixEnd_4363139 2240387469377509932296795 := by
  unfold tailWord_4363139
  simp only [CollatzResearch.WordTrace]
  refine ⟨159136752940100042660708471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106091168626733361773805647 159136752940100042660708471)
  ·
    refine ⟨238705129410150063991062707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159136752940100042660708471 238705129410150063991062707)
    ·
      refine ⟨358057694115225095986594061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238705129410150063991062707 358057694115225095986594061)
      ·
        refine ⟨134271635293209410994972773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358057694115225095986594061 134271635293209410994972773)
        ·
          refine ⟨25175931617476764561557395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134271635293209410994972773 25175931617476764561557395)
          ·
            refine ⟨37763897426215146842336093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25175931617476764561557395 37763897426215146842336093)
            ·
              refine ⟨14161461534830680065876035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37763897426215146842336093 14161461534830680065876035)
              ·
                refine ⟨21242192302246020098814053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14161461534830680065876035 21242192302246020098814053)
                ·
                  refine ⟨3982911056671128768527635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21242192302246020098814053 3982911056671128768527635)
                  ·
                    refine ⟨5974366585006693152791453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3982911056671128768527635 5974366585006693152791453)
                    ·
                      refine ⟨2240387469377509932296795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974366585006693152791453 2240387469377509932296795)
                      ·
                        rfl

theorem cell23_4363139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_4363139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363139 prefixEnd_4363139 := by exact prefixLift 4363139
  have htrace : WordTrace (prefixWord ++ tailWord_4363139) baseStart_4363139 baseEnd_4363139 := by
    simpa [prefixWord, tailWord_4363139, baseEnd_4363139] using wordTrace_append hprefix tailTrace_4363139
  have hstable : (prefixWord ++ tailWord_4363139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363139).length < 2 ^ (prefixWord ++ tailWord_4363139).sum := by decide
  have hdescent : baseEnd_4363139 < baseStart_4363139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363155 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 8]
def baseStart_4363155 : Nat := 118140960795 + 4363155 * 2 ^ 59
def prefixEnd_4363155 : Nat := 4983230072969 + 3 ^ 40 * 4363155 * 2
def baseEnd_4363155 : Nat := 746798561689327289898907

theorem tailTrace_4363155 : CollatzResearch.WordTrace tailWord_4363155 prefixEnd_4363155 746798561689327289898907 := by
  unfold tailWord_4363155
  simp only [CollatzResearch.WordTrace]
  refine ⟨159137336508042077393290919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106091557672028051595527279 159137336508042077393290919)
  ·
    refine ⟨238706004762063116089936379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159137336508042077393290919 238706004762063116089936379)
    ·
      refine ⟨358059007143094674134904569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238706004762063116089936379 358059007143094674134904569)
      ·
        refine ⟨268544255357321005601178427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358059007143094674134904569 268544255357321005601178427)
        ·
          refine ⟨402816383035981508401767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268544255357321005601178427 402816383035981508401767641)
          ·
            refine ⟨302112287276986131301325731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402816383035981508401767641 302112287276986131301325731)
            ·
              refine ⟨453168430915479196951988597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302112287276986131301325731 453168430915479196951988597)
              ·
                refine ⟨42484540398326174714248931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 453168430915479196951988597 42484540398326174714248931)
                ·
                  refine ⟨63726810597489262071373397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42484540398326174714248931 63726810597489262071373397)
                  ·
                    refine ⟨746798561689327289898907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63726810597489262071373397 746798561689327289898907)
                    ·
                      rfl

theorem cell23_4363155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_4363155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363155 prefixEnd_4363155 := by exact prefixLift 4363155
  have htrace : WordTrace (prefixWord ++ tailWord_4363155) baseStart_4363155 baseEnd_4363155 := by
    simpa [prefixWord, tailWord_4363155, baseEnd_4363155] using wordTrace_append hprefix tailTrace_4363155
  have hstable : (prefixWord ++ tailWord_4363155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363155).length < 2 ^ (prefixWord ++ tailWord_4363155).sum := by decide
  have hdescent : baseEnd_4363155 < baseStart_4363155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363249 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_4363249 : Nat := 118140960795 + 4363249 * 2 ^ 59
def prefixEnd_4363249 : Nat := 4983230072969 + 3 ^ 40 * 4363249 * 2
def baseEnd_4363249 : Nat := 746814650749834833973763

theorem tailTrace_4363249 : CollatzResearch.WordTrace tailWord_4363249 prefixEnd_4363249 746814650749834833973763 := by
  unfold tailWord_4363249
  simp only [CollatzResearch.WordTrace]
  refine ⟨159140764969701531447212801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106093843313134354298141867 159140764969701531447212801)
  ·
    refine ⟨119355573727276148585409601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159140764969701531447212801 119355573727276148585409601)
    ·
      refine ⟨89516680295457111439057201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119355573727276148585409601 89516680295457111439057201)
      ·
        refine ⟨67137510221592833579292901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89516680295457111439057201 67137510221592833579292901)
        ·
          refine ⟨12588283166548656296117419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67137510221592833579292901 12588283166548656296117419)
          ·
            refine ⟨18882424749822984444176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12588283166548656296117419 18882424749822984444176129)
            ·
              refine ⟨14161818562367238333132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18882424749822984444176129 14161818562367238333132097)
              ·
                refine ⟨10621363921775428749849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14161818562367238333132097 10621363921775428749849073)
                ·
                  refine ⟨7966022941331571562386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10621363921775428749849073 7966022941331571562386805)
                  ·
                    refine ⟨746814650749834833973763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7966022941331571562386805 746814650749834833973763)
                    ·
                      rfl

theorem cell23_4363249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_4363249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363249 prefixEnd_4363249 := by exact prefixLift 4363249
  have htrace : WordTrace (prefixWord ++ tailWord_4363249) baseStart_4363249 baseEnd_4363249 := by
    simpa [prefixWord, tailWord_4363249, baseEnd_4363249] using wordTrace_append hprefix tailTrace_4363249
  have hstable : (prefixWord ++ tailWord_4363249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363249).length < 2 ^ (prefixWord ++ tailWord_4363249).sum := by decide
  have hdescent : baseEnd_4363249 < baseStart_4363249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363303 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4363303 : Nat := 118140960795 + 4363303 * 2 ^ 59
def prefixEnd_4363303 : Nat := 4983230072969 + 3 ^ 40 * 4363303 * 2
def baseEnd_4363303 : Nat := 2240471680204847290646041

theorem tailTrace_4363303 : CollatzResearch.WordTrace tailWord_4363303 prefixEnd_4363303 2240471680204847290646041 := by
  unfold tailWord_4363303
  simp only [CollatzResearch.WordTrace]
  refine ⟨159142734511505898669678563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106095156341003932446452375 159142734511505898669678563)
  ·
    refine ⟨238714101767258848004517845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159142734511505898669678563 238714101767258848004517845)
    ·
      refine ⟨5594861760170129250105887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 238714101767258848004517845 5594861760170129250105887)
      ·
        refine ⟨8392292640255193875158831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594861760170129250105887 8392292640255193875158831)
        ·
          refine ⟨12588438960382790812738247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8392292640255193875158831 12588438960382790812738247)
          ·
            refine ⟨18882658440574186219107371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12588438960382790812738247 18882658440574186219107371)
            ·
              refine ⟨28323987660861279328661057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18882658440574186219107371 28323987660861279328661057)
              ·
                refine ⟨21242990745645959496495793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28323987660861279328661057 21242990745645959496495793)
                ·
                  refine ⟨15932243059234469622371845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21242990745645959496495793 15932243059234469622371845)
                  ·
                    refine ⟨2987295573606463054194721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15932243059234469622371845 2987295573606463054194721)
                    ·
                      refine ⟨2240471680204847290646041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987295573606463054194721 2240471680204847290646041)
                      ·
                        rfl

theorem cell23_4363303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4363303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363303 prefixEnd_4363303 := by exact prefixLift 4363303
  have htrace : WordTrace (prefixWord ++ tailWord_4363303) baseStart_4363303 baseEnd_4363303 := by
    simpa [prefixWord, tailWord_4363303, baseEnd_4363303] using wordTrace_append hprefix tailTrace_4363303
  have hstable : (prefixWord ++ tailWord_4363303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363303).length < 2 ^ (prefixWord ++ tailWord_4363303).sum := by decide
  have hdescent : baseEnd_4363303 < baseStart_4363303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363312 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_4363312 : Nat := 118140960795 + 4363312 * 2 ^ 59
def prefixEnd_4363312 : Nat := 4983230072969 + 3 ^ 40 * 4363312 * 2
def baseEnd_4363312 : Nat := 2240476301530737755433499

theorem tailTrace_4363312 : CollatzResearch.WordTrace tailWord_4363312 prefixEnd_4363312 2240476301530737755433499 := by
  unfold tailWord_4363312
  simp only [CollatzResearch.WordTrace]
  refine ⟨79571531384236646603378095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106095375178982195471170793 79571531384236646603378095)
  ·
    refine ⟨119357297076354969905067143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79571531384236646603378095 119357297076354969905067143)
    ·
      refine ⟨179035945614532454857600715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119357297076354969905067143 179035945614532454857600715)
      ·
        refine ⟨268553918421798682286401073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179035945614532454857600715 268553918421798682286401073)
        ·
          refine ⟨201415438816349011714800805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268553918421798682286401073 201415438816349011714800805)
          ·
            refine ⟨37765394778065439696525151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201415438816349011714800805 37765394778065439696525151)
            ·
              refine ⟨56648092167098159544787727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37765394778065439696525151 56648092167098159544787727)
              ·
                refine ⟨84972138250647239317181591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56648092167098159544787727 84972138250647239317181591)
                ·
                  refine ⟨127458207375970858975772387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84972138250647239317181591 127458207375970858975772387)
                  ·
                    refine ⟨191187311063956288463658581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127458207375970858975772387 191187311063956288463658581)
                    ·
                      refine ⟨2240476301530737755433499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191187311063956288463658581 2240476301530737755433499)
                      ·
                        rfl

theorem cell23_4363312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_4363312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363312 prefixEnd_4363312 := by exact prefixLift 4363312
  have htrace : WordTrace (prefixWord ++ tailWord_4363312) baseStart_4363312 baseEnd_4363312 := by
    simpa [prefixWord, tailWord_4363312, baseEnd_4363312] using wordTrace_append hprefix tailTrace_4363312
  have hstable : (prefixWord ++ tailWord_4363312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363312).length < 2 ^ (prefixWord ++ tailWord_4363312).sum := by decide
  have hdescent : baseEnd_4363312 < baseStart_4363312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363336 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_4363336 : Nat := 118140960795 + 4363336 * 2 ^ 59
def prefixEnd_4363336 : Nat := 4983230072969 + 3 ^ 40 * 4363336 * 2
def baseEnd_4363336 : Nat := 2240488625066445661533389

theorem tailTrace_4363336 : CollatzResearch.WordTrace tailWord_4363336 prefixEnd_4363336 2240488625066445661533389 := by
  unfold tailWord_4363336
  simp only [CollatzResearch.WordTrace]
  refine ⟨79571969060193172652814931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106095958746924230203753241 79571969060193172652814931)
  ·
    refine ⟨119357953590289758979222397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79571969060193172652814931 119357953590289758979222397)
    ·
      refine ⟨44759232596358659617208399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119357953590289758979222397 44759232596358659617208399)
      ·
        refine ⟨67138848894537989425812599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44759232596358659617208399 67138848894537989425812599)
        ·
          refine ⟨100708273341806984138718899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67138848894537989425812599 100708273341806984138718899)
          ·
            refine ⟨151062410012710476208078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100708273341806984138718899 151062410012710476208078349)
            ·
              refine ⟨56648403754766428578029381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151062410012710476208078349 56648403754766428578029381)
              ·
                refine ⟨10621575704018705358380509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56648403754766428578029381 10621575704018705358380509)
                ·
                  refine ⟨3983090889007014509392691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10621575704018705358380509 3983090889007014509392691)
                  ·
                    refine ⟨5974636333510521764089037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983090889007014509392691 5974636333510521764089037)
                    ·
                      refine ⟨2240488625066445661533389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974636333510521764089037 2240488625066445661533389)
                      ·
                        rfl

theorem cell23_4363336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_4363336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363336 prefixEnd_4363336 := by exact prefixLift 4363336
  have htrace : WordTrace (prefixWord ++ tailWord_4363336) baseStart_4363336 baseEnd_4363336 := by
    simpa [prefixWord, tailWord_4363336, baseEnd_4363336] using wordTrace_append hprefix tailTrace_4363336
  have hstable : (prefixWord ++ tailWord_4363336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363336).length < 2 ^ (prefixWord ++ tailWord_4363336).sum := by decide
  have hdescent : baseEnd_4363336 < baseStart_4363336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 7, 1, 1, 3]
def baseStart_4363353 : Nat := 118140960795 + 4363353 * 2 ^ 59
def prefixEnd_4363353 : Nat := 4983230072969 + 3 ^ 40 * 4363353 * 2
def baseEnd_4363353 : Nat := 2240497354237572095020811

theorem tailTrace_4363353 : CollatzResearch.WordTrace tailWord_4363353 prefixEnd_4363353 2240497354237572095020811 := by
  unfold tailWord_4363353
  simp only [CollatzResearch.WordTrace]
  refine ⟨159144558161324757208998713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106096372107549838139332475 159144558161324757208998713)
  ·
    refine ⟨119358418620993567906749035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159144558161324757208998713 119358418620993567906749035)
    ·
      refine ⟨179037627931490351860123553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119358418620993567906749035 179037627931490351860123553)
      ·
        refine ⟨134278220948617763895092665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179037627931490351860123553 134278220948617763895092665)
        ·
          refine ⟨100708665711463322921319499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134278220948617763895092665 100708665711463322921319499)
          ·
            refine ⟨151062998567194984381979249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100708665711463322921319499 151062998567194984381979249)
            ·
              refine ⟨113297248925396238286484437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151062998567194984381979249 113297248925396238286484437)
              ·
                refine ⟨2655404271688974334839479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113297248925396238286484437 2655404271688974334839479)
                ·
                  refine ⟨3983106407533461502259219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655404271688974334839479 3983106407533461502259219)
                  ·
                    refine ⟨5974659611300192253388829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983106407533461502259219 5974659611300192253388829)
                    ·
                      refine ⟨2240497354237572095020811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974659611300192253388829 2240497354237572095020811)
                      ·
                        rfl

theorem cell23_4363353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_4363353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363353 prefixEnd_4363353 := by exact prefixLift 4363353
  have htrace : WordTrace (prefixWord ++ tailWord_4363353) baseStart_4363353 baseEnd_4363353 := by
    simpa [prefixWord, tailWord_4363353, baseEnd_4363353] using wordTrace_append hprefix tailTrace_4363353
  have hstable : (prefixWord ++ tailWord_4363353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363353).length < 2 ^ (prefixWord ++ tailWord_4363353).sum := by decide
  have hdescent : baseEnd_4363353 < baseStart_4363353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363356 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4363356 : Nat := 118140960795 + 4363356 * 2 ^ 59
def prefixEnd_4363356 : Nat := 4983230072969 + 3 ^ 40 * 4363356 * 2
def baseEnd_4363356 : Nat := 746832964893178527761099

theorem tailTrace_4363356 : CollatzResearch.WordTrace tailWord_4363356 prefixEnd_4363356 746832964893178527761099 := by
  unfold tailWord_4363356
  simp only [CollatzResearch.WordTrace]
  refine ⟨79572333790156944360678961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106096445053542592480905281 79572333790156944360678961)
  ·
    refine ⟨59679250342617708270509221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79572333790156944360678961 59679250342617708270509221)
    ·
      refine ⟨11189859439240820300720479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59679250342617708270509221 11189859439240820300720479)
      ·
        refine ⟨16784789158861230451080719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11189859439240820300720479 16784789158861230451080719)
        ·
          refine ⟨25177183738291845676621079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16784789158861230451080719 25177183738291845676621079)
          ·
            refine ⟨37765775607437768514931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25177183738291845676621079 37765775607437768514931619)
            ·
              refine ⟨56648663411156652772397429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37765775607437768514931619 56648663411156652772397429)
              ·
                refine ⟨5310812194795936197412259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56648663411156652772397429 5310812194795936197412259)
                ·
                  refine ⟨7966218292193904296118389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310812194795936197412259 7966218292193904296118389)
                  ·
                    refine ⟨746832964893178527761099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7966218292193904296118389 746832964893178527761099)
                    ·
                      rfl

theorem cell23_4363356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4363356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363356 prefixEnd_4363356 := by exact prefixLift 4363356
  have htrace : WordTrace (prefixWord ++ tailWord_4363356) baseStart_4363356 baseEnd_4363356 := by
    simpa [prefixWord, tailWord_4363356, baseEnd_4363356] using wordTrace_append hprefix tailTrace_4363356
  have hstable : (prefixWord ++ tailWord_4363356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363356).length < 2 ^ (prefixWord ++ tailWord_4363356).sum := by decide
  have hdescent : baseEnd_4363356 < baseStart_4363356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363370 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4363370 : Nat := 118140960795 + 4363370 * 2 ^ 59
def prefixEnd_4363370 : Nat := 4983230072969 + 3 ^ 40 * 4363370 * 2
def baseEnd_4363370 : Nat := 2240506083408698528508233

theorem tailTrace_4363370 : CollatzResearch.WordTrace tailWord_4363370 prefixEnd_4363370 2240506083408698528508233 := by
  unfold tailWord_4363370
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786294550565792278091891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106096785468175446074911709 39786294550565792278091891)
  ·
    refine ⟨59679441825848688417137837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39786294550565792278091891 59679441825848688417137837)
    ·
      refine ⟨22379790684693258156426689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59679441825848688417137837 22379790684693258156426689)
      ·
        refine ⟨16784843013519943617320017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22379790684693258156426689 16784843013519943617320017)
        ·
          refine ⟨12588632260139957712990013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16784843013519943617320017 12588632260139957712990013)
          ·
            refine ⟨4720737097552484142371255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12588632260139957712990013 4720737097552484142371255)
            ·
              refine ⟨7081105646328726213556883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720737097552484142371255 7081105646328726213556883)
              ·
                refine ⟨10621658469493089320335325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081105646328726213556883 10621658469493089320335325)
                ·
                  refine ⟨3983121926059908495125747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10621658469493089320335325 3983121926059908495125747)
                  ·
                    refine ⟨5974682889089862742688621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983121926059908495125747 5974682889089862742688621)
                    ·
                      refine ⟨2240506083408698528508233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974682889089862742688621 2240506083408698528508233)
                      ·
                        rfl

theorem cell23_4363370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4363370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363370 prefixEnd_4363370 := by exact prefixLift 4363370
  have htrace : WordTrace (prefixWord ++ tailWord_4363370) baseStart_4363370 baseEnd_4363370 := by
    simpa [prefixWord, tailWord_4363370, baseEnd_4363370] using wordTrace_append hprefix tailTrace_4363370
  have hstable : (prefixWord ++ tailWord_4363370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363370).length < 2 ^ (prefixWord ++ tailWord_4363370).sum := by decide
  have hdescent : baseEnd_4363370 < baseStart_4363370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363389 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_4363389 : Nat := 118140960795 + 4363389 * 2 ^ 59
def prefixEnd_4363389 : Nat := 4983230072969 + 3 ^ 40 * 4363389 * 2
def baseEnd_4363389 : Nat := 2240515839541133954170645

theorem tailTrace_4363389 : CollatzResearch.WordTrace tailWord_4363389 prefixEnd_4363389 2240515839541133954170645 := by
  unfold tailWord_4363389
  simp only [CollatzResearch.WordTrace]
  refine ⟨159145871189194335357309221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106097247459462890238206147 159145871189194335357309221)
  ·
    refine ⟨29839850847973937879495479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159145871189194335357309221 29839850847973937879495479)
    ·
      refine ⟨44759776271960906819243219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29839850847973937879495479 44759776271960906819243219)
      ·
        refine ⟨67139664407941360228864829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44759776271960906819243219 67139664407941360228864829)
        ·
          refine ⟨25177374152978010085824311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67139664407941360228864829 25177374152978010085824311)
          ·
            refine ⟨37766061229467015128736467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25177374152978010085824311 37766061229467015128736467)
            ·
              refine ⟨56649091844200522693104701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37766061229467015128736467 56649091844200522693104701)
              ·
                refine ⟨21243409441575196009914263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56649091844200522693104701 21243409441575196009914263)
                ·
                  refine ⟨31865114162362794014871395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21243409441575196009914263 31865114162362794014871395)
                  ·
                    refine ⟨47797671243544191022307093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31865114162362794014871395 47797671243544191022307093)
                    ·
                      refine ⟨2240515839541133954170645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47797671243544191022307093 2240515839541133954170645)
                      ·
                        rfl

theorem cell23_4363389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_4363389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363389 prefixEnd_4363389 := by exact prefixLift 4363389
  have htrace : WordTrace (prefixWord ++ tailWord_4363389) baseStart_4363389 baseEnd_4363389 := by
    simpa [prefixWord, tailWord_4363389, baseEnd_4363389] using wordTrace_append hprefix tailTrace_4363389
  have hstable : (prefixWord ++ tailWord_4363389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363389).length < 2 ^ (prefixWord ++ tailWord_4363389).sum := by decide
  have hdescent : baseEnd_4363389 < baseStart_4363389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363393 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_4363393 : Nat := 118140960795 + 4363393 * 2 ^ 59
def prefixEnd_4363393 : Nat := 4983230072969 + 3 ^ 40 * 4363393 * 2
def baseEnd_4363393 : Nat := 2240517893463751938520627

theorem tailTrace_4363393 : CollatzResearch.WordTrace tailWord_4363393 prefixEnd_4363393 2240517893463751938520627 := by
  unfold tailWord_4363393
  simp only [CollatzResearch.WordTrace]
  refine ⟨159146017081179844040454833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106097344720786562693636555 159146017081179844040454833)
  ·
    refine ⟨119359512810884883030341125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159146017081179844040454833 119359512810884883030341125)
    ·
      refine ⟨22379908652040915568188961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119359512810884883030341125 22379908652040915568188961)
      ·
        refine ⟨16784931489030686676141721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22379908652040915568188961 16784931489030686676141721)
        ·
          refine ⟨12588698616773015007106291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16784931489030686676141721 12588698616773015007106291)
          ·
            refine ⟨18883047925159522510659437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12588698616773015007106291 18883047925159522510659437)
            ·
              refine ⟨7081142971934820941497289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18883047925159522510659437 7081142971934820941497289)
              ·
                refine ⟨5310857228951115706122967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081142971934820941497289 5310857228951115706122967)
                ·
                  refine ⟨7966285843426673559184451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310857228951115706122967 7966285843426673559184451)
                  ·
                    refine ⟨11949428765140010338776677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7966285843426673559184451 11949428765140010338776677)
                    ·
                      refine ⟨2240517893463751938520627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11949428765140010338776677 2240517893463751938520627)
                      ·
                        rfl

theorem cell23_4363393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_4363393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363393 prefixEnd_4363393 := by exact prefixLift 4363393
  have htrace : WordTrace (prefixWord ++ tailWord_4363393) baseStart_4363393 baseEnd_4363393 := by
    simpa [prefixWord, tailWord_4363393, baseEnd_4363393] using wordTrace_append hprefix tailTrace_4363393
  have hstable : (prefixWord ++ tailWord_4363393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363393).length < 2 ^ (prefixWord ++ tailWord_4363393).sum := by decide
  have hdescent : baseEnd_4363393 < baseStart_4363393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363406 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4363406 : Nat := 118140960795 + 4363406 * 2 ^ 59
def prefixEnd_4363406 : Nat := 4983230072969 + 3 ^ 40 * 4363406 * 2
def baseEnd_4363406 : Nat := 2240524568712260387658067

theorem tailTrace_4363406 : CollatzResearch.WordTrace tailWord_4363406 prefixEnd_4363406 2240524568712260387658067 := by
  unfold tailWord_4363406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893311403766593407584759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106097660820088498173785381 19893311403766593407584759)
  ·
    refine ⟨29839967105649890111377139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19893311403766593407584759 29839967105649890111377139)
    ·
      refine ⟨44759950658474835167065709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29839967105649890111377139 44759950658474835167065709)
      ·
        refine ⟨16784981496928063187649641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44759950658474835167065709 16784981496928063187649641)
        ·
          refine ⟨12588736122696047390737231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16784981496928063187649641 12588736122696047390737231)
          ·
            refine ⟨18883104184044071086105847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12588736122696047390737231 18883104184044071086105847)
            ·
              refine ⟨28324656276066106629158771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18883104184044071086105847 28324656276066106629158771)
              ·
                refine ⟨42486984414099159943738157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28324656276066106629158771 42486984414099159943738157)
                ·
                  refine ⟨15932619155287184978901809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42486984414099159943738157 15932619155287184978901809)
                  ·
                    refine ⟨11949464366465388734176357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15932619155287184978901809 11949464366465388734176357)
                    ·
                      refine ⟨2240524568712260387658067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11949464366465388734176357 2240524568712260387658067)
                      ·
                        rfl

theorem cell23_4363406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4363406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363406 prefixEnd_4363406 := by exact prefixLift 4363406
  have htrace : WordTrace (prefixWord ++ tailWord_4363406) baseStart_4363406 baseEnd_4363406 := by
    simpa [prefixWord, tailWord_4363406, baseEnd_4363406] using wordTrace_append hprefix tailTrace_4363406
  have hstable : (prefixWord ++ tailWord_4363406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363406).length < 2 ^ (prefixWord ++ tailWord_4363406).sum := by decide
  have hdescent : baseEnd_4363406 < baseStart_4363406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363410 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_4363410 : Nat := 118140960795 + 4363410 * 2 ^ 59
def prefixEnd_4363410 : Nat := 4983230072969 + 3 ^ 40 * 4363410 * 2
def baseEnd_4363410 : Nat := 2240526622634878372008049

theorem tailTrace_4363410 : CollatzResearch.WordTrace tailWord_4363410 prefixEnd_4363410 2240526622634878372008049 := by
  unfold tailWord_4363410
  simp only [CollatzResearch.WordTrace]
  refine ⟨39786659280529563985955921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106097758081412170629215789 39786659280529563985955921)
  ·
    refine ⟨29839994460397172989466941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39786659280529563985955921 29839994460397172989466941)
    ·
      refine ⟨11189997922648939871050103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29839994460397172989466941 11189997922648939871050103)
      ·
        refine ⟨16784996883973409806575155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11189997922648939871050103 16784996883973409806575155)
        ·
          refine ⟨25177495325960114709862733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16784996883973409806575155 25177495325960114709862733)
          ·
            refine ⟨9441560747235043016198525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25177495325960114709862733 9441560747235043016198525)
            ·
              refine ⟨3540585280213141131074447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9441560747235043016198525 3540585280213141131074447)
              ·
                refine ⟨5310877920319711696611671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540585280213141131074447 5310877920319711696611671)
                ·
                  refine ⟨7966316880479567544917507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5310877920319711696611671 7966316880479567544917507)
                  ·
                    refine ⟨11949475320719351317376261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7966316880479567544917507 11949475320719351317376261)
                    ·
                      refine ⟨2240526622634878372008049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11949475320719351317376261 2240526622634878372008049)
                      ·
                        rfl

theorem cell23_4363410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_4363410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363410 prefixEnd_4363410 := by exact prefixLift 4363410
  have htrace : WordTrace (prefixWord ++ tailWord_4363410) baseStart_4363410 baseEnd_4363410 := by
    simpa [prefixWord, tailWord_4363410, baseEnd_4363410] using wordTrace_append hprefix tailTrace_4363410
  have hstable : (prefixWord ++ tailWord_4363410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363410).length < 2 ^ (prefixWord ++ tailWord_4363410).sum := by decide
  have hdescent : baseEnd_4363410 < baseStart_4363410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363429 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_4363429 : Nat := 118140960795 + 4363429 * 2 ^ 59
def prefixEnd_4363429 : Nat := 4983230072969 + 3 ^ 40 * 4363429 * 2
def baseEnd_4363429 : Nat := 746845459589104599223487

theorem tailTrace_4363429 : CollatzResearch.WordTrace tailWord_4363429 prefixEnd_4363429 746845459589104599223487 := by
  unfold tailWord_4363429
  simp only [CollatzResearch.WordTrace]
  refine ⟨159147330109049422188765341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106098220072699614792510227 159147330109049422188765341)
  ·
    refine ⟨59680248790893533320787003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159147330109049422188765341 59680248790893533320787003)
    ·
      refine ⟨89520373186340299981180505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59680248790893533320787003 89520373186340299981180505)
      ·
        refine ⟨67140279889755224985885379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89520373186340299981180505 67140279889755224985885379)
        ·
          refine ⟨100710419834632837478828069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67140279889755224985885379 100710419834632837478828069)
          ·
            refine ⟨18883203718993657027280263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100710419834632837478828069 18883203718993657027280263)
            ·
              refine ⟨28324805578490485540920395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18883203718993657027280263 28324805578490485540920395)
              ·
                refine ⟨42487208367735728311380593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28324805578490485540920395 42487208367735728311380593)
                ·
                  refine ⟨31865406275801796233535445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42487208367735728311380593 31865406275801796233535445)
                  ·
                    refine ⟨746845459589104599223487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31865406275801796233535445 746845459589104599223487)
                    ·
                      rfl

theorem cell23_4363429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_4363429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363429 prefixEnd_4363429 := by exact prefixLift 4363429
  have htrace : WordTrace (prefixWord ++ tailWord_4363429) baseStart_4363429 baseEnd_4363429 := by
    simpa [prefixWord, tailWord_4363429, baseEnd_4363429] using wordTrace_append hprefix tailTrace_4363429
  have hstable : (prefixWord ++ tailWord_4363429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363429).length < 2 ^ (prefixWord ++ tailWord_4363429).sum := by decide
  have hdescent : baseEnd_4363429 < baseStart_4363429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363443 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 3]
def baseStart_4363443 : Nat := 118140960795 + 4363443 * 2 ^ 59
def prefixEnd_4363443 : Nat := 4983230072969 + 3 ^ 40 * 4363443 * 2
def baseEnd_4363443 : Nat := 2240543567496476742895397

theorem tailTrace_4363443 : CollatzResearch.WordTrace tailWord_4363443 prefixEnd_4363443 2240543567496476742895397 := by
  unfold tailWord_4363443
  simp only [CollatzResearch.WordTrace]
  refine ⟨159147840730998702579774983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106098560487332468386516655 159147840730998702579774983)
  ·
    refine ⟨238721761096498053869662475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159147840730998702579774983 238721761096498053869662475)
    ·
      refine ⟨358082641644747080804493713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238721761096498053869662475 358082641644747080804493713)
      ·
        refine ⟨268561981233560310603370285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358082641644747080804493713 268561981233560310603370285)
        ·
          refine ⟨100710742962585116476263857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268561981233560310603370285 100710742962585116476263857)
          ·
            refine ⟨75533057221938837357197893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100710742962585116476263857 75533057221938837357197893)
            ·
              refine ⟨14162448229113532004474605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75533057221938837357197893 14162448229113532004474605)
              ·
                refine ⟨5310918085917574501677977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14162448229113532004474605 5310918085917574501677977)
                ·
                  refine ⟨3983188564438180876258483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310918085917574501677977 3983188564438180876258483)
                  ·
                    refine ⟨5974782846657271314387725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983188564438180876258483 5974782846657271314387725)
                    ·
                      refine ⟨2240543567496476742895397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974782846657271314387725 2240543567496476742895397)
                      ·
                        rfl

theorem cell23_4363443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_4363443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363443 prefixEnd_4363443 := by exact prefixLift 4363443
  have htrace : WordTrace (prefixWord ++ tailWord_4363443) baseStart_4363443 baseEnd_4363443 := by
    simpa [prefixWord, tailWord_4363443, baseEnd_4363443] using wordTrace_append hprefix tailTrace_4363443
  have hstable : (prefixWord ++ tailWord_4363443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363443).length < 2 ^ (prefixWord ++ tailWord_4363443).sum := by decide
  have hdescent : baseEnd_4363443 < baseStart_4363443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363453 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_4363453 : Nat := 118140960795 + 4363453 * 2 ^ 59
def prefixEnd_4363453 : Nat := 4983230072969 + 3 ^ 40 * 4363453 * 2
def baseEnd_4363453 : Nat := 2240548702303021703770351

theorem tailTrace_4363453 : CollatzResearch.WordTrace tailWord_4363453 prefixEnd_4363453 2240548702303021703770351 := by
  unfold tailWord_4363453
  simp only [CollatzResearch.WordTrace]
  refine ⟨159148205460962474287639013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106098803640641649525092675 159148205460962474287639013)
  ·
    refine ⟨29840288523930463928932315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159148205460962474287639013 29840288523930463928932315)
    ·
      refine ⟨44760432785895695893398473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29840288523930463928932315 44760432785895695893398473)
      ·
        refine ⟨33570324589421771920048855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44760432785895695893398473 33570324589421771920048855)
        ·
          refine ⟨50355486884132657880073283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33570324589421771920048855 50355486884132657880073283)
          ·
            refine ⟨75533230326198986820109925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50355486884132657880073283 75533230326198986820109925)
            ·
              refine ⟨14162480686162310028770611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75533230326198986820109925 14162480686162310028770611)
              ·
                refine ⟨21243721029243465043155917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14162480686162310028770611 21243721029243465043155917)
                ·
                  refine ⟨7966395385966299391183469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21243721029243465043155917 7966395385966299391183469)
                  ·
                    refine ⟨2987398269737362271693801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7966395385966299391183469 2987398269737362271693801)
                    ·
                      refine ⟨2240548702303021703770351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987398269737362271693801 2240548702303021703770351)
                      ·
                        rfl

theorem cell23_4363453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_4363453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363453 prefixEnd_4363453 := by exact prefixLift 4363453
  have htrace : WordTrace (prefixWord ++ tailWord_4363453) baseStart_4363453 baseEnd_4363453 := by
    simpa [prefixWord, tailWord_4363453, baseEnd_4363453] using wordTrace_append hprefix tailTrace_4363453
  have hstable : (prefixWord ++ tailWord_4363453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363453).length < 2 ^ (prefixWord ++ tailWord_4363453).sum := by decide
  have hdescent : baseEnd_4363453 < baseStart_4363453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363477 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4363477 : Nat := 118140960795 + 4363477 * 2 ^ 59
def prefixEnd_4363477 : Nat := 4983230072969 + 3 ^ 40 * 4363477 * 2
def baseEnd_4363477 : Nat := 2240561025838729609870241

theorem tailTrace_4363477 : CollatzResearch.WordTrace tailWord_4363477 prefixEnd_4363477 2240561025838729609870241 := by
  unfold tailWord_4363477
  simp only [CollatzResearch.WordTrace]
  refine ⟨159149080812875526386512685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106099387208583684257675123 159149080812875526386512685)
  ·
    refine ⟨59680905304828322394942257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159149080812875526386512685 59680905304828322394942257)
    ·
      refine ⟨44760678978621241796206693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59680905304828322394942257 44760678978621241796206693)
      ·
        refine ⟨8392627308491482836788755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44760678978621241796206693 8392627308491482836788755)
        ·
          refine ⟨12588940962737224255183133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8392627308491482836788755 12588940962737224255183133)
          ·
            refine ⟨4720852861026459095693675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12588940962737224255183133 4720852861026459095693675)
            ·
              refine ⟨7081279291539688643540513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720852861026459095693675 7081279291539688643540513)
              ·
                refine ⟨5310959468654766482655385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081279291539688643540513 5310959468654766482655385)
                ·
                  refine ⟨3983219601491074861991539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5310959468654766482655385 3983219601491074861991539)
                  ·
                    refine ⟨5974829402236612292987309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983219601491074861991539 5974829402236612292987309)
                    ·
                      refine ⟨2240561025838729609870241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974829402236612292987309 2240561025838729609870241)
                      ·
                        rfl

theorem cell23_4363477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4363477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363477 prefixEnd_4363477 := by exact prefixLift 4363477
  have htrace : WordTrace (prefixWord ++ tailWord_4363477) baseStart_4363477 baseEnd_4363477 := by
    simpa [prefixWord, tailWord_4363477, baseEnd_4363477] using wordTrace_append hprefix tailTrace_4363477
  have hstable : (prefixWord ++ tailWord_4363477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363477).length < 2 ^ (prefixWord ++ tailWord_4363477).sum := by decide
  have hdescent : baseEnd_4363477 < baseStart_4363477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363496 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4363496 : Nat := 118140960795 + 4363496 * 2 ^ 59
def prefixEnd_4363496 : Nat := 4983230072969 + 3 ^ 40 * 4363496 * 2
def baseEnd_4363496 : Nat := 2240570781971165035532653

theorem tailTrace_4363496 : CollatzResearch.WordTrace tailWord_4363496 prefixEnd_4363496 2240570781971165035532653 := by
  unfold tailWord_4363496
  simp only [CollatzResearch.WordTrace]
  refine ⟨79574886899903346315727171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106099849199871128420969561 79574886899903346315727171)
  ·
    refine ⟨119362330349855019473590757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79574886899903346315727171 119362330349855019473590757)
    ·
      refine ⟨22380436940597816151298267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119362330349855019473590757 22380436940597816151298267)
      ·
        refine ⟨33570655410896724226947401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22380436940597816151298267 33570655410896724226947401)
        ·
          refine ⟨25177991558172543170210551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33570655410896724226947401 25177991558172543170210551)
          ·
            refine ⟨37766987337258814755315827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25177991558172543170210551 37766987337258814755315827)
            ·
              refine ⟨56650481005888222132973741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37766987337258814755315827 56650481005888222132973741)
              ·
                refine ⟨21243930377208083299865153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56650481005888222132973741 21243930377208083299865153)
                ·
                  refine ⟨15932947782906062474898865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21243930377208083299865153 15932947782906062474898865)
                  ·
                    refine ⟨11949710837179546856174149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15932947782906062474898865 11949710837179546856174149)
                    ·
                      refine ⟨2240570781971165035532653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11949710837179546856174149 2240570781971165035532653)
                      ·
                        rfl

theorem cell23_4363496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4363496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363496 prefixEnd_4363496 := by exact prefixLift 4363496
  have htrace : WordTrace (prefixWord ++ tailWord_4363496) baseStart_4363496 baseEnd_4363496 := by
    simpa [prefixWord, tailWord_4363496, baseEnd_4363496] using wordTrace_append hprefix tailTrace_4363496
  have hstable : (prefixWord ++ tailWord_4363496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363496).length < 2 ^ (prefixWord ++ tailWord_4363496).sum := by decide
  have hdescent : baseEnd_4363496 < baseStart_4363496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363500 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_4363500 : Nat := 118140960795 + 4363500 * 2 ^ 59
def prefixEnd_4363500 : Nat := 4983230072969 + 3 ^ 40 * 4363500 * 2
def baseEnd_4363500 : Nat := 2240572835893783019882635

theorem tailTrace_4363500 : CollatzResearch.WordTrace tailWord_4363500 prefixEnd_4363500 2240572835893783019882635 := by
  unfold tailWord_4363500
  simp only [CollatzResearch.WordTrace]
  refine ⟨79574959845896100657299977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106099946461194800876399969 79574959845896100657299977)
  ·
    refine ⟨59681219884422075492974983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79574959845896100657299977 59681219884422075492974983)
    ·
      refine ⟨89521829826633113239462475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59681219884422075492974983 89521829826633113239462475)
      ·
        refine ⟨134282744739949669859193713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89521829826633113239462475 134282744739949669859193713)
        ·
          refine ⟨100712058554962252394395285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134282744739949669859193713 100712058554962252394395285)
          ·
            refine ⟨4720877744763855580987279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100712058554962252394395285 4720877744763855580987279)
            ·
              refine ⟨7081316617145783371480919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720877744763855580987279 7081316617145783371480919)
              ·
                refine ⟨10621974925718675057221379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081316617145783371480919 10621974925718675057221379)
                ·
                  refine ⟨15932962388578012585832069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10621974925718675057221379 15932962388578012585832069)
                  ·
                    refine ⟨2987430447858377359843513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15932962388578012585832069 2987430447858377359843513)
                    ·
                      refine ⟨2240572835893783019882635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987430447858377359843513 2240572835893783019882635)
                      ·
                        rfl

theorem cell23_4363500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_4363500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363500 prefixEnd_4363500 := by exact prefixLift 4363500
  have htrace : WordTrace (prefixWord ++ tailWord_4363500) baseStart_4363500 baseEnd_4363500 := by
    simpa [prefixWord, tailWord_4363500, baseEnd_4363500] using wordTrace_append hprefix tailTrace_4363500
  have hstable : (prefixWord ++ tailWord_4363500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363500).length < 2 ^ (prefixWord ++ tailWord_4363500).sum := by decide
  have hdescent : baseEnd_4363500 < baseStart_4363500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363523 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 5]
def baseStart_4363523 : Nat := 118140960795 + 4363523 * 2 ^ 59
def prefixEnd_4363523 : Nat := 4983230072969 + 3 ^ 40 * 4363523 * 2
def baseEnd_4363523 : Nat := 248953849549870714432781

theorem tailTrace_4363523 : CollatzResearch.WordTrace tailWord_4363523 prefixEnd_4363523 248953849549870714432781 := by
  unfold tailWord_4363523
  simp only [CollatzResearch.WordTrace]
  refine ⟨159150758570708876242687223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106100505713805917495124815 159150758570708876242687223)
  ·
    refine ⟨238726137856063314364030835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159150758570708876242687223 238726137856063314364030835)
    ·
      refine ⟨358089206784094971546046253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238726137856063314364030835 358089206784094971546046253)
      ·
        refine ⟨134283452544035614329767345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358089206784094971546046253 134283452544035614329767345)
        ·
          refine ⟨100712589408026710747325509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134283452544035614329767345 100712589408026710747325509)
          ·
            refine ⟨18883610514005008265123533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100712589408026710747325509 18883610514005008265123533)
            ·
              refine ⟨7081353942751878099421325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18883610514005008265123533 7081353942751878099421325)
              ·
                refine ⟨2655507728531954287282997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7081353942751878099421325 2655507728531954287282997)
                ·
                  refine ⟨248953849549870714432781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2655507728531954287282997 248953849549870714432781)
                  ·
                    rfl

theorem cell23_4363523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 5].length) (baseStart_4363523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363523 prefixEnd_4363523 := by exact prefixLift 4363523
  have htrace : WordTrace (prefixWord ++ tailWord_4363523) baseStart_4363523 baseEnd_4363523 := by
    simpa [prefixWord, tailWord_4363523, baseEnd_4363523] using wordTrace_append hprefix tailTrace_4363523
  have hstable : (prefixWord ++ tailWord_4363523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363523).length < 2 ^ (prefixWord ++ tailWord_4363523).sum := by decide
  have hdescent : baseEnd_4363523 < baseStart_4363523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_4363539 : Nat := 118140960795 + 4363539 * 2 ^ 59
def prefixEnd_4363539 : Nat := 4983230072969 + 3 ^ 40 * 4363539 * 2
def baseEnd_4363539 : Nat := 2240592861639308367294955

theorem tailTrace_4363539 : CollatzResearch.WordTrace tailWord_4363539 prefixEnd_4363539 2240592861639308367294955 := by
  unfold tailWord_4363539
  simp only [CollatzResearch.WordTrace]
  refine ⟨159151342138650910975269671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106100894759100607316846447 159151342138650910975269671)
  ·
    refine ⟨238727013207976366462904507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159151342138650910975269671 238727013207976366462904507)
    ·
      refine ⟨358090519811964549694356761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238727013207976366462904507 358090519811964549694356761)
      ·
        refine ⟨268567889858973412270767571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358090519811964549694356761 268567889858973412270767571)
        ·
          refine ⟨402851834788460118406151357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268567889858973412270767571 402851834788460118406151357)
          ·
            refine ⟨151069438045672544402306759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402851834788460118406151357 151069438045672544402306759)
            ·
              refine ⟨226604157068508816603460139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151069438045672544402306759 226604157068508816603460139)
              ·
                refine ⟨339906235602763224905190209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226604157068508816603460139 339906235602763224905190209)
                ·
                  refine ⟨254929676702072418678892657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 339906235602763224905190209 254929676702072418678892657)
                  ·
                    refine ⟨191197257526554314009169493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254929676702072418678892657 191197257526554314009169493)
                    ·
                      refine ⟨2240592861639308367294955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191197257526554314009169493 2240592861639308367294955)
                      ·
                        rfl

theorem cell23_4363539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_4363539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363539 prefixEnd_4363539 := by exact prefixLift 4363539
  have htrace : WordTrace (prefixWord ++ tailWord_4363539) baseStart_4363539 baseEnd_4363539 := by
    simpa [prefixWord, tailWord_4363539, baseEnd_4363539] using wordTrace_append hprefix tailTrace_4363539
  have hstable : (prefixWord ++ tailWord_4363539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363539).length < 2 ^ (prefixWord ++ tailWord_4363539).sum := by decide
  have hdescent : baseEnd_4363539 < baseStart_4363539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363543 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4363543 : Nat := 118140960795 + 4363543 * 2 ^ 59
def prefixEnd_4363543 : Nat := 4983230072969 + 3 ^ 40 * 4363543 * 2
def baseEnd_4363543 : Nat := 2240594915561926351644937

theorem tailTrace_4363543 : CollatzResearch.WordTrace tailWord_4363543 prefixEnd_4363543 2240594915561926351644937 := by
  unfold tailWord_4363543
  simp only [CollatzResearch.WordTrace]
  refine ⟨159151488030636419658415283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106100992020424279772276855 159151488030636419658415283)
  ·
    refine ⟨238727232045954629487622925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159151488030636419658415283 238727232045954629487622925)
    ·
      refine ⟨89522712017232986057858597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238727232045954629487622925 89522712017232986057858597)
      ·
        refine ⟨16785508503231184885848487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89522712017232986057858597 16785508503231184885848487)
        ·
          refine ⟨25178262754846777328772731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16785508503231184885848487 25178262754846777328772731)
          ·
            refine ⟨37767394132270165993159097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25178262754846777328772731 37767394132270165993159097)
            ·
              refine ⟨28325545599202624494869323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37767394132270165993159097 28325545599202624494869323)
              ·
                refine ⟨42488318398803936742303985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28325545599202624494869323 42488318398803936742303985)
                ·
                  refine ⟨31866238799102952556727989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42488318398803936742303985 31866238799102952556727989)
                  ·
                    refine ⟨2987459887415901802193249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31866238799102952556727989 2987459887415901802193249)
                    ·
                      refine ⟨2240594915561926351644937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987459887415901802193249 2240594915561926351644937)
                      ·
                        rfl

theorem cell23_4363543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4363543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363543 prefixEnd_4363543 := by exact prefixLift 4363543
  have htrace : WordTrace (prefixWord ++ tailWord_4363543) baseStart_4363543 baseEnd_4363543 := by
    simpa [prefixWord, tailWord_4363543, baseEnd_4363543] using wordTrace_append hprefix tailTrace_4363543
  have hstable : (prefixWord ++ tailWord_4363543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363543).length < 2 ^ (prefixWord ++ tailWord_4363543).sum := by decide
  have hdescent : baseEnd_4363543 < baseStart_4363543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363546 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4363546 : Nat := 118140960795 + 4363546 * 2 ^ 59
def prefixEnd_4363546 : Nat := 4983230072969 + 3 ^ 40 * 4363546 * 2
def baseEnd_4363546 : Nat := 2240596456003889839907423

theorem tailTrace_4363546 : CollatzResearch.WordTrace tailWord_4363546 prefixEnd_4363546 2240596456003889839907423 := by
  unfold tailWord_4363546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39787899362406387792693623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106101064966417034113849661 39787899362406387792693623)
  ·
    refine ⟨59681849043609581689040435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39787899362406387792693623 59681849043609581689040435)
    ·
      refine ⟨89522773565414372533560653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59681849043609581689040435 89522773565414372533560653)
      ·
        refine ⟨33571040087030389700085245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89522773565414372533560653 33571040087030389700085245)
        ·
          refine ⟨12589140032636396137531967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33571040087030389700085245 12589140032636396137531967)
          ·
            refine ⟨18883710048954594206297951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12589140032636396137531967 18883710048954594206297951)
            ·
              refine ⟨28325565073431891309446927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18883710048954594206297951 28325565073431891309446927)
              ·
                refine ⟨42488347610147836964170391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28325565073431891309446927 42488347610147836964170391)
                ·
                  refine ⟨63732521415221755446255587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42488347610147836964170391 63732521415221755446255587)
                  ·
                    refine ⟨95598782122832633169383381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63732521415221755446255587 95598782122832633169383381)
                    ·
                      refine ⟨2240596456003889839907423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95598782122832633169383381 2240596456003889839907423)
                      ·
                        rfl

theorem cell23_4363546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4363546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363546 prefixEnd_4363546 := by exact prefixLift 4363546
  have htrace : WordTrace (prefixWord ++ tailWord_4363546) baseStart_4363546 baseEnd_4363546 := by
    simpa [prefixWord, tailWord_4363546, baseEnd_4363546] using wordTrace_append hprefix tailTrace_4363546
  have hstable : (prefixWord ++ tailWord_4363546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363546).length < 2 ^ (prefixWord ++ tailWord_4363546).sum := by decide
  have hdescent : baseEnd_4363546 < baseStart_4363546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363551 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 2, 2, 2]
def baseStart_4363551 : Nat := 118140960795 + 4363551 * 2 ^ 59
def prefixEnd_4363551 : Nat := 4983230072969 + 3 ^ 40 * 4363551 * 2
def baseEnd_4363551 : Nat := 2240599023407162320344901

theorem tailTrace_4363551 : CollatzResearch.WordTrace tailWord_4363551 prefixEnd_4363551 2240599023407162320344901 := by
  unfold tailWord_4363551
  simp only [CollatzResearch.WordTrace]
  refine ⟨159151779814607437024706507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106101186543071624683137671 159151779814607437024706507)
  ·
    refine ⟨238727669721911155537059761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159151779814607437024706507 238727669721911155537059761)
    ·
      refine ⟨179045752291433366652794821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238727669721911155537059761 179045752291433366652794821)
      ·
        refine ⟨33571078554643756247399029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179045752291433366652794821 33571078554643756247399029)
        ·
          refine ⟨3147288614497852148193659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33571078554643756247399029 3147288614497852148193659)
          ·
            refine ⟨4720932921746778222290489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147288614497852148193659 4720932921746778222290489)
            ·
              refine ⟨3540699691310083666717867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4720932921746778222290489 3540699691310083666717867)
              ·
                refine ⟨5311049536965125500076801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540699691310083666717867 5311049536965125500076801)
                ·
                  refine ⟨3983287152723844125057601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311049536965125500076801 3983287152723844125057601)
                  ·
                    refine ⟨2987465364542883093793201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983287152723844125057601 2987465364542883093793201)
                    ·
                      refine ⟨2240599023407162320344901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987465364542883093793201 2240599023407162320344901)
                      ·
                        rfl

theorem cell23_4363551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_4363551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363551 prefixEnd_4363551 := by exact prefixLift 4363551
  have htrace : WordTrace (prefixWord ++ tailWord_4363551) baseStart_4363551 baseEnd_4363551 := by
    simpa [prefixWord, tailWord_4363551, baseEnd_4363551] using wordTrace_append hprefix tailTrace_4363551
  have hstable : (prefixWord ++ tailWord_4363551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363551).length < 2 ^ (prefixWord ++ tailWord_4363551).sum := by decide
  have hdescent : baseEnd_4363551 < baseStart_4363551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363573 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4363573 : Nat := 118140960795 + 4363573 * 2 ^ 59
def prefixEnd_4363573 : Nat := 4983230072969 + 3 ^ 40 * 4363573 * 2
def baseEnd_4363573 : Nat := 2240610319981561234269799

theorem tailTrace_4363573 : CollatzResearch.WordTrace tailWord_4363573 prefixEnd_4363573 2240610319981561234269799 := by
  unfold tailWord_4363573
  simp only [CollatzResearch.WordTrace]
  refine ⟨159152582220527734782007373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106101721480351823188004915 159152582220527734782007373)
  ·
    refine ⟨59682218332697900543252765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159152582220527734782007373 59682218332697900543252765)
    ·
      refine ⟨22380831874761712703719787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59682218332697900543252765 22380831874761712703719787)
      ·
        refine ⟨33571247812142569055579681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22380831874761712703719787 33571247812142569055579681)
        ·
          refine ⟨25178435859106926791684761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33571247812142569055579681 25178435859106926791684761)
          ·
            refine ⟨18883826894330195093763571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25178435859106926791684761 18883826894330195093763571)
            ·
              refine ⟨28325740341495292640645357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18883826894330195093763571 28325740341495292640645357)
              ·
                refine ⟨10622152628060734740242009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28325740341495292640645357 10622152628060734740242009)
                ·
                  refine ⟨7966614471045551055181507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622152628060734740242009 7966614471045551055181507)
                  ·
                    refine ⟨11949921706568326582772261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7966614471045551055181507 11949921706568326582772261)
                    ·
                      refine ⟨2240610319981561234269799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11949921706568326582772261 2240610319981561234269799)
                      ·
                        rfl

theorem cell23_4363573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4363573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363573 prefixEnd_4363573 := by exact prefixLift 4363573
  have htrace : WordTrace (prefixWord ++ tailWord_4363573) baseStart_4363573 baseEnd_4363573 := by
    simpa [prefixWord, tailWord_4363573, baseEnd_4363573] using wordTrace_append hprefix tailTrace_4363573
  have hstable : (prefixWord ++ tailWord_4363573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363573).length < 2 ^ (prefixWord ++ tailWord_4363573).sum := by decide
  have hdescent : baseEnd_4363573 < baseStart_4363573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363593 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_4363593 : Nat := 118140960795 + 4363593 * 2 ^ 59
def prefixEnd_4363593 : Nat := 4983230072969 + 3 ^ 40 * 4363593 * 2
def baseEnd_4363593 : Nat := 2240620589594651156019707

theorem tailTrace_4363593 : CollatzResearch.WordTrace tailWord_4363593 prefixEnd_4363593 2240620589594651156019707 := by
  unfold tailWord_4363593
  simp only [CollatzResearch.WordTrace]
  refine ⟨159153311680455278197735433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106102207786970185465156955 159153311680455278197735433)
  ·
    refine ⟨119364983760341458648301575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159153311680455278197735433 119364983760341458648301575)
    ·
      refine ⟨179047475640512187972452363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119364983760341458648301575 179047475640512187972452363)
      ·
        refine ⟨268571213460768281958678545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179047475640512187972452363 268571213460768281958678545)
        ·
          refine ⟨201428410095576211469008909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268571213460768281958678545 201428410095576211469008909)
          ·
            refine ⟨75535653785841079300878341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201428410095576211469008909 75535653785841079300878341)
            ·
              refine ⟨14162935084845202368914689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75535653785841079300878341 14162935084845202368914689)
              ·
                refine ⟨10622201313633901776686017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14162935084845202368914689 10622201313633901776686017)
                ·
                  refine ⟨7966650985225426332514513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622201313633901776686017 7966650985225426332514513)
                  ·
                    refine ⟨5974988238919069749385885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7966650985225426332514513 5974988238919069749385885)
                    ·
                      refine ⟨2240620589594651156019707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5974988238919069749385885 2240620589594651156019707)
                      ·
                        rfl

theorem cell23_4363593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_4363593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363593 prefixEnd_4363593 := by exact prefixLift 4363593
  have htrace : WordTrace (prefixWord ++ tailWord_4363593) baseStart_4363593 baseEnd_4363593 := by
    simpa [prefixWord, tailWord_4363593, baseEnd_4363593] using wordTrace_append hprefix tailTrace_4363593
  have hstable : (prefixWord ++ tailWord_4363593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363593).length < 2 ^ (prefixWord ++ tailWord_4363593).sum := by decide
  have hdescent : baseEnd_4363593 < baseStart_4363593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363600 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 1, 4]
def baseStart_4363600 : Nat := 118140960795 + 4363600 * 2 ^ 59
def prefixEnd_4363600 : Nat := 4983230072969 + 3 ^ 40 * 4363600 * 2
def baseEnd_4363600 : Nat := 746874727986410876210725

theorem tailTrace_4363600 : CollatzResearch.WordTrace tailWord_4363600 prefixEnd_4363600 746874727986410876210725 := by
  unfold tailWord_4363600
  simp only [CollatzResearch.WordTrace]
  refine ⟨79576783495714959196620127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106102377994286612262160169 79576783495714959196620127)
  ·
    refine ⟨119365175243572438794930191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79576783495714959196620127 119365175243572438794930191)
    ·
      refine ⟨179047762865358658192395287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119365175243572438794930191 179047762865358658192395287)
      ·
        refine ⟨268571644298037987288592931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179047762865358658192395287 268571644298037987288592931)
        ·
          refine ⟨402857466447056980932889397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268571644298037987288592931 402857466447056980932889397)
          ·
            refine ⟨37767887479411591962458381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 402857466447056980932889397 37767887479411591962458381)
            ·
              refine ⟨14162957804779346985921893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37767887479411591962458381 14162957804779346985921893)
              ·
                refine ⟨2655554588396127559860355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14162957804779346985921893 2655554588396127559860355)
                ·
                  refine ⟨3983331882594191339790533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655554588396127559860355 3983331882594191339790533)
                  ·
                    refine ⟨746874727986410876210725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983331882594191339790533 746874727986410876210725)
                    ·
                      rfl

theorem cell23_4363600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 4].length) (baseStart_4363600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363600 prefixEnd_4363600 := by exact prefixLift 4363600
  have htrace : WordTrace (prefixWord ++ tailWord_4363600) baseStart_4363600 baseEnd_4363600 := by
    simpa [prefixWord, tailWord_4363600, baseEnd_4363600] using wordTrace_append hprefix tailTrace_4363600
  have hstable : (prefixWord ++ tailWord_4363600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363600).length < 2 ^ (prefixWord ++ tailWord_4363600).sum := by decide
  have hdescent : baseEnd_4363600 < baseStart_4363600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363643 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 1, 5]
def baseStart_4363643 : Nat := 118140960795 + 4363643 * 2 ^ 59
def prefixEnd_4363643 : Nat := 4983230072969 + 3 ^ 40 * 4363643 * 2
def baseEnd_4363643 : Nat := 746882087875791986798159

theorem tailTrace_4363643 : CollatzResearch.WordTrace tailWord_4363643 prefixEnd_4363643 746882087875791986798159 := by
  unfold tailWord_4363643
  simp only [CollatzResearch.WordTrace]
  refine ⟨159155135330274136737055583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106103423553516091158037055 159155135330274136737055583)
  ·
    refine ⟨238732702995411205105583375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159155135330274136737055583 238732702995411205105583375)
    ·
      refine ⟨358099054493116807658375063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238732702995411205105583375 358099054493116807658375063)
      ·
        refine ⟨537148581739675211487562595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358099054493116807658375063 537148581739675211487562595)
        ·
          refine ⟨805722872609512817231343893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537148581739675211487562595 805722872609512817231343893)
          ·
            refine ⟨37768259653570913307719245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 805722872609512817231343893 37768259653570913307719245)
            ·
              refine ⟨14163097370089092490394717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37768259653570913307719245 14163097370089092490394717)
              ·
                refine ⟨5311161513783409683898019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14163097370089092490394717 5311161513783409683898019)
                ·
                  refine ⟨7966742270675114525847029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311161513783409683898019 7966742270675114525847029)
                  ·
                    refine ⟨746882087875791986798159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7966742270675114525847029 746882087875791986798159)
                    ·
                      rfl

theorem cell23_4363643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 5].length) (baseStart_4363643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363643 prefixEnd_4363643 := by exact prefixLift 4363643
  have htrace : WordTrace (prefixWord ++ tailWord_4363643) baseStart_4363643 baseEnd_4363643 := by
    simpa [prefixWord, tailWord_4363643, baseEnd_4363643] using wordTrace_append hprefix tailTrace_4363643
  have hstable : (prefixWord ++ tailWord_4363643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363643).length < 2 ^ (prefixWord ++ tailWord_4363643).sum := by decide
  have hdescent : baseEnd_4363643 < baseStart_4363643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363650 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4363650 : Nat := 118140960795 + 4363650 * 2 ^ 59
def prefixEnd_4363650 : Nat := 4983230072969 + 3 ^ 40 * 4363650 * 2
def baseEnd_4363650 : Nat := 2240649857991957433006945

theorem tailTrace_4363650 : CollatzResearch.WordTrace tailWord_4363650 prefixEnd_4363650 2240649857991957433006945 := by
  unfold tailWord_4363650
  simp only [CollatzResearch.WordTrace]
  refine ⟨39788847660312194233140101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106103593760832517955040269 39788847660312194233140101)
  ·
    refine ⟨7460408936308536418713769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39788847660312194233140101 7460408936308536418713769)
    ·
      refine ⟨5595306702231402314035327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7460408936308536418713769 5595306702231402314035327)
      ·
        refine ⟨8392960053347103471052991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595306702231402314035327 8392960053347103471052991)
        ·
          refine ⟨12589440080020655206579487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8392960053347103471052991 12589440080020655206579487)
          ·
            refine ⟨18884160120030982809869231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12589440080020655206579487 18884160120030982809869231)
            ·
              refine ⟨28326240180046474214803847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18884160120030982809869231 28326240180046474214803847)
              ·
                refine ⟨42489360270069711322205771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28326240180046474214803847 42489360270069711322205771)
                ·
                  refine ⟨63734040405104566983308657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42489360270069711322205771 63734040405104566983308657)
                  ·
                    refine ⟨47800530303828425237481493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63734040405104566983308657 47800530303828425237481493)
                    ·
                      refine ⟨2240649857991957433006945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47800530303828425237481493 2240649857991957433006945)
                      ·
                        rfl

theorem cell23_4363650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4363650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363650 prefixEnd_4363650 := by exact prefixLift 4363650
  have htrace : WordTrace (prefixWord ++ tailWord_4363650) baseStart_4363650 baseEnd_4363650 := by
    simpa [prefixWord, tailWord_4363650, baseEnd_4363650] using wordTrace_append hprefix tailTrace_4363650
  have hstable : (prefixWord ++ tailWord_4363650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363650).length < 2 ^ (prefixWord ++ tailWord_4363650).sum := by decide
  have hdescent : baseEnd_4363650 < baseStart_4363650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363657 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_4363657 : Nat := 118140960795 + 4363657 * 2 ^ 59
def prefixEnd_4363657 : Nat := 4983230072969 + 3 ^ 40 * 4363657 * 2
def baseEnd_4363657 : Nat := 2240653452356538905619413

theorem tailTrace_4363657 : CollatzResearch.WordTrace tailWord_4363657 prefixEnd_4363657 2240653452356538905619413 := by
  unfold tailWord_4363657
  simp only [CollatzResearch.WordTrace]
  refine ⟨159155645952223417128065225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106103763968148944752043483 159155645952223417128065225)
  ·
    refine ⟨119366734464167562846048919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159155645952223417128065225 119366734464167562846048919)
    ·
      refine ⟨179050101696251344269073379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119366734464167562846048919 179050101696251344269073379)
      ·
        refine ⟨268575152544377016403610069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179050101696251344269073379 268575152544377016403610069)
        ·
          refine ⟨6294730137758836321959611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 268575152544377016403610069 6294730137758836321959611)
          ·
            refine ⟨9442095206638254482939417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294730137758836321959611 9442095206638254482939417)
            ·
              refine ⟨7081571404978690862204563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442095206638254482939417 7081571404978690862204563)
              ·
                refine ⟨10622357107468036293306845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081571404978690862204563 10622357107468036293306845)
                ·
                  refine ⟨3983383915300513609990067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10622357107468036293306845 3983383915300513609990067)
                  ·
                    refine ⟨5975075872950770414985101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983383915300513609990067 5975075872950770414985101)
                    ·
                      refine ⟨2240653452356538905619413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975075872950770414985101 2240653452356538905619413)
                      ·
                        rfl

theorem cell23_4363657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_4363657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363657 prefixEnd_4363657 := by exact prefixLift 4363657
  have htrace : WordTrace (prefixWord ++ tailWord_4363657) baseStart_4363657 baseEnd_4363657 := by
    simpa [prefixWord, tailWord_4363657, baseEnd_4363657] using wordTrace_append hprefix tailTrace_4363657
  have hstable : (prefixWord ++ tailWord_4363657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363657).length < 2 ^ (prefixWord ++ tailWord_4363657).sum := by decide
  have hdescent : baseEnd_4363657 < baseStart_4363657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363673 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_4363673 : Nat := 118140960795 + 4363673 * 2 ^ 59
def prefixEnd_4363673 : Nat := 4983230072969 + 3 ^ 40 * 4363673 * 2
def baseEnd_4363673 : Nat := 746887222682336947673113

theorem tailTrace_4363673 : CollatzResearch.WordTrace tailWord_4363673 prefixEnd_4363673 746887222682336947673113 := by
  unfold tailWord_4363673
  simp only [CollatzResearch.WordTrace]
  refine ⟨159156229520165451860647673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106104153013443634573765115 159156229520165451860647673)
  ·
    refine ⟨119367172140124088895485755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159156229520165451860647673 119367172140124088895485755)
    ·
      refine ⟨179050758210186133343228633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119367172140124088895485755 179050758210186133343228633)
      ·
        refine ⟨134288068657639600007421475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179050758210186133343228633 134288068657639600007421475)
        ·
          refine ⟨201432102986459400011132213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134288068657639600007421475 201432102986459400011132213)
          ·
            refine ⟨18884259654980568751043645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201432102986459400011132213 18884259654980568751043645)
            ·
              refine ⟨7081597370617713281641367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18884259654980568751043645 7081597370617713281641367)
              ·
                refine ⟨10622396055926569922462051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081597370617713281641367 10622396055926569922462051)
                ·
                  refine ⟨15933594083889854883693077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10622396055926569922462051 15933594083889854883693077)
                  ·
                    refine ⟨746887222682336947673113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15933594083889854883693077 746887222682336947673113)
                    ·
                      rfl

theorem cell23_4363673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_4363673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363673 prefixEnd_4363673 := by exact prefixLift 4363673
  have htrace : WordTrace (prefixWord ++ tailWord_4363673) baseStart_4363673 baseEnd_4363673 := by
    simpa [prefixWord, tailWord_4363673, baseEnd_4363673] using wordTrace_append hprefix tailTrace_4363673
  have hstable : (prefixWord ++ tailWord_4363673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363673).length < 2 ^ (prefixWord ++ tailWord_4363673).sum := by decide
  have hdescent : baseEnd_4363673 < baseStart_4363673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363680 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_4363680 : Nat := 118140960795 + 4363680 * 2 ^ 59
def prefixEnd_4363680 : Nat := 4983230072969 + 3 ^ 40 * 4363680 * 2
def baseEnd_4363680 : Nat := 2240665262411592315631807

theorem tailTrace_4363680 : CollatzResearch.WordTrace tailWord_4363680 prefixEnd_4363680 2240665262411592315631807 := by
  unfold tailWord_4363680
  simp only [CollatzResearch.WordTrace]
  refine ⟨79578242415570046028076247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106104323220760061370768329 79578242415570046028076247)
  ·
    refine ⟨119367363623355069042114371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79578242415570046028076247 119367363623355069042114371)
    ·
      refine ⟨179051045435032603563171557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119367363623355069042114371 179051045435032603563171557)
      ·
        refine ⟨33572071019068613168094667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179051045435032603563171557 33572071019068613168094667)
        ·
          refine ⟨50358106528602919752142001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33572071019068613168094667 50358106528602919752142001)
          ·
            refine ⟨37768579896452189814106501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50358106528602919752142001 37768579896452189814106501)
            ·
              refine ⟨7081608730584785590144969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37768579896452189814106501 7081608730584785590144969)
              ·
                refine ⟨5311206547938589192608727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081608730584785590144969 5311206547938589192608727)
                ·
                  refine ⟨7966809821907883788913091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311206547938589192608727 7966809821907883788913091)
                  ·
                    refine ⟨11950214732861825683369637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7966809821907883788913091 11950214732861825683369637)
                    ·
                      refine ⟨2240665262411592315631807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11950214732861825683369637 2240665262411592315631807)
                      ·
                        rfl

theorem cell23_4363680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_4363680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363680 prefixEnd_4363680 := by exact prefixLift 4363680
  have htrace : WordTrace (prefixWord ++ tailWord_4363680) baseStart_4363680 baseEnd_4363680 := by
    simpa [prefixWord, tailWord_4363680, baseEnd_4363680] using wordTrace_append hprefix tailTrace_4363680
  have hstable : (prefixWord ++ tailWord_4363680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363680).length < 2 ^ (prefixWord ++ tailWord_4363680).sum := by decide
  have hdescent : baseEnd_4363680 < baseStart_4363680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363724 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_4363724 : Nat := 118140960795 + 4363724 * 2 ^ 59
def prefixEnd_4363724 : Nat := 4983230072969 + 3 ^ 40 * 4363724 * 2
def baseEnd_4363724 : Nat := 746895951853463381160535

theorem tailTrace_4363724 : CollatzResearch.WordTrace tailWord_4363724 prefixEnd_4363724 746895951853463381160535 := by
  unfold tailWord_4363724
  simp only [CollatzResearch.WordTrace]
  refine ⟨79579044821490343785377113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106105393095320458380502817 79579044821490343785377113)
  ·
    refine ⟨59684283616117757839032835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79579044821490343785377113 59684283616117757839032835)
    ·
      refine ⟨89526425424176636758549253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59684283616117757839032835 89526425424176636758549253)
      ·
        refine ⟨16786204767033119392227985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89526425424176636758549253 16786204767033119392227985)
        ·
          refine ⟨12589653575274839544170989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786204767033119392227985 12589653575274839544170989)
          ·
            refine ⟨4721120090728064829064121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12589653575274839544170989 4721120090728064829064121)
            ·
              refine ⟨3540840068046048621798091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721120090728064829064121 3540840068046048621798091)
              ·
                refine ⟨5311260102069072932697137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540840068046048621798091 5311260102069072932697137)
                ·
                  refine ⟨3983445076551804699522853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311260102069072932697137 3983445076551804699522853)
                  ·
                    refine ⟨746895951853463381160535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983445076551804699522853 746895951853463381160535)
                    ·
                      rfl

theorem cell23_4363724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_4363724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363724 prefixEnd_4363724 := by exact prefixLift 4363724
  have htrace : WordTrace (prefixWord ++ tailWord_4363724) baseStart_4363724 baseEnd_4363724 := by
    simpa [prefixWord, tailWord_4363724, baseEnd_4363724] using wordTrace_append hprefix tailTrace_4363724
  have hstable : (prefixWord ++ tailWord_4363724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363724).length < 2 ^ (prefixWord ++ tailWord_4363724).sum := by decide
  have hdescent : baseEnd_4363724 < baseStart_4363724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363734 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4363734 : Nat := 118140960795 + 4363734 * 2 ^ 59
def prefixEnd_4363734 : Nat := 4983230072969 + 3 ^ 40 * 4363734 * 2
def baseEnd_4363734 : Nat := 2240692990366935104356559

theorem tailTrace_4363734 : CollatzResearch.WordTrace tailWord_4363734 prefixEnd_4363734 2240692990366935104356559 := by
  unfold tailWord_4363734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947403398309028704913641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106105636248629639519078837 9947403398309028704913641)
  ·
    refine ⟨7460552548731771528685231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9947403398309028704913641 7460552548731771528685231)
    ·
      refine ⟨11190828823097657293027847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460552548731771528685231 11190828823097657293027847)
      ·
        refine ⟨16786243234646485939541771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11190828823097657293027847 16786243234646485939541771)
        ·
          refine ⟨25179364851969728909312657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16786243234646485939541771 25179364851969728909312657)
          ·
            refine ⟨18884523638977296681984493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25179364851969728909312657 18884523638977296681984493)
            ·
              refine ⟨7081696364616486255744185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18884523638977296681984493 7081696364616486255744185)
              ·
                refine ⟨5311272273462364691808139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081696364616486255744185 5311272273462364691808139)
                ·
                  refine ⟨7966908410193547037712209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311272273462364691808139 7966908410193547037712209)
                  ·
                    refine ⟨5975181307645160278284157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7966908410193547037712209 5975181307645160278284157)
                    ·
                      refine ⟨2240692990366935104356559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975181307645160278284157 2240692990366935104356559)
                      ·
                        rfl

theorem cell23_4363734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4363734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363734 prefixEnd_4363734 := by exact prefixLift 4363734
  have htrace : WordTrace (prefixWord ++ tailWord_4363734) baseStart_4363734 baseEnd_4363734 := by
    simpa [prefixWord, tailWord_4363734, baseEnd_4363734] using wordTrace_append hprefix tailTrace_4363734
  have hstable : (prefixWord ++ tailWord_4363734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363734).length < 2 ^ (prefixWord ++ tailWord_4363734).sum := by decide
  have hdescent : baseEnd_4363734 < baseStart_4363734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363765 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4363765 : Nat := 118140960795 + 4363765 * 2 ^ 59
def prefixEnd_4363765 : Nat := 4983230072969 + 3 ^ 40 * 4363765 * 2
def baseEnd_4363765 : Nat := 2240708908267224483068917

theorem tailTrace_4363765 : CollatzResearch.WordTrace tailWord_4363765 prefixEnd_4363765 2240708908267224483068917 := by
  unfold tailWord_4363765
  simp only [CollatzResearch.WordTrace]
  refine ⟨159159585035832151572996749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106106390023888101048664499 159159585035832151572996749)
  ·
    refine ⟨59684844388437056839873781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159159585035832151572996749 59684844388437056839873781)
    ·
      refine ⟨5595454161415974078738167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59684844388437056839873781 5595454161415974078738167)
      ·
        refine ⟨8393181242123961118107251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595454161415974078738167 8393181242123961118107251)
        ·
          refine ⟨12589771863185941677160877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8393181242123961118107251 12589771863185941677160877)
          ·
            refine ⟨4721164448694728128935329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12589771863185941677160877 4721164448694728128935329)
            ·
              refine ⟨3540873336521046096701497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721164448694728128935329 3540873336521046096701497)
              ·
                refine ⟨2655655002390784572526123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3540873336521046096701497 2655655002390784572526123)
                ·
                  refine ⟨3983482503586176858789185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655655002390784572526123 3983482503586176858789185)
                  ·
                    refine ⟨2987611877689632644091889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983482503586176858789185 2987611877689632644091889)
                    ·
                      refine ⟨2240708908267224483068917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987611877689632644091889 2240708908267224483068917)
                      ·
                        rfl

theorem cell23_4363765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4363765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363765 prefixEnd_4363765 := by exact prefixLift 4363765
  have htrace : WordTrace (prefixWord ++ tailWord_4363765) baseStart_4363765 baseEnd_4363765 := by
    simpa [prefixWord, tailWord_4363765, baseEnd_4363765] using wordTrace_append hprefix tailTrace_4363765
  have hstable : (prefixWord ++ tailWord_4363765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363765).length < 2 ^ (prefixWord ++ tailWord_4363765).sum := by decide
  have hdescent : baseEnd_4363765 < baseStart_4363765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363770 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_4363770 : Nat := 118140960795 + 4363770 * 2 ^ 59
def prefixEnd_4363770 : Nat := 4983230072969 + 3 ^ 40 * 4363770 * 2
def baseEnd_4363770 : Nat := 2240711475670496963506393

theorem tailTrace_4363770 : CollatzResearch.WordTrace tailWord_4363770 prefixEnd_4363770 2240711475670496963506393 := by
  unfold tailWord_4363770
  simp only [CollatzResearch.WordTrace]
  refine ⟨39789941850203509356732191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106106511600542691617952509 39789941850203509356732191)
  ·
    refine ⟨59684912775305264035098287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39789941850203509356732191 59684912775305264035098287)
    ·
      refine ⟨89527369162957896052647431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59684912775305264035098287 89527369162957896052647431)
      ·
        refine ⟨134291053744436844078971147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89527369162957896052647431 134291053744436844078971147)
        ·
          refine ⟨201436580616655266118456721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134291053744436844078971147 201436580616655266118456721)
          ·
            refine ⟨151077435462491449588842541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201436580616655266118456721 151077435462491449588842541)
            ·
              refine ⟨56654038298434293595815953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151077435462491449588842541 56654038298434293595815953)
              ·
                refine ⟨42490528723825720196861965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56654038298434293595815953 42490528723825720196861965)
                ·
                  refine ⟨15933948271434645073823237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42490528723825720196861965 15933948271434645073823237)
                  ·
                    refine ⟨2987615300893995951341857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15933948271434645073823237 2987615300893995951341857)
                    ·
                      refine ⟨2240711475670496963506393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2987615300893995951341857 2240711475670496963506393)
                      ·
                        rfl

theorem cell23_4363770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_4363770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363770 prefixEnd_4363770 := by exact prefixLift 4363770
  have htrace : WordTrace (prefixWord ++ tailWord_4363770) baseStart_4363770 baseEnd_4363770 := by
    simpa [prefixWord, tailWord_4363770, baseEnd_4363770] using wordTrace_append hprefix tailTrace_4363770
  have hstable : (prefixWord ++ tailWord_4363770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363770).length < 2 ^ (prefixWord ++ tailWord_4363770).sum := by decide
  have hdescent : baseEnd_4363770 < baseStart_4363770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363793 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 7]
def baseStart_4363793 : Nat := 118140960795 + 4363793 * 2 ^ 59
def prefixEnd_4363793 : Nat := 4983230072969 + 3 ^ 40 * 4363793 * 2
def baseEnd_4363793 : Nat := 248969253969505597057643

theorem tailTrace_4363793 : CollatzResearch.WordTrace tailWord_4363793 prefixEnd_4363793 248969253969505597057643 := by
  unfold tailWord_4363793
  simp only [CollatzResearch.WordTrace]
  refine ⟨159160606279730712355016033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106107070853153808236677355 159160606279730712355016033)
  ·
    refine ⟨119370454709798034266262025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159160606279730712355016033 119370454709798034266262025)
    ·
      refine ⟨89527841032348525699696519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119370454709798034266262025 89527841032348525699696519)
      ·
        refine ⟨134291761548522788549544779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89527841032348525699696519 134291761548522788549544779)
        ·
          refine ⟨201437642322784182824317169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134291761548522788549544779 201437642322784182824317169)
          ·
            refine ⟨151078231742088137118237877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201437642322784182824317169 151078231742088137118237877)
            ·
              refine ⟨14163584225820762854834801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151078231742088137118237877 14163584225820762854834801)
              ·
                refine ⟨10622688169365572141126101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14163584225820762854834801 10622688169365572141126101)
                ·
                  refine ⟨248969253969505597057643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10622688169365572141126101 248969253969505597057643)
                  ·
                    rfl

theorem cell23_4363793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_4363793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363793 prefixEnd_4363793 := by exact prefixLift 4363793
  have htrace : WordTrace (prefixWord ++ tailWord_4363793) baseStart_4363793 baseEnd_4363793 := by
    simpa [prefixWord, tailWord_4363793, baseEnd_4363793] using wordTrace_append hprefix tailTrace_4363793
  have hstable : (prefixWord ++ tailWord_4363793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363793).length < 2 ^ (prefixWord ++ tailWord_4363793).sum := by decide
  have hdescent : baseEnd_4363793 < baseStart_4363793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363860 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4363860 : Nat := 118140960795 + 4363860 * 2 ^ 59
def prefixEnd_4363860 : Nat := 4983230072969 + 3 ^ 40 * 4363860 * 2
def baseEnd_4363860 : Nat := 2240757688929401611380979

theorem tailTrace_4363860 : CollatzResearch.WordTrace tailWord_4363860 prefixEnd_4363860 2240757688929401611380979 := by
  unfold tailWord_4363860
  simp only [CollatzResearch.WordTrace]
  refine ⟨79581524985243991398852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106108699980325321865136689 79581524985243991398852517)
  ·
    refine ⟨14921535934733248387284847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79581524985243991398852517 14921535934733248387284847)
    ·
      refine ⟨22382303902099872580927271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14921535934733248387284847 22382303902099872580927271)
      ·
        refine ⟨33573455853149808871390907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22382303902099872580927271 33573455853149808871390907)
        ·
          refine ⟨50360183779724713307086361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33573455853149808871390907 50360183779724713307086361)
          ·
            refine ⟨37770137834793534980314771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50360183779724713307086361 37770137834793534980314771)
            ·
              refine ⟨56655206752190302470472157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37770137834793534980314771 56655206752190302470472157)
              ·
                refine ⟨21245702532071363426427059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56655206752190302470472157 21245702532071363426427059)
                ·
                  refine ⟨31868553798107045139640589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21245702532071363426427059 31868553798107045139640589)
                  ·
                    refine ⟨11950707674290141927365221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31868553798107045139640589 11950707674290141927365221)
                    ·
                      refine ⟨2240757688929401611380979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11950707674290141927365221 2240757688929401611380979)
                      ·
                        rfl

theorem cell23_4363860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4363860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363860 prefixEnd_4363860 := by exact prefixLift 4363860
  have htrace : WordTrace (prefixWord ++ tailWord_4363860) baseStart_4363860 baseEnd_4363860 := by
    simpa [prefixWord, tailWord_4363860, baseEnd_4363860] using wordTrace_append hprefix tailTrace_4363860
  have hstable : (prefixWord ++ tailWord_4363860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363860).length < 2 ^ (prefixWord ++ tailWord_4363860).sum := by decide
  have hdescent : baseEnd_4363860 < baseStart_4363860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363877 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4363877 : Nat := 118140960795 + 4363877 * 2 ^ 59
def prefixEnd_4363877 : Nat := 4983230072969 + 3 ^ 40 * 4363877 * 2
def baseEnd_4363877 : Nat := 2240766418100528044868401

theorem tailTrace_4363877 : CollatzResearch.WordTrace tailWord_4363877 prefixEnd_4363877 2240766418100528044868401 := by
  unfold tailWord_4363877
  simp only [CollatzResearch.WordTrace]
  refine ⟨159163670011426394701073885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106109113340950929800715923 159163670011426394701073885)
  ·
    refine ⟨59686376254284898012902707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159163670011426394701073885 59686376254284898012902707)
    ·
      refine ⟨89529564381427347019354061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59686376254284898012902707 89529564381427347019354061)
      ·
        refine ⟨33573586643035255132257773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89529564381427347019354061 33573586643035255132257773)
        ·
          refine ⟨12590094991138220674596665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33573586643035255132257773 12590094991138220674596665)
          ·
            refine ⟨9442571243353665505947499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12590094991138220674596665 9442571243353665505947499)
            ·
              refine ⟨14163856865030498258921249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442571243353665505947499 14163856865030498258921249)
              ·
                refine ⟨10622892648772873694190937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14163856865030498258921249 10622892648772873694190937)
                ·
                  refine ⟨7967169486579655270643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622892648772873694190937 7967169486579655270643203)
                  ·
                    refine ⟨11950754229869482905964805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7967169486579655270643203 11950754229869482905964805)
                    ·
                      refine ⟨2240766418100528044868401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11950754229869482905964805 2240766418100528044868401)
                      ·
                        rfl

theorem cell23_4363877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4363877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363877 prefixEnd_4363877 := by exact prefixLift 4363877
  have htrace : WordTrace (prefixWord ++ tailWord_4363877) baseStart_4363877 baseEnd_4363877 := by
    simpa [prefixWord, tailWord_4363877, baseEnd_4363877] using wordTrace_append hprefix tailTrace_4363877
  have hstable : (prefixWord ++ tailWord_4363877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363877).length < 2 ^ (prefixWord ++ tailWord_4363877).sum := by decide
  have hdescent : baseEnd_4363877 < baseStart_4363877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363903 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_4363903 : Nat := 118140960795 + 4363903 * 2 ^ 59
def prefixEnd_4363903 : Nat := 4983230072969 + 3 ^ 40 * 4363903 * 2
def baseEnd_4363903 : Nat := 2240779768597544943143281

theorem tailTrace_4363903 : CollatzResearch.WordTrace tailWord_4363903 prefixEnd_4363903 2240779768597544943143281 := by
  unfold tailWord_4363903
  simp only [CollatzResearch.WordTrace]
  refine ⟨159164618309332201141520363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106109745539554800761013575 159164618309332201141520363)
  ·
    refine ⟨238746927463998301712280545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159164618309332201141520363 238746927463998301712280545)
    ·
      refine ⟨179060195597998726284210409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238746927463998301712280545 179060195597998726284210409)
      ·
        refine ⟨134295146698499044713157807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179060195597998726284210409 134295146698499044713157807)
        ·
          refine ⟨201442720047748567069736711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134295146698499044713157807 201442720047748567069736711)
          ·
            refine ⟨302164080071622850604605067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201442720047748567069736711 302164080071622850604605067)
            ·
              refine ⟨453246120107434275906907601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302164080071622850604605067 453246120107434275906907601)
              ·
                refine ⟨339934590080575706930180701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453246120107434275906907601 339934590080575706930180701)
                ·
                  refine ⟨127475471280215890098817763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339934590080575706930180701 127475471280215890098817763)
                  ·
                    refine ⟨191213206920323835148226645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127475471280215890098817763 191213206920323835148226645)
                    ·
                      refine ⟨2240779768597544943143281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191213206920323835148226645 2240779768597544943143281)
                      ·
                        rfl

theorem cell23_4363903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_4363903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363903 prefixEnd_4363903 := by exact prefixLift 4363903
  have htrace : WordTrace (prefixWord ++ tailWord_4363903) baseStart_4363903 baseEnd_4363903 := by
    simpa [prefixWord, tailWord_4363903, baseEnd_4363903] using wordTrace_append hprefix tailTrace_4363903
  have hstable : (prefixWord ++ tailWord_4363903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363903).length < 2 ^ (prefixWord ++ tailWord_4363903).sum := by decide
  have hdescent : baseEnd_4363903 < baseStart_4363903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363914 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_4363914 : Nat := 118140960795 + 4363914 * 2 ^ 59
def prefixEnd_4363914 : Nat := 4983230072969 + 3 ^ 40 * 4363914 * 2
def baseEnd_4363914 : Nat := 2240785416884744400105731

theorem tailTrace_4363914 : CollatzResearch.WordTrace tailWord_4363914 prefixEnd_4363914 2240785416884744400105731 := by
  unfold tailWord_4363914
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791254878073087505042699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106110013008194900013447197 39791254878073087505042699)
  ·
    refine ⟨59686882317109631257564049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39791254878073087505042699 59686882317109631257564049)
    ·
      refine ⟨44765161737832223443173037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59686882317109631257564049 44765161737832223443173037)
      ·
        refine ⟨16786935651687083791189889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44765161737832223443173037 16786935651687083791189889)
        ·
          refine ⟨12590201738765312843392417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786935651687083791189889 12590201738765312843392417)
          ·
            refine ⟨9442651304073984632544313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12590201738765312843392417 9442651304073984632544313)
            ·
              refine ⟨7081988478055488474408235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442651304073984632544313 7081988478055488474408235)
              ·
                refine ⟨10622982717083232711612353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081988478055488474408235 10622982717083232711612353)
                ·
                  refine ⟨7967237037812424533709265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622982717083232711612353 7967237037812424533709265)
                  ·
                    refine ⟨5975427778359318400281949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7967237037812424533709265 5975427778359318400281949)
                    ·
                      refine ⟨2240785416884744400105731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5975427778359318400281949 2240785416884744400105731)
                      ·
                        rfl

theorem cell23_4363914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_4363914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363914 prefixEnd_4363914 := by exact prefixLift 4363914
  have htrace : WordTrace (prefixWord ++ tailWord_4363914) baseStart_4363914 baseEnd_4363914 := by
    simpa [prefixWord, tailWord_4363914, baseEnd_4363914] using wordTrace_append hprefix tailTrace_4363914
  have hstable : (prefixWord ++ tailWord_4363914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363914).length < 2 ^ (prefixWord ++ tailWord_4363914).sum := by decide
  have hdescent : baseEnd_4363914 < baseStart_4363914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363934 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4363934 : Nat := 118140960795 + 4363934 * 2 ^ 59
def prefixEnd_4363934 : Nat := 4983230072969 + 3 ^ 40 * 4363934 * 2
def baseEnd_4363934 : Nat := 248977298499759369095071

theorem tailTrace_4363934 : CollatzResearch.WordTrace tailWord_4363934 prefixEnd_4363934 248977298499759369095071 := by
  unfold tailWord_4363934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19895718621527486679487357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106110499314813262290599237 19895718621527486679487357)
  ·
    refine ⟨7460894483072807504807759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19895718621527486679487357 7460894483072807504807759)
    ·
      refine ⟨11191341724609211257211639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460894483072807504807759 11191341724609211257211639)
      ·
        refine ⟨16787012586913816885817459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191341724609211257211639 16787012586913816885817459)
        ·
          refine ⟨25180518880370725328726189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16787012586913816885817459 25180518880370725328726189)
          ·
            refine ⟨9442694580139021998272321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25180518880370725328726189 9442694580139021998272321)
            ·
              refine ⟨7082020935104266498704241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442694580139021998272321 7082020935104266498704241)
              ·
                refine ⟨5311515701328199874028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7082020935104266498704241 5311515701328199874028181)
                ·
                  refine ⟨248977298499759369095071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5311515701328199874028181 248977298499759369095071)
                  ·
                    rfl

theorem cell23_4363934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4363934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363934 prefixEnd_4363934 := by exact prefixLift 4363934
  have htrace : WordTrace (prefixWord ++ tailWord_4363934) baseStart_4363934 baseEnd_4363934 := by
    simpa [prefixWord, tailWord_4363934, baseEnd_4363934] using wordTrace_append hprefix tailTrace_4363934
  have hstable : (prefixWord ++ tailWord_4363934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363934).length < 2 ^ (prefixWord ++ tailWord_4363934).sum := by decide
  have hdescent : baseEnd_4363934 < baseStart_4363934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363938 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4363938 : Nat := 118140960795 + 4363938 * 2 ^ 59
def prefixEnd_4363938 : Nat := 4983230072969 + 3 ^ 40 * 4363938 * 2
def baseEnd_4363938 : Nat := 746932580140150768735207

theorem tailTrace_4363938 : CollatzResearch.WordTrace tailWord_4363938 prefixEnd_4363938 746932580140150768735207 := by
  unfold tailWord_4363938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791473716051350529761117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106110596576136934746029645 39791473716051350529761117)
  ·
    refine ⟨14921802643519256448660419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39791473716051350529761117 14921802643519256448660419)
    ·
      refine ⟨22382703965278884672990629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14921802643519256448660419 22382703965278884672990629)
      ·
        refine ⟨4196756993489790876185743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22382703965278884672990629 4196756993489790876185743)
        ·
          refine ⟨6295135490234686314278615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196756993489790876185743 6295135490234686314278615)
          ·
            refine ⟨9442703235352029471417923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295135490234686314278615 9442703235352029471417923)
            ·
              refine ⟨14164054853028044207126885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442703235352029471417923 14164054853028044207126885)
              ·
                refine ⟨2655760284942758288836291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14164054853028044207126885 2655760284942758288836291)
                ·
                  refine ⟨3983640427414137433254437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655760284942758288836291 3983640427414137433254437)
                  ·
                    refine ⟨746932580140150768735207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983640427414137433254437 746932580140150768735207)
                    ·
                      rfl

theorem cell23_4363938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4363938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363938 prefixEnd_4363938 := by exact prefixLift 4363938
  have htrace : WordTrace (prefixWord ++ tailWord_4363938) baseStart_4363938 baseEnd_4363938 := by
    simpa [prefixWord, tailWord_4363938, baseEnd_4363938] using wordTrace_append hprefix tailTrace_4363938
  have hstable : (prefixWord ++ tailWord_4363938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363938).length < 2 ^ (prefixWord ++ tailWord_4363938).sum := by decide
  have hdescent : baseEnd_4363938 < baseStart_4363938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4363967 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_4363967 : Nat := 118140960795 + 4363967 * 2 ^ 59
def prefixEnd_4363967 : Nat := 4983230072969 + 3 ^ 40 * 4363967 * 2
def baseEnd_4363967 : Nat := 2240812631359432692742987

theorem tailTrace_4363967 : CollatzResearch.WordTrace tailWord_4363967 prefixEnd_4363967 2240812631359432692742987 := by
  unfold tailWord_4363967
  simp only [CollatzResearch.WordTrace]
  refine ⟨159166952581100340071850155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106111301720733560047900103 159166952581100340071850155)
  ·
    refine ⟨238750428871650510107775233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159166952581100340071850155 238750428871650510107775233)
    ·
      refine ⟨179062821653737882580831425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238750428871650510107775233 179062821653737882580831425)
      ·
        refine ⟨134297116240303411935623569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179062821653737882580831425 134297116240303411935623569)
        ·
          refine ⟨100722837180227558951717677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134297116240303411935623569 100722837180227558951717677)
          ·
            refine ⟨37771063942585334606894129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100722837180227558951717677 37771063942585334606894129)
            ·
              refine ⟨28328297956939000955170597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37771063942585334606894129 28328297956939000955170597)
              ·
                refine ⟨5311555866926062679094487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28328297956939000955170597 5311555866926062679094487)
                ·
                  refine ⟨7967333800389094018641731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311555866926062679094487 7967333800389094018641731)
                  ·
                    refine ⟨11951000700583641027962597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7967333800389094018641731 11951000700583641027962597)
                    ·
                      refine ⟨2240812631359432692742987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11951000700583641027962597 2240812631359432692742987)
                      ·
                        rfl

theorem cell23_4363967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_4363967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4363967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4363967 prefixEnd_4363967 := by exact prefixLift 4363967
  have htrace : WordTrace (prefixWord ++ tailWord_4363967) baseStart_4363967 baseEnd_4363967 := by
    simpa [prefixWord, tailWord_4363967, baseEnd_4363967] using wordTrace_append hprefix tailTrace_4363967
  have hstable : (prefixWord ++ tailWord_4363967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4363967).length < 2 ^ (prefixWord ++ tailWord_4363967).sum := by decide
  have hdescent : baseEnd_4363967 < baseStart_4363967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4363967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
