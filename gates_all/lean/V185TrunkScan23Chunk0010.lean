import V185TrunkScan23Chunk0009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_58093 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_58093 : Nat := 118140960795 + 58093 * 2 ^ 59
def prefixEnd_58093 : Nat := 4983230072969 + 3 ^ 40 * 58093 * 2
def baseEnd_58093 : Nat := 9943210553915481523447

theorem tailTrace_58093 : CollatzResearch.WordTrace tailWord_58093 prefixEnd_58093 9943210553915481523447 := by
  unfold tailWord_58093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118825778546457339618933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1412550519030971559745955 2118825778546457339618933)
  ·
    refine ⟨198639916738730375589275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2118825778546457339618933 198639916738730375589275)
    ·
      refine ⟨297959875108095563383913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198639916738730375589275 297959875108095563383913)
      ·
        refine ⟨223469906331071672537935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297959875108095563383913 223469906331071672537935)
        ·
          refine ⟨335204859496607508806903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223469906331071672537935 335204859496607508806903)
          ·
            refine ⟨502807289244911263210355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335204859496607508806903 502807289244911263210355)
            ·
              refine ⟨754210933867366894815533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502807289244911263210355 754210933867366894815533)
              ·
                refine ⟨282829100200262585555825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 754210933867366894815533 282829100200262585555825)
                ·
                  refine ⟨212121825150196939166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282829100200262585555825 212121825150196939166869)
                  ·
                    refine ⟨9943210553915481523447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212121825150196939166869 9943210553915481523447)
                    ·
                      rfl

theorem cell23_58093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_58093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58093 prefixEnd_58093 := by exact prefixLift 58093
  have htrace : WordTrace (prefixWord ++ tailWord_58093) baseStart_58093 baseEnd_58093 := by
    simpa [prefixWord, tailWord_58093, baseEnd_58093] using wordTrace_append hprefix tailTrace_58093
  have hstable : (prefixWord ++ tailWord_58093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58093).length < 2 ^ (prefixWord ++ tailWord_58093).sum := by decide
  have hdescent : baseEnd_58093 < baseStart_58093 := by decide
  rcases family_descends (prefixWord ++ tailWord_58093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58094 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_58094 : Nat := 118140960795 + 58094 * 2 ^ 59
def prefixEnd_58094 : Nat := 4983230072969 + 3 ^ 40 * 58094 * 2
def baseEnd_58094 : Nat := 29830145142400940657837

theorem tailTrace_58094 : CollatzResearch.WordTrace tailWord_58094 prefixEnd_58094 29830145142400940657837 := by
  unfold tailWord_58094
  simp only [CollatzResearch.WordTrace]
  refine ⟨264857781442854313800667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1412574834361889673603557 264857781442854313800667)
  ·
    refine ⟨397286672164281470701001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264857781442854313800667 397286672164281470701001)
    ·
      refine ⟨297965004123211103025751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397286672164281470701001 297965004123211103025751)
      ·
        refine ⟨446947506184816654538627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297965004123211103025751 446947506184816654538627)
        ·
          refine ⟨670421259277224981807941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446947506184816654538627 670421259277224981807941)
          ·
            refine ⟨125703986114479684088989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670421259277224981807941 125703986114479684088989)
            ·
              refine ⟨47138994792929881533371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125703986114479684088989 47138994792929881533371)
              ·
                refine ⟨70708492189394822300057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47138994792929881533371 70708492189394822300057)
                ·
                  refine ⟨53031369142046116725043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70708492189394822300057 53031369142046116725043)
                  ·
                    refine ⟨79547053713069175087565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53031369142046116725043 79547053713069175087565)
                    ·
                      refine ⟨29830145142400940657837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79547053713069175087565 29830145142400940657837)
                      ·
                        rfl

theorem cell23_58094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_58094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58094 prefixEnd_58094 := by exact prefixLift 58094
  have htrace : WordTrace (prefixWord ++ tailWord_58094) baseStart_58094 baseEnd_58094 := by
    simpa [prefixWord, tailWord_58094, baseEnd_58094] using wordTrace_append hprefix tailTrace_58094
  have hstable : (prefixWord ++ tailWord_58094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58094).length < 2 ^ (prefixWord ++ tailWord_58094).sum := by decide
  have hdescent : baseEnd_58094 < baseStart_58094 := by decide
  rcases family_descends (prefixWord ++ tailWord_58094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58101 : List Nat := [1, 3, 6, 1, 2, 1, 2, 7]
def baseStart_58101 : Nat := 118140960795 + 58101 * 2 ^ 59
def prefixEnd_58101 : Nat := 4983230072969 + 3 ^ 40 * 58101 * 2
def baseEnd_58101 : Nat := 1104953315073422713715

theorem tailTrace_58101 : CollatzResearch.WordTrace tailWord_58101 prefixEnd_58101 1104953315073422713715 := by
  unfold tailWord_58101
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119117562517474705910157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1412745041678316470606771 2119117562517474705910157)
  ·
    refine ⟨794669085944053014716309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2119117562517474705910157 794669085944053014716309)
    ·
      refine ⟨37250113403627485064827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 794669085944053014716309 37250113403627485064827)
      ·
        refine ⟨55875170105441227597241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37250113403627485064827 55875170105441227597241)
        ·
          refine ⟨41906377579080920697931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55875170105441227597241 41906377579080920697931)
          ·
            refine ⟨62859566368621381046897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41906377579080920697931 62859566368621381046897)
            ·
              refine ⟨47144674776466035785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62859566368621381046897 47144674776466035785173)
              ·
                refine ⟨1104953315073422713715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47144674776466035785173 1104953315073422713715)
                ·
                  rfl

theorem cell23_58101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 7].length) (baseStart_58101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58101 prefixEnd_58101 := by exact prefixLift 58101
  have htrace : WordTrace (prefixWord ++ tailWord_58101) baseStart_58101 baseEnd_58101 := by
    simpa [prefixWord, tailWord_58101, baseEnd_58101] using wordTrace_append hprefix tailTrace_58101
  have hstable : (prefixWord ++ tailWord_58101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58101).length < 2 ^ (prefixWord ++ tailWord_58101).sum := by decide
  have hdescent : baseEnd_58101 < baseStart_58101 := by decide
  rcases family_descends (prefixWord ++ tailWord_58101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58140 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 7]
def baseStart_58140 : Nat := 118140960795 + 58140 * 2 ^ 59
def prefixEnd_58140 : Nat := 4983230072969 + 3 ^ 40 * 58140 * 2
def baseEnd_58140 : Nat := 3317085028056417853625

theorem tailTrace_58140 : CollatzResearch.WordTrace tailWord_58140 prefixEnd_58140 3317085028056417853625 := by
  unfold tailWord_58140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060270004688092183289937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1413693339584122911053249 1060270004688092183289937)
  ·
    refine ⟨795202503516069137467453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1060270004688092183289937 795202503516069137467453)
    ·
      refine ⟨298200938818525926550295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 795202503516069137467453 298200938818525926550295)
      ·
        refine ⟨447301408227788889825443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298200938818525926550295 447301408227788889825443)
        ·
          refine ⟨670952112341683334738165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447301408227788889825443 670952112341683334738165)
          ·
            refine ⟨62901760532032812631703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 670952112341683334738165 62901760532032812631703)
            ·
              refine ⟨94352640798049218947555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62901760532032812631703 94352640798049218947555)
              ·
                refine ⟨141528961197073828421333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94352640798049218947555 141528961197073828421333)
                ·
                  refine ⟨3317085028056417853625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 141528961197073828421333 3317085028056417853625)
                  ·
                    rfl

theorem cell23_58140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_58140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58140 prefixEnd_58140 := by exact prefixLift 58140
  have htrace : WordTrace (prefixWord ++ tailWord_58140) baseStart_58140 baseEnd_58140 := by
    simpa [prefixWord, tailWord_58140, baseEnd_58140] using wordTrace_append hprefix tailTrace_58140
  have hstable : (prefixWord ++ tailWord_58140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58140).length < 2 ^ (prefixWord ++ tailWord_58140).sum := by decide
  have hdescent : baseEnd_58140 < baseStart_58140 := by decide
  rcases family_descends (prefixWord ++ tailWord_58140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58190 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_58190 : Nat := 118140960795 + 58190 * 2 ^ 59
def prefixEnd_58190 : Nat := 4983230072969 + 3 ^ 40 * 58190 * 2
def baseEnd_58190 : Nat := 29879439285232565057395

theorem tailTrace_58190 : CollatzResearch.WordTrace tailWord_58190 prefixEnd_58190 29879439285232565057395 := by
  unfold tailWord_58190
  simp only [CollatzResearch.WordTrace]
  refine ⟨265295457399380363237503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1414909106130028603933349 265295457399380363237503)
  ·
    refine ⟨397943186099070544856255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265295457399380363237503 397943186099070544856255)
    ·
      refine ⟨596914779148605817284383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397943186099070544856255 596914779148605817284383)
      ·
        refine ⟨895372168722908725926575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596914779148605817284383 895372168722908725926575)
        ·
          refine ⟨1343058253084363088889863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895372168722908725926575 1343058253084363088889863)
          ·
            refine ⟨2014587379626544633334795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343058253084363088889863 2014587379626544633334795)
            ·
              refine ⟨3021881069439816950002193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014587379626544633334795 3021881069439816950002193)
              ·
                refine ⟨2266410802079862712501645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021881069439816950002193 2266410802079862712501645)
                ·
                  refine ⟨849904050779948517188117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2266410802079862712501645 849904050779948517188117)
                  ·
                    refine ⟨39839252380310086743193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 849904050779948517188117 39839252380310086743193)
                    ·
                      refine ⟨29879439285232565057395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 39839252380310086743193 29879439285232565057395)
                      ·
                        rfl

theorem cell23_58190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_58190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58190 prefixEnd_58190 := by exact prefixLift 58190
  have htrace : WordTrace (prefixWord ++ tailWord_58190) baseStart_58190 baseEnd_58190 := by
    simpa [prefixWord, tailWord_58190, baseEnd_58190] using wordTrace_append hprefix tailTrace_58190
  have hstable : (prefixWord ++ tailWord_58190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58190).length < 2 ^ (prefixWord ++ tailWord_58190).sum := by decide
  have hdescent : baseEnd_58190 < baseStart_58190 := by decide
  rcases family_descends (prefixWord ++ tailWord_58190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58247 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 6]
def baseStart_58247 : Nat := 118140960795 + 58247 * 2 ^ 59
def prefixEnd_58247 : Nat := 4983230072969 + 3 ^ 40 * 58247 * 2
def baseEnd_58247 : Nat := 3323189742504315782737

theorem tailTrace_58247 : CollatzResearch.WordTrace tailWord_58247 prefixEnd_58247 3323189742504315782737 := by
  unfold tailWord_58247
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124442619988541640724995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1416295079992361093816663 2124442619988541640724995)
  ·
    refine ⟨3186663929982812461087493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2124442619988541640724995 3186663929982812461087493)
    ·
      refine ⟨597499486871777336453905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3186663929982812461087493 597499486871777336453905)
      ·
        refine ⟨448124615153833002340429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597499486871777336453905 448124615153833002340429)
        ·
          refine ⟨168046730682687375877661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448124615153833002340429 168046730682687375877661)
          ·
            refine ⟨63017524006007765954123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168046730682687375877661 63017524006007765954123)
            ·
              refine ⟨94526286009011648931185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63017524006007765954123 94526286009011648931185)
              ·
                refine ⟨70894714506758736698389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94526286009011648931185 70894714506758736698389)
                ·
                  refine ⟨3323189742504315782737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70894714506758736698389 3323189742504315782737)
                  ·
                    rfl

theorem cell23_58247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 6].length) (baseStart_58247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58247 prefixEnd_58247 := by exact prefixLift 58247
  have htrace : WordTrace (prefixWord ++ tailWord_58247) baseStart_58247 baseEnd_58247 := by
    simpa [prefixWord, tailWord_58247, baseEnd_58247] using wordTrace_append hprefix tailTrace_58247
  have hstable : (prefixWord ++ tailWord_58247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58247).length < 2 ^ (prefixWord ++ tailWord_58247).sum := by decide
  have hdescent : baseEnd_58247 < baseStart_58247 := by decide
  rcases family_descends (prefixWord ++ tailWord_58247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58250 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_58250 : Nat := 118140960795 + 58250 * 2 ^ 59
def prefixEnd_58250 : Nat := 4983230072969 + 3 ^ 40 * 58250 * 2
def baseEnd_58250 : Nat := 29910248124502330307119

theorem tailTrace_58250 : CollatzResearch.WordTrace tailWord_58250 prefixEnd_58250 29910248124502330307119 := by
  unfold tailWord_58250
  simp only [CollatzResearch.WordTrace]
  refine ⟨531138009744418288271051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1416368025985115435389469 531138009744418288271051)
  ·
    refine ⟨796707014616627432406577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531138009744418288271051 796707014616627432406577)
    ·
      refine ⟨597530260962470574304933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796707014616627432406577 597530260962470574304933)
      ·
        refine ⟨112036923930463232682175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 597530260962470574304933 112036923930463232682175)
        ·
          refine ⟨168055385895694849023263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112036923930463232682175 168055385895694849023263)
          ·
            refine ⟨252083078843542273534895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168055385895694849023263 252083078843542273534895)
            ·
              refine ⟨378124618265313410302343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252083078843542273534895 378124618265313410302343)
              ·
                refine ⟨567186927397970115453515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378124618265313410302343 567186927397970115453515)
                ·
                  refine ⟨850780391096955173180273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567186927397970115453515 850780391096955173180273)
                  ·
                    refine ⟨638085293322716379885205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850780391096955173180273 638085293322716379885205)
                    ·
                      refine ⟨29910248124502330307119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 638085293322716379885205 29910248124502330307119)
                      ·
                        rfl

theorem cell23_58250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_58250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58250 prefixEnd_58250 := by exact prefixLift 58250
  have htrace : WordTrace (prefixWord ++ tailWord_58250) baseStart_58250 baseEnd_58250 := by
    simpa [prefixWord, tailWord_58250, baseEnd_58250] using wordTrace_append hprefix tailTrace_58250
  have hstable : (prefixWord ++ tailWord_58250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58250).length < 2 ^ (prefixWord ++ tailWord_58250).sum := by decide
  have hdescent : baseEnd_58250 < baseStart_58250 := by decide
  rcases family_descends (prefixWord ++ tailWord_58250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58274 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_58274 : Nat := 118140960795 + 58274 * 2 ^ 59
def prefixEnd_58274 : Nat := 4983230072969 + 3 ^ 40 * 58274 * 2
def baseEnd_58274 : Nat := 29922571660210236407009

theorem tailTrace_58274 : CollatzResearch.WordTrace tailWord_58274 prefixEnd_58274 29922571660210236407009 := by
  unfold tailWord_58274
  simp only [CollatzResearch.WordTrace]
  refine ⟨531356847722681312989469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1416951593927150167971917 531356847722681312989469)
  ·
    refine ⟨199258817896005492371051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 531356847722681312989469 199258817896005492371051)
    ·
      refine ⟨298888226844008238556577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199258817896005492371051 298888226844008238556577)
      ·
        refine ⟨224166170133006178917433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298888226844008238556577 224166170133006178917433)
        ·
          refine ⟨168124627599754634188075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224166170133006178917433 168124627599754634188075)
          ·
            refine ⟨252186941399631951282113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168124627599754634188075 252186941399631951282113)
            ·
              refine ⟨189140206049723963461585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252186941399631951282113 189140206049723963461585)
              ·
                refine ⟨141855154537292972596189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189140206049723963461585 141855154537292972596189)
                ·
                  refine ⟨53195682951484864723571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141855154537292972596189 53195682951484864723571)
                  ·
                    refine ⟨79793524427227297085357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53195682951484864723571 79793524427227297085357)
                    ·
                      refine ⟨29922571660210236407009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79793524427227297085357 29922571660210236407009)
                      ·
                        rfl

theorem cell23_58274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_58274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58274 prefixEnd_58274 := by exact prefixLift 58274
  have htrace : WordTrace (prefixWord ++ tailWord_58274) baseStart_58274 baseEnd_58274 := by
    simpa [prefixWord, tailWord_58274, baseEnd_58274] using wordTrace_append hprefix tailTrace_58274
  have hstable : (prefixWord ++ tailWord_58274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58274).length < 2 ^ (prefixWord ++ tailWord_58274).sum := by decide
  have hdescent : baseEnd_58274 < baseStart_58274 := by decide
  rcases family_descends (prefixWord ++ tailWord_58274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58285 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_58285 : Nat := 118140960795 + 58285 * 2 ^ 59
def prefixEnd_58285 : Nat := 4983230072969 + 3 ^ 40 * 58285 * 2
def baseEnd_58285 : Nat := 9976073315803231123153

theorem tailTrace_58285 : CollatzResearch.WordTrace tailWord_58285 prefixEnd_58285 9976073315803231123153 := by
  unfold tailWord_58285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125828593850874130608309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1417219062567249420405539 2125828593850874130608309)
  ·
    refine ⟨199296430673519449744529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2125828593850874130608309 199296430673519449744529)
    ·
      refine ⟨149472323005139587308397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199296430673519449744529 149472323005139587308397)
      ·
        refine ⟨56052121126927345240649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149472323005139587308397 56052121126927345240649)
        ·
          refine ⟨42039090845195508930487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56052121126927345240649 42039090845195508930487)
          ·
            refine ⟨63058636267793263395731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42039090845195508930487 63058636267793263395731)
            ·
              refine ⟨94587954401689895093597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63058636267793263395731 94587954401689895093597)
              ·
                refine ⟨35470482900633710660099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94587954401689895093597 35470482900633710660099)
                ·
                  refine ⟨53205724350950565990149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35470482900633710660099 53205724350950565990149)
                  ·
                    refine ⟨9976073315803231123153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53205724350950565990149 9976073315803231123153)
                    ·
                      rfl

theorem cell23_58285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_58285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58285 prefixEnd_58285 := by exact prefixLift 58285
  have htrace : WordTrace (prefixWord ++ tailWord_58285) baseStart_58285 baseEnd_58285 := by
    simpa [prefixWord, tailWord_58285, baseEnd_58285] using wordTrace_append hprefix tailTrace_58285
  have hstable : (prefixWord ++ tailWord_58285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58285).length < 2 ^ (prefixWord ++ tailWord_58285).sum := by decide
  have hdescent : baseEnd_58285 < baseStart_58285 := by decide
  rcases family_descends (prefixWord ++ tailWord_58285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58297 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 4]
def baseStart_58297 : Nat := 118140960795 + 58297 * 2 ^ 59
def prefixEnd_58297 : Nat := 4983230072969 + 3 ^ 40 * 58297 * 2
def baseEnd_58297 : Nat := 29934381715263646419403

theorem tailTrace_58297 : CollatzResearch.WordTrace tailWord_58297 prefixEnd_58297 29934381715263646419403 := by
  unfold tailWord_58297
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126266269807400180045145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1417510846538266786696763 2126266269807400180045145)
  ·
    refine ⟨1594699702355550135033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2126266269807400180045145 1594699702355550135033859)
    ·
      refine ⟨2392049553533325202550789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594699702355550135033859 2392049553533325202550789)
      ·
        refine ⟨448509291287498475478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2392049553533325202550789 448509291287498475478273)
        ·
          refine ⟨336381968465623856608705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448509291287498475478273 336381968465623856608705)
          ·
            refine ⟨252286476349217892456529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336381968465623856608705 252286476349217892456529)
            ·
              refine ⟨189214857261913419342397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252286476349217892456529 189214857261913419342397)
              ·
                refine ⟨70955571473217532253399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189214857261913419342397 70955571473217532253399)
                ·
                  refine ⟨106433357209826298380099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70955571473217532253399 106433357209826298380099)
                  ·
                    refine ⟨159650035814739447570149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106433357209826298380099 159650035814739447570149)
                    ·
                      refine ⟨29934381715263646419403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 159650035814739447570149 29934381715263646419403)
                      ·
                        rfl

theorem cell23_58297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_58297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58297 prefixEnd_58297 := by exact prefixLift 58297
  have htrace : WordTrace (prefixWord ++ tailWord_58297) baseStart_58297 baseEnd_58297 := by
    simpa [prefixWord, tailWord_58297, baseEnd_58297] using wordTrace_append hprefix tailTrace_58297
  have hstable : (prefixWord ++ tailWord_58297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58297).length < 2 ^ (prefixWord ++ tailWord_58297).sum := by decide
  have hdescent : baseEnd_58297 < baseStart_58297 := by decide
  rcases family_descends (prefixWord ++ tailWord_58297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58308 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_58308 : Nat := 118140960795 + 58308 * 2 ^ 59
def prefixEnd_58308 : Nat := 4983230072969 + 3 ^ 40 * 58308 * 2
def baseEnd_58308 : Nat := 29940030002463103381853

theorem tailTrace_58308 : CollatzResearch.WordTrace tailWord_58308 prefixEnd_58308 29940030002463103381853 := by
  unfold tailWord_58308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063333736383774529347789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1417778315178366039130385 1063333736383774529347789)
  ·
    refine ⟨398750151143915448505421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1063333736383774529347789 398750151143915448505421)
    ·
      refine ⟨149531306678968293189533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398750151143915448505421 149531306678968293189533)
      ·
        refine ⟨56074240004613109946075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149531306678968293189533 56074240004613109946075)
        ·
          refine ⟨84111360006919664919113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56074240004613109946075 84111360006919664919113)
          ·
            refine ⟨63083520005189748689335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84111360006919664919113 63083520005189748689335)
            ·
              refine ⟨94625280007784623034003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63083520005189748689335 94625280007784623034003)
              ·
                refine ⟨141937920011676934551005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94625280007784623034003 141937920011676934551005)
                ·
                  refine ⟨53226720004378850456627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141937920011676934551005 53226720004378850456627)
                  ·
                    refine ⟨79840080006568275684941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53226720004378850456627 79840080006568275684941)
                    ·
                      refine ⟨29940030002463103381853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79840080006568275684941 29940030002463103381853)
                      ·
                        rfl

theorem cell23_58308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_58308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58308 prefixEnd_58308 := by exact prefixLift 58308
  have htrace : WordTrace (prefixWord ++ tailWord_58308) baseStart_58308 baseEnd_58308 := by
    simpa [prefixWord, tailWord_58308, baseEnd_58308] using wordTrace_append hprefix tailTrace_58308
  have hstable : (prefixWord ++ tailWord_58308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58308).length < 2 ^ (prefixWord ++ tailWord_58308).sum := by decide
  have hdescent : baseEnd_58308 < baseStart_58308 := by decide
  rcases family_descends (prefixWord ++ tailWord_58308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58313 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_58313 : Nat := 118140960795 + 58313 * 2 ^ 59
def prefixEnd_58313 : Nat := 4983230072969 + 3 ^ 40 * 58313 * 2
def baseEnd_58313 : Nat := 29942597405735583819329

theorem tailTrace_58313 : CollatzResearch.WordTrace tailWord_58313 prefixEnd_58313 29942597405735583819329 := by
  unfold tailWord_58313
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126849837749434912627593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1417899891832956608418395 2126849837749434912627593)
  ·
    refine ⟨1595137378312076184470695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2126849837749434912627593 1595137378312076184470695)
    ·
      refine ⟨2392706067468114276706043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595137378312076184470695 2392706067468114276706043)
      ·
        refine ⟨3589059101202171415059065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392706067468114276706043 3589059101202171415059065)
        ·
          refine ⟨2691794325901628561294299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589059101202171415059065 2691794325901628561294299)
          ·
            refine ⟨4037691488852442841941449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691794325901628561294299 4037691488852442841941449)
            ·
              refine ⟨3028268616639332131456087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4037691488852442841941449 3028268616639332131456087)
              ·
                refine ⟨4542402924958998197184131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028268616639332131456087 4542402924958998197184131)
                ·
                  refine ⟨6813604387438497295776197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4542402924958998197184131 6813604387438497295776197)
                  ·
                    refine ⟨1277550822644718242958037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6813604387438497295776197 1277550822644718242958037)
                    ·
                      refine ⟨29942597405735583819329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1277550822644718242958037 29942597405735583819329)
                      ·
                        rfl

theorem cell23_58313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_58313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58313 prefixEnd_58313 := by exact prefixLift 58313
  have htrace : WordTrace (prefixWord ++ tailWord_58313) baseStart_58313 baseEnd_58313 := by
    simpa [prefixWord, tailWord_58313, baseEnd_58313] using wordTrace_append hprefix tailTrace_58313
  have hstable : (prefixWord ++ tailWord_58313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58313).length < 2 ^ (prefixWord ++ tailWord_58313).sum := by decide
  have hdescent : baseEnd_58313 < baseStart_58313 := by decide
  rcases family_descends (prefixWord ++ tailWord_58313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58324 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_58324 : Nat := 118140960795 + 58324 * 2 ^ 59
def prefixEnd_58324 : Nat := 4983230072969 + 3 ^ 40 * 58324 * 2
def baseEnd_58324 : Nat := 9982748564311680260593

theorem tailTrace_58324 : CollatzResearch.WordTrace tailWord_58324 prefixEnd_58324 9982748564311680260593 := by
  unfold tailWord_58324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063625520354791895639013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1418167360473055860852017 1063625520354791895639013)
  ·
    refine ⟨199429785066523480432315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1063625520354791895639013 199429785066523480432315)
    ·
      refine ⟨299144677599785220648473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199429785066523480432315 299144677599785220648473)
      ·
        refine ⟨224358508199838915486355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299144677599785220648473 224358508199838915486355)
        ·
          refine ⟨336537762299758373229533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224358508199838915486355 336537762299758373229533)
          ·
            refine ⟨126201660862409389961075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336537762299758373229533 126201660862409389961075)
            ·
              refine ⟨189302491293614084941613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126201660862409389961075 189302491293614084941613)
              ·
                refine ⟨70988434235105281853105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189302491293614084941613 70988434235105281853105)
                ·
                  refine ⟨53241325676328961389829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70988434235105281853105 53241325676328961389829)
                  ·
                    refine ⟨9982748564311680260593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53241325676328961389829 9982748564311680260593)
                    ·
                      rfl

theorem cell23_58324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_58324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58324 prefixEnd_58324 := by exact prefixLift 58324
  have htrace : WordTrace (prefixWord ++ tailWord_58324) baseStart_58324 baseEnd_58324 := by
    simpa [prefixWord, tailWord_58324, baseEnd_58324] using wordTrace_append hprefix tailTrace_58324
  have hstable : (prefixWord ++ tailWord_58324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58324).length < 2 ^ (prefixWord ++ tailWord_58324).sum := by decide
  have hdescent : baseEnd_58324 < baseStart_58324 := by decide
  rcases family_descends (prefixWord ++ tailWord_58324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58364 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_58364 : Nat := 118140960795 + 58364 * 2 ^ 59
def prefixEnd_58364 : Nat := 4983230072969 + 3 ^ 40 * 58364 * 2
def baseEnd_58364 : Nat := 29968784919114884281595

theorem tailTrace_58364 : CollatzResearch.WordTrace tailWord_58364 prefixEnd_58364 29968784919114884281595 := by
  unfold tailWord_58364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064354980282335311367073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1419139973709780415156097 1064354980282335311367073)
  ·
    refine ⟨798266235211751483525305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1064354980282335311367073 798266235211751483525305)
    ·
      refine ⟨598699676408813612643979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798266235211751483525305 598699676408813612643979)
      ·
        refine ⟨898049514613220418965969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598699676408813612643979 898049514613220418965969)
        ·
          refine ⟨673537135959915314224477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898049514613220418965969 673537135959915314224477)
          ·
            refine ⟨252576425984968242834179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673537135959915314224477 252576425984968242834179)
            ·
              refine ⟨378864638977452364251269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252576425984968242834179 378864638977452364251269)
              ·
                refine ⟨71037119808272318297113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378864638977452364251269 71037119808272318297113)
                ·
                  refine ⟨53277839856204238722835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71037119808272318297113 53277839856204238722835)
                  ·
                    refine ⟨79916759784306358084253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53277839856204238722835 79916759784306358084253)
                    ·
                      refine ⟨29968784919114884281595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 79916759784306358084253 29968784919114884281595)
                      ·
                        rfl

theorem cell23_58364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_58364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58364 prefixEnd_58364 := by exact prefixLift 58364
  have htrace : WordTrace (prefixWord ++ tailWord_58364) baseStart_58364 baseEnd_58364 := by
    simpa [prefixWord, tailWord_58364, baseEnd_58364] using wordTrace_append hprefix tailTrace_58364
  have hstable : (prefixWord ++ tailWord_58364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58364).length < 2 ^ (prefixWord ++ tailWord_58364).sum := by decide
  have hdescent : baseEnd_58364 < baseStart_58364 := by decide
  rcases family_descends (prefixWord ++ tailWord_58364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58380 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_58380 : Nat := 118140960795 + 58380 * 2 ^ 59
def prefixEnd_58380 : Nat := 4983230072969 + 3 ^ 40 * 58380 * 2
def baseEnd_58380 : Nat := 9992333536528940560507

theorem tailTrace_58380 : CollatzResearch.WordTrace tailWord_58380 prefixEnd_58380 9992333536528940560507 := by
  unfold tailWord_58380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064646764253352677658297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1419529019004470236877729 1064646764253352677658297)
  ·
    refine ⟨798485073190014508243723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1064646764253352677658297 798485073190014508243723)
    ·
      refine ⟨1197727609785021762365585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798485073190014508243723 1197727609785021762365585)
      ·
        refine ⟨898295707338766321774189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197727609785021762365585 898295707338766321774189)
        ·
          refine ⟨336860890252037370665321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898295707338766321774189 336860890252037370665321)
          ·
            refine ⟨252645667689028027998991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336860890252037370665321 252645667689028027998991)
            ·
              refine ⟨378968501533542041998487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252645667689028027998991 378968501533542041998487)
              ·
                refine ⟨568452752300313062997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378968501533542041998487 568452752300313062997731)
                ·
                  refine ⟨852679128450469594496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568452752300313062997731 852679128450469594496597)
                  ·
                    refine ⟨9992333536528940560507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 852679128450469594496597 9992333536528940560507)
                    ·
                      rfl

theorem cell23_58380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_58380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58380 prefixEnd_58380 := by exact prefixLift 58380
  have htrace : WordTrace (prefixWord ++ tailWord_58380) baseStart_58380 baseEnd_58380 := by
    simpa [prefixWord, tailWord_58380, baseEnd_58380] using wordTrace_append hprefix tailTrace_58380
  have hstable : (prefixWord ++ tailWord_58380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58380).length < 2 ^ (prefixWord ++ tailWord_58380).sum := by decide
  have hdescent : baseEnd_58380 < baseStart_58380 := by decide
  rcases family_descends (prefixWord ++ tailWord_58380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58437 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_58437 : Nat := 118140960795 + 58437 * 2 ^ 59
def prefixEnd_58437 : Nat := 4983230072969 + 3 ^ 40 * 58437 * 2
def baseEnd_58437 : Nat := 30006269006893098668759

theorem tailTrace_58437 : CollatzResearch.WordTrace tailWord_58437 prefixEnd_58437 30006269006893098668759 := by
  unfold tailWord_58437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131372489300204090141565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1420914992866802726761043 2131372489300204090141565)
  ·
    refine ⟨799264683487576533803087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2131372489300204090141565 799264683487576533803087)
    ·
      refine ⟨1198897025231364800704631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799264683487576533803087 1198897025231364800704631)
      ·
        refine ⟨1798345537847047201056947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198897025231364800704631 1798345537847047201056947)
        ·
          refine ⟨2697518306770570801585421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798345537847047201056947 2697518306770570801585421)
          ·
            refine ⟨1011569365038964050594533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2697518306770570801585421 1011569365038964050594533)
            ·
              refine ⟨189669255944805759486475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1011569365038964050594533 189669255944805759486475)
              ·
                refine ⟨284503883917208639229713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189669255944805759486475 284503883917208639229713)
                ·
                  refine ⟨213377912937906479422285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284503883917208639229713 213377912937906479422285)
                  ·
                    refine ⟨80016717351714929783357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213377912937906479422285 80016717351714929783357)
                    ·
                      refine ⟨30006269006893098668759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80016717351714929783357 30006269006893098668759)
                      ·
                        rfl

theorem cell23_58437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_58437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58437 prefixEnd_58437 := by exact prefixLift 58437
  have htrace : WordTrace (prefixWord ++ tailWord_58437) baseStart_58437 baseEnd_58437 := by
    simpa [prefixWord, tailWord_58437, baseEnd_58437] using wordTrace_append hprefix tailTrace_58437
  have hstable : (prefixWord ++ tailWord_58437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58437).length < 2 ^ (prefixWord ++ tailWord_58437).sum := by decide
  have hdescent : baseEnd_58437 < baseStart_58437 := by decide
  rcases family_descends (prefixWord ++ tailWord_58437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58438 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_58438 : Nat := 118140960795 + 58438 * 2 ^ 59
def prefixEnd_58438 : Nat := 4983230072969 + 3 ^ 40 * 58438 * 2
def baseEnd_58438 : Nat := 30006782487547594756255

theorem tailTrace_58438 : CollatzResearch.WordTrace tailWord_58438 prefixEnd_58438 30006782487547594756255 := by
  unfold tailWord_58438
  simp only [CollatzResearch.WordTrace]
  refine ⟨66606530071768164403999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1420939308197720840618645 66606530071768164403999)
  ·
    refine ⟨99909795107652246605999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66606530071768164403999 99909795107652246605999)
    ·
      refine ⟨149864692661478369908999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99909795107652246605999 149864692661478369908999)
      ·
        refine ⟨224797038992217554863499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149864692661478369908999 224797038992217554863499)
        ·
          refine ⟨337195558488326332295249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224797038992217554863499 337195558488326332295249)
          ·
            refine ⟨252896668866244749221437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337195558488326332295249 252896668866244749221437)
            ·
              refine ⟨94836250824841780958039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252896668866244749221437 94836250824841780958039)
              ·
                refine ⟨142254376237262671437059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94836250824841780958039 142254376237262671437059)
                ·
                  refine ⟨213381564355894007155589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142254376237262671437059 213381564355894007155589)
                  ·
                    refine ⟨40009043316730126341673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213381564355894007155589 40009043316730126341673)
                    ·
                      refine ⟨30006782487547594756255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40009043316730126341673 30006782487547594756255)
                      ·
                        rfl

theorem cell23_58438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_58438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58438 prefixEnd_58438 := by exact prefixLift 58438
  have htrace : WordTrace (prefixWord ++ tailWord_58438) baseStart_58438 baseEnd_58438 := by
    simpa [prefixWord, tailWord_58438, baseEnd_58438] using wordTrace_append hprefix tailTrace_58438
  have hstable : (prefixWord ++ tailWord_58438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58438).length < 2 ^ (prefixWord ++ tailWord_58438).sum := by decide
  have hdescent : baseEnd_58438 < baseStart_58438 := by decide
  rcases family_descends (prefixWord ++ tailWord_58438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58440 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 3, 7]
def baseStart_58440 : Nat := 118140960795 + 58440 * 2 ^ 59
def prefixEnd_58440 : Nat := 4983230072969 + 3 ^ 40 * 58440 * 2
def baseEnd_58440 : Nat := 10002603149618862310415

theorem tailTrace_58440 : CollatzResearch.WordTrace tailWord_58440 prefixEnd_58440 10002603149618862310415 := by
  unfold tailWord_58440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065740954144667801250387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1420987938859557068333849 1065740954144667801250387)
  ·
    refine ⟨1598611431217001701875581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1065740954144667801250387 1598611431217001701875581)
    ·
      refine ⟨599479286706375638203343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1598611431217001701875581 599479286706375638203343)
      ·
        refine ⟨899218930059563457305015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599479286706375638203343 899218930059563457305015)
        ·
          refine ⟨1348828395089345185957523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899218930059563457305015 1348828395089345185957523)
          ·
            refine ⟨2023242592634017778936285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348828395089345185957523 2023242592634017778936285)
            ·
              refine ⟨758715972237756667101107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2023242592634017778936285 758715972237756667101107)
              ·
                refine ⟨1138073958356635000651661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758715972237756667101107 1138073958356635000651661)
                ·
                  refine ⟨426777734383738125244373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138073958356635000651661 426777734383738125244373)
                  ·
                    refine ⟨10002603149618862310415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 426777734383738125244373 10002603149618862310415)
                    ·
                      rfl

theorem cell23_58440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_58440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58440 prefixEnd_58440 := by exact prefixLift 58440
  have htrace : WordTrace (prefixWord ++ tailWord_58440) baseStart_58440 baseEnd_58440 := by
    simpa [prefixWord, tailWord_58440, baseEnd_58440] using wordTrace_append hprefix tailTrace_58440
  have hstable : (prefixWord ++ tailWord_58440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58440).length < 2 ^ (prefixWord ++ tailWord_58440).sum := by decide
  have hdescent : baseEnd_58440 < baseStart_58440 := by decide
  rcases family_descends (prefixWord ++ tailWord_58440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58474 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_58474 : Nat := 118140960795 + 58474 * 2 ^ 59
def prefixEnd_58474 : Nat := 4983230072969 + 3 ^ 40 * 58474 * 2
def baseEnd_58474 : Nat := 10008422597036484635363

theorem tailTrace_58474 : CollatzResearch.WordTrace tailWord_58474 prefixEnd_58474 10008422597036484635363 := by
  unfold tailWord_58474
  simp only [CollatzResearch.WordTrace]
  refine ⟨533180497541539852309619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1421814660110772939492317 533180497541539852309619)
  ·
    refine ⟨799770746312309778464429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533180497541539852309619 799770746312309778464429)
    ·
      refine ⟨299914029867116166924161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 799770746312309778464429 299914029867116166924161)
      ·
        refine ⟨224935522400337125193121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299914029867116166924161 224935522400337125193121)
        ·
          refine ⟨168701641800252843894841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224935522400337125193121 168701641800252843894841)
          ·
            refine ⟨126526231350189632921131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168701641800252843894841 126526231350189632921131)
            ·
              refine ⟨189789347025284449381697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126526231350189632921131 189789347025284449381697)
              ·
                refine ⟨142342010268963337036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189789347025284449381697 142342010268963337036273)
                ·
                  refine ⟨106756507701722502777205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142342010268963337036273 106756507701722502777205)
                  ·
                    refine ⟨10008422597036484635363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106756507701722502777205 10008422597036484635363)
                    ·
                      rfl

theorem cell23_58474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_58474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58474 prefixEnd_58474 := by exact prefixLift 58474
  have htrace : WordTrace (prefixWord ++ tailWord_58474) baseStart_58474 baseEnd_58474 := by
    simpa [prefixWord, tailWord_58474, baseEnd_58474] using wordTrace_append hprefix tailTrace_58474
  have hstable : (prefixWord ++ tailWord_58474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58474).length < 2 ^ (prefixWord ++ tailWord_58474).sum := by decide
  have hdescent : baseEnd_58474 < baseStart_58474 := by decide
  rcases family_descends (prefixWord ++ tailWord_58474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58547 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 3, 5]
def baseStart_58547 : Nat := 118140960795 + 58547 * 2 ^ 59
def prefixEnd_58547 : Nat := 4983230072969 + 3 ^ 40 * 58547 * 2
def baseEnd_58547 : Nat := 10020917292962556097751

theorem tailTrace_58547 : CollatzResearch.WordTrace tailWord_58547 prefixEnd_58547 10020917292962556097751 := by
  unfold tailWord_58547
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135384518901692876645895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1423589679267795251097263 2135384518901692876645895)
  ·
    refine ⟨3203076778352539314968843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2135384518901692876645895 3203076778352539314968843)
    ·
      refine ⟨4804615167528808972453265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203076778352539314968843 4804615167528808972453265)
      ·
        refine ⟨3603461375646606729339949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804615167528808972453265 3603461375646606729339949)
        ·
          refine ⟨1351298015867477523502481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3603461375646606729339949 1351298015867477523502481)
          ·
            refine ⟨1013473511900608142626861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351298015867477523502481 1013473511900608142626861)
            ·
              refine ⟨380052566962728053485073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013473511900608142626861 380052566962728053485073)
              ·
                refine ⟨285039425222046040113805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380052566962728053485073 285039425222046040113805)
                ·
                  refine ⟨106889784458267265042677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285039425222046040113805 106889784458267265042677)
                  ·
                    refine ⟨10020917292962556097751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106889784458267265042677 10020917292962556097751)
                    ·
                      rfl

theorem cell23_58547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].length) (baseStart_58547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58547 prefixEnd_58547 := by exact prefixLift 58547
  have htrace : WordTrace (prefixWord ++ tailWord_58547) baseStart_58547 baseEnd_58547 := by
    simpa [prefixWord, tailWord_58547, baseEnd_58547] using wordTrace_append hprefix tailTrace_58547
  have hstable : (prefixWord ++ tailWord_58547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58547).length < 2 ^ (prefixWord ++ tailWord_58547).sum := by decide
  have hdescent : baseEnd_58547 < baseStart_58547 := by decide
  rcases family_descends (prefixWord ++ tailWord_58547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58554 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_58554 : Nat := 118140960795 + 58554 * 2 ^ 59
def prefixEnd_58554 : Nat := 4983230072969 + 3 ^ 40 * 58554 * 2
def baseEnd_58554 : Nat := 30066346243469140905721

theorem tailTrace_58554 : CollatzResearch.WordTrace tailWord_58554 prefixEnd_58554 30066346243469140905721 := by
  unfold tailWord_58554
  simp only [CollatzResearch.WordTrace]
  refine ⟨533909957469083268037679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1423759886584222048100477 533909957469083268037679)
  ·
    refine ⟨800864936203624902056519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533909957469083268037679 800864936203624902056519)
    ·
      refine ⟨1201297404305437353084779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800864936203624902056519 1201297404305437353084779)
      ·
        refine ⟨1801946106458156029627169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201297404305437353084779 1801946106458156029627169)
        ·
          refine ⟨1351459579843617022220377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801946106458156029627169 1351459579843617022220377)
          ·
            refine ⟨1013594684882712766665283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351459579843617022220377 1013594684882712766665283)
            ·
              refine ⟨1520392027324069149997925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013594684882712766665283 1520392027324069149997925)
              ·
                refine ⟨285073505123262965624611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1520392027324069149997925 285073505123262965624611)
                ·
                  refine ⟨427610257684894448436917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285073505123262965624611 427610257684894448436917)
                  ·
                    refine ⟨40088461657958854540961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 427610257684894448436917 40088461657958854540961)
                    ·
                      refine ⟨30066346243469140905721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40088461657958854540961 30066346243469140905721)
                      ·
                        rfl

theorem cell23_58554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_58554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58554 prefixEnd_58554 := by exact prefixLift 58554
  have htrace : WordTrace (prefixWord ++ tailWord_58554) baseStart_58554 baseEnd_58554 := by
    simpa [prefixWord, tailWord_58554, baseEnd_58554] using wordTrace_append hprefix tailTrace_58554
  have hstable : (prefixWord ++ tailWord_58554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58554).length < 2 ^ (prefixWord ++ tailWord_58554).sum := by decide
  have hdescent : baseEnd_58554 < baseStart_58554 := by decide
  rcases family_descends (prefixWord ++ tailWord_58554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58562 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_58562 : Nat := 118140960795 + 58562 * 2 ^ 59
def prefixEnd_58562 : Nat := 4983230072969 + 3 ^ 40 * 58562 * 2
def baseEnd_58562 : Nat := 30070454088705109605685

theorem tailTrace_58562 : CollatzResearch.WordTrace tailWord_58562 prefixEnd_58562 30070454088705109605685 := by
  unfold tailWord_58562
  simp only [CollatzResearch.WordTrace]
  refine ⟨533982903461837609610485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1423954409231566958961293 533982903461837609610485)
  ·
    refine ⟨50060897199547275900983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 533982903461837609610485 50060897199547275900983)
    ·
      refine ⟨75091345799320913851475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50060897199547275900983 75091345799320913851475)
      ·
        refine ⟨112637018698981370777213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75091345799320913851475 112637018698981370777213)
        ·
          refine ⟨42238882012118014041455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112637018698981370777213 42238882012118014041455)
          ·
            refine ⟨63358323018177021062183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42238882012118014041455 63358323018177021062183)
            ·
              refine ⟨95037484527265531593275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63358323018177021062183 95037484527265531593275)
              ·
                refine ⟨142556226790898297389913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95037484527265531593275 142556226790898297389913)
                ·
                  refine ⟨106917170093173723042435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142556226790898297389913 106917170093173723042435)
                  ·
                    refine ⟨160375755139760584563653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106917170093173723042435 160375755139760584563653)
                    ·
                      refine ⟨30070454088705109605685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 160375755139760584563653 30070454088705109605685)
                      ·
                        rfl

theorem cell23_58562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_58562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58562 prefixEnd_58562 := by exact prefixLift 58562
  have htrace : WordTrace (prefixWord ++ tailWord_58562) baseStart_58562 baseEnd_58562 := by
    simpa [prefixWord, tailWord_58562, baseEnd_58562] using wordTrace_append hprefix tailTrace_58562
  have hstable : (prefixWord ++ tailWord_58562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58562).length < 2 ^ (prefixWord ++ tailWord_58562).sum := by decide
  have hdescent : baseEnd_58562 < baseStart_58562 := by decide
  rcases family_descends (prefixWord ++ tailWord_58562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58581 : List Nat := [1, 3, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_58581 : Nat := 118140960795 + 58581 * 2 ^ 59
def prefixEnd_58581 : Nat := 4983230072969 + 3 ^ 40 * 58581 * 2
def baseEnd_58581 : Nat := 10026736740380178422699

theorem tailTrace_58581 : CollatzResearch.WordTrace tailWord_58581 prefixEnd_58581 10026736740380178422699 := by
  unfold tailWord_58581
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136624600778516683383597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1424416400519011122255731 2136624600778516683383597)
  ·
    refine ⟨801234225291943756268849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2136624600778516683383597 801234225291943756268849)
    ·
      refine ⟨600925668968957817201637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 801234225291943756268849 600925668968957817201637)
      ·
        refine ⟨112673562931679590725307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 600925668968957817201637 112673562931679590725307)
        ·
          refine ⟨169010344397519386087961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112673562931679590725307 169010344397519386087961)
          ·
            refine ⟨126757758298139539565971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169010344397519386087961 126757758298139539565971)
            ·
              refine ⟨190136637447209309348957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126757758298139539565971 190136637447209309348957)
              ·
                refine ⟨71301239042703491005859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190136637447209309348957 71301239042703491005859)
                ·
                  refine ⟨106951858564055236508789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71301239042703491005859 106951858564055236508789)
                  ·
                    refine ⟨10026736740380178422699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106951858564055236508789 10026736740380178422699)
                    ·
                      rfl

theorem cell23_58581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_58581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58581 prefixEnd_58581 := by exact prefixLift 58581
  have htrace : WordTrace (prefixWord ++ tailWord_58581) baseStart_58581 baseEnd_58581 := by
    simpa [prefixWord, tailWord_58581, baseEnd_58581] using wordTrace_append hprefix tailTrace_58581
  have hstable : (prefixWord ++ tailWord_58581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58581).length < 2 ^ (prefixWord ++ tailWord_58581).sum := by decide
  have hdescent : baseEnd_58581 < baseStart_58581 := by decide
  rcases family_descends (prefixWord ++ tailWord_58581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3]
def baseStart_58587 : Nat := 118140960795 + 58587 * 2 ^ 59
def prefixEnd_58587 : Nat := 4983230072969 + 3 ^ 40 * 58587 * 2
def baseEnd_58587 : Nat := 30083291105067511793069

theorem tailTrace_58587 : CollatzResearch.WordTrace tailWord_58587 prefixEnd_58587 30083291105067511793069 := by
  unfold tailWord_58587
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136843438756779708102015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1424562292504519805401343 2136843438756779708102015)
  ·
    refine ⟨3205265158135169562153023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2136843438756779708102015 3205265158135169562153023)
    ·
      refine ⟨4807897737202754343229535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205265158135169562153023 4807897737202754343229535)
      ·
        refine ⟨7211846605804131514844303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807897737202754343229535 7211846605804131514844303)
        ·
          refine ⟨10817769908706197272266455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211846605804131514844303 10817769908706197272266455)
          ·
            refine ⟨16226654863059295908399683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817769908706197272266455 16226654863059295908399683)
            ·
              refine ⟨24339982294588943862599525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16226654863059295908399683 24339982294588943862599525)
              ·
                refine ⟨4563746680235426974237411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24339982294588943862599525 4563746680235426974237411)
                ·
                  refine ⟨6845620020353140461356117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4563746680235426974237411 6845620020353140461356117)
                  ·
                    refine ⟨80222109613513364781517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6845620020353140461356117 80222109613513364781517)
                    ·
                      refine ⟨30083291105067511793069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80222109613513364781517 30083291105067511793069)
                      ·
                        rfl

theorem cell23_58587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].length) (baseStart_58587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58587 prefixEnd_58587 := by exact prefixLift 58587
  have htrace : WordTrace (prefixWord ++ tailWord_58587) baseStart_58587 baseEnd_58587 := by
    simpa [prefixWord, tailWord_58587, baseEnd_58587] using wordTrace_append hprefix tailTrace_58587
  have hstable : (prefixWord ++ tailWord_58587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58587).length < 2 ^ (prefixWord ++ tailWord_58587).sum := by decide
  have hdescent : baseEnd_58587 < baseStart_58587 := by decide
  rcases family_descends (prefixWord ++ tailWord_58587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58604 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_58604 : Nat := 118140960795 + 58604 * 2 ^ 59
def prefixEnd_58604 : Nat := 4983230072969 + 3 ^ 40 * 58604 * 2
def baseEnd_58604 : Nat := 30092020276193945280491

theorem tailTrace_58604 : CollatzResearch.WordTrace tailWord_58604 prefixEnd_58604 30092020276193945280491 := by
  unfold tailWord_58604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068731739847595805735433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1424975653130127740980577 1068731739847595805735433)
  ·
    refine ⟨801548804885696854301575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1068731739847595805735433 801548804885696854301575)
    ·
      refine ⟨1202323207328545281452363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801548804885696854301575 1202323207328545281452363)
      ·
        refine ⟨1803484810992817922178545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202323207328545281452363 1803484810992817922178545)
        ·
          refine ⟨1352613608244613441633909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803484810992817922178545 1352613608244613441633909)
          ·
            refine ⟨126807525772932510153179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1352613608244613441633909 126807525772932510153179)
            ·
              refine ⟨190211288659398765229769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126807525772932510153179 190211288659398765229769)
              ·
                refine ⟨142658466494549073922327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190211288659398765229769 142658466494549073922327)
                ·
                  refine ⟨213987699741823610883491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142658466494549073922327 213987699741823610883491)
                  ·
                    refine ⟨320981549612735416325237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213987699741823610883491 320981549612735416325237)
                    ·
                      refine ⟨30092020276193945280491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 320981549612735416325237 30092020276193945280491)
                      ·
                        rfl

theorem cell23_58604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_58604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58604 prefixEnd_58604 := by exact prefixLift 58604
  have htrace : WordTrace (prefixWord ++ tailWord_58604) baseStart_58604 baseEnd_58604 := by
    simpa [prefixWord, tailWord_58604, baseEnd_58604] using wordTrace_append hprefix tailTrace_58604
  have hstable : (prefixWord ++ tailWord_58604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58604).length < 2 ^ (prefixWord ++ tailWord_58604).sum := by decide
  have hdescent : baseEnd_58604 < baseStart_58604 := by decide
  rcases family_descends (prefixWord ++ tailWord_58604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58634 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_58634 : Nat := 118140960795 + 58634 * 2 ^ 59
def prefixEnd_58634 : Nat := 4983230072969 + 3 ^ 40 * 58634 * 2
def baseEnd_58634 : Nat := 30107424695828827905353

theorem tailTrace_58634 : CollatzResearch.WordTrace tailWord_58634 prefixEnd_58634 30107424695828827905353 := by
  unfold tailWord_58634
  simp only [CollatzResearch.WordTrace]
  refine ⟨534639417396626683765739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1425705113057671156708637 534639417396626683765739)
  ·
    refine ⟨801959126094940025648609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534639417396626683765739 801959126094940025648609)
    ·
      refine ⟨601469344571205019236457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 801959126094940025648609 601469344571205019236457)
      ·
        refine ⟨451102008428403764427343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601469344571205019236457 451102008428403764427343)
        ·
          refine ⟨676653012642605646641015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451102008428403764427343 676653012642605646641015)
          ·
            refine ⟨1014979518963908469961523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676653012642605646641015 1014979518963908469961523)
            ·
              refine ⟨1522469278445862704942285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014979518963908469961523 1522469278445862704942285)
              ·
                refine ⟨570925979417198514353357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522469278445862704942285 570925979417198514353357)
                ·
                  refine ⟨214097242281449442882509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570925979417198514353357 214097242281449442882509)
                  ·
                    refine ⟨80286465855543541080941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214097242281449442882509 80286465855543541080941)
                    ·
                      refine ⟨30107424695828827905353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80286465855543541080941 30107424695828827905353)
                      ·
                        rfl

theorem cell23_58634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_58634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58634 prefixEnd_58634 := by exact prefixLift 58634
  have htrace : WordTrace (prefixWord ++ tailWord_58634) baseStart_58634 baseEnd_58634 := by
    simpa [prefixWord, tailWord_58634, baseEnd_58634] using wordTrace_append hprefix tailTrace_58634
  have hstable : (prefixWord ++ tailWord_58634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58634).length < 2 ^ (prefixWord ++ tailWord_58634).sum := by decide
  have hdescent : baseEnd_58634 < baseStart_58634 := by decide
  rcases family_descends (prefixWord ++ tailWord_58634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58635 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 1, 2, 2]
def baseStart_58635 : Nat := 118140960795 + 58635 * 2 ^ 59
def prefixEnd_58635 : Nat := 4983230072969 + 3 ^ 40 * 58635 * 2
def baseEnd_58635 : Nat := 30107938176483323992849

theorem tailTrace_58635 : CollatzResearch.WordTrace tailWord_58635 prefixEnd_58635 30107938176483323992849 := by
  unfold tailWord_58635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138594142582883905849359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1425729428388589270566239 2138594142582883905849359)
  ·
    refine ⟨3207891213874325858774039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138594142582883905849359 3207891213874325858774039)
    ·
      refine ⟨4811836820811488788161059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207891213874325858774039 4811836820811488788161059)
      ·
        refine ⟨7217755231217233182241589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811836820811488788161059 7217755231217233182241589)
        ·
          refine ⟨676664552926615610835149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7217755231217233182241589 676664552926615610835149)
          ·
            refine ⟨253749207347480854063181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676664552926615610835149 253749207347480854063181)
            ·
              refine ⟨95155952755305320273693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253749207347480854063181 95155952755305320273693)
              ·
                refine ⟨35683482283239495102635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95155952755305320273693 35683482283239495102635)
                ·
                  refine ⟨53525223424859242653953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35683482283239495102635 53525223424859242653953)
                  ·
                    refine ⟨40143917568644431990465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53525223424859242653953 40143917568644431990465)
                    ·
                      refine ⟨30107938176483323992849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40143917568644431990465 30107938176483323992849)
                      ·
                        rfl

theorem cell23_58635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 2, 2].length) (baseStart_58635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58635 prefixEnd_58635 := by exact prefixLift 58635
  have htrace : WordTrace (prefixWord ++ tailWord_58635) baseStart_58635 baseEnd_58635 := by
    simpa [prefixWord, tailWord_58635, baseEnd_58635] using wordTrace_append hprefix tailTrace_58635
  have hstable : (prefixWord ++ tailWord_58635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58635).length < 2 ^ (prefixWord ++ tailWord_58635).sum := by decide
  have hdescent : baseEnd_58635 < baseStart_58635 := by decide
  rcases family_descends (prefixWord ++ tailWord_58635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58651 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 3]
def baseStart_58651 : Nat := 118140960795 + 58651 * 2 ^ 59
def prefixEnd_58651 : Nat := 4983230072969 + 3 ^ 40 * 58651 * 2
def baseEnd_58651 : Nat := 30116153866955261392775

theorem tailTrace_58651 : CollatzResearch.WordTrace tailWord_58651 prefixEnd_58651 30116153866955261392775 := by
  unfold tailWord_58651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139177710524918638431807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1426118473683279092287871 2139177710524918638431807)
  ·
    refine ⟨3208766565787377957647711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2139177710524918638431807 3208766565787377957647711)
    ·
      refine ⟨4813149848681066936471567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208766565787377957647711 4813149848681066936471567)
      ·
        refine ⟨7219724773021600404707351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813149848681066936471567 7219724773021600404707351)
        ·
          refine ⟨10829587159532400607061027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219724773021600404707351 10829587159532400607061027)
          ·
            refine ⟨16244380739298600910591541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10829587159532400607061027 16244380739298600910591541)
            ·
              refine ⟨1522910694309243835367957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16244380739298600910591541 1522910694309243835367957)
              ·
                refine ⟨71386438795745804782873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1522910694309243835367957 71386438795745804782873)
                ·
                  refine ⟨53539829096809353587155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71386438795745804782873 53539829096809353587155)
                  ·
                    refine ⟨80309743645214030380733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53539829096809353587155 80309743645214030380733)
                    ·
                      refine ⟨30116153866955261392775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80309743645214030380733 30116153866955261392775)
                      ·
                        rfl

theorem cell23_58651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 3].length) (baseStart_58651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58651 prefixEnd_58651 := by exact prefixLift 58651
  have htrace : WordTrace (prefixWord ++ tailWord_58651) baseStart_58651 baseEnd_58651 := by
    simpa [prefixWord, tailWord_58651, baseEnd_58651] using wordTrace_append hprefix tailTrace_58651
  have hstable : (prefixWord ++ tailWord_58651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58651).length < 2 ^ (prefixWord ++ tailWord_58651).sum := by decide
  have hdescent : baseEnd_58651 < baseStart_58651 := by decide
  rcases family_descends (prefixWord ++ tailWord_58651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58695 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_58695 : Nat := 118140960795 + 58695 * 2 ^ 59
def prefixEnd_58695 : Nat := 4983230072969 + 3 ^ 40 * 58695 * 2
def baseEnd_58695 : Nat := 30138747015753089242573

theorem tailTrace_58695 : CollatzResearch.WordTrace tailWord_58695 prefixEnd_58695 30138747015753089242573 := by
  unfold tailWord_58695
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140782522365514153033539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1427188348243676102022359 2140782522365514153033539)
  ·
    refine ⟨3211173783548271229550309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140782522365514153033539 3211173783548271229550309)
    ·
      refine ⟨602095084415300855540683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3211173783548271229550309 602095084415300855540683)
      ·
        refine ⟨903142626622951283311025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602095084415300855540683 903142626622951283311025)
        ·
          refine ⟨677356969967213462483269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903142626622951283311025 677356969967213462483269)
          ·
            refine ⟨127004431868852524215613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 677356969967213462483269 127004431868852524215613)
            ·
              refine ⟨47626661950819696580855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127004431868852524215613 47626661950819696580855)
              ·
                refine ⟨71439992926229544871283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47626661950819696580855 71439992926229544871283)
                ·
                  refine ⟨107159989389344317306925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71439992926229544871283 107159989389344317306925)
                  ·
                    refine ⟨40184996021004118990097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107159989389344317306925 40184996021004118990097)
                    ·
                      refine ⟨30138747015753089242573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40184996021004118990097 30138747015753089242573)
                      ·
                        rfl

theorem cell23_58695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_58695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58695 prefixEnd_58695 := by exact prefixLift 58695
  have htrace : WordTrace (prefixWord ++ tailWord_58695) baseStart_58695 baseEnd_58695 := by
    simpa [prefixWord, tailWord_58695, baseEnd_58695] using wordTrace_append hprefix tailTrace_58695
  have hstable : (prefixWord ++ tailWord_58695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58695).length < 2 ^ (prefixWord ++ tailWord_58695).sum := by decide
  have hdescent : baseEnd_58695 < baseStart_58695 := by decide
  rcases family_descends (prefixWord ++ tailWord_58695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58704 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_58704 : Nat := 118140960795 + 58704 * 2 ^ 59
def prefixEnd_58704 : Nat := 4983230072969 + 3 ^ 40 * 58704 * 2
def baseEnd_58704 : Nat := 30143368341643554030031

theorem tailTrace_58704 : CollatzResearch.WordTrace tailWord_58704 prefixEnd_58704 30143368341643554030031 := by
  unfold tailWord_58704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070555389666454345055583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1427407186221939126740777 1070555389666454345055583)
  ·
    refine ⟨1605833084499681517583375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070555389666454345055583 1605833084499681517583375)
    ·
      refine ⟨2408749626749522276375063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605833084499681517583375 2408749626749522276375063)
      ·
        refine ⟨3613124440124283414562595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408749626749522276375063 3613124440124283414562595)
        ·
          refine ⟨5419686660186425121843893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613124440124283414562595 5419686660186425121843893)
          ·
            refine ⟨508095624392477355172865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5419686660186425121843893 508095624392477355172865)
            ·
              refine ⟨381071718294358016379649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508095624392477355172865 381071718294358016379649)
              ·
                refine ⟨285803788720768512284737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381071718294358016379649 285803788720768512284737)
                ·
                  refine ⟨214352841540576384213553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285803788720768512284737 214352841540576384213553)
                  ·
                    refine ⟨160764631155432288160165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214352841540576384213553 160764631155432288160165)
                    ·
                      refine ⟨30143368341643554030031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 160764631155432288160165 30143368341643554030031)
                      ·
                        rfl

theorem cell23_58704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_58704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58704 prefixEnd_58704 := by exact prefixLift 58704
  have htrace : WordTrace (prefixWord ++ tailWord_58704) baseStart_58704 baseEnd_58704 := by
    simpa [prefixWord, tailWord_58704, baseEnd_58704] using wordTrace_append hprefix tailTrace_58704
  have hstable : (prefixWord ++ tailWord_58704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58704).length < 2 ^ (prefixWord ++ tailWord_58704).sum := by decide
  have hdescent : baseEnd_58704 < baseStart_58704 := by decide
  rcases family_descends (prefixWord ++ tailWord_58704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58781 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_58781 : Nat := 118140960795 + 58781 * 2 ^ 59
def prefixEnd_58781 : Nat := 4983230072969 + 3 ^ 40 * 58781 * 2
def baseEnd_58781 : Nat := 30182906352039752767177

theorem tailTrace_58781 : CollatzResearch.WordTrace tailWord_58781 prefixEnd_58781 30182906352039752767177 := by
  unfold tailWord_58781
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143919200053950840664197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1429279466702633893776131 2143919200053950840664197)
  ·
    refine ⟨401984850010115782624537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2143919200053950840664197 401984850010115782624537)
    ·
      refine ⟨301488637507586836968403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401984850010115782624537 301488637507586836968403)
      ·
        refine ⟨452232956261380255452605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301488637507586836968403 452232956261380255452605)
        ·
          refine ⟨169587358598017595794727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452232956261380255452605 169587358598017595794727)
          ·
            refine ⟨254381037897026393692091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169587358598017595794727 254381037897026393692091)
            ·
              refine ⟨381571556845539590538137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254381037897026393692091 381571556845539590538137)
              ·
                refine ⟨286178667634154692903603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381571556845539590538137 286178667634154692903603)
                ·
                  refine ⟨429268001451232039355405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286178667634154692903603 429268001451232039355405)
                  ·
                    refine ⟨160975500544212014758277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429268001451232039355405 160975500544212014758277)
                    ·
                      refine ⟨30182906352039752767177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 160975500544212014758277 30182906352039752767177)
                      ·
                        rfl

theorem cell23_58781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_58781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58781 prefixEnd_58781 := by exact prefixLift 58781
  have htrace : WordTrace (prefixWord ++ tailWord_58781) baseStart_58781 baseEnd_58781 := by
    simpa [prefixWord, tailWord_58781, baseEnd_58781] using wordTrace_append hprefix tailTrace_58781
  have hstable : (prefixWord ++ tailWord_58781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58781).length < 2 ^ (prefixWord ++ tailWord_58781).sum := by decide
  have hdescent : baseEnd_58781 < baseStart_58781 := by decide
  rcases family_descends (prefixWord ++ tailWord_58781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58801 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_58801 : Nat := 118140960795 + 58801 * 2 ^ 59
def prefixEnd_58801 : Nat := 4983230072969 + 3 ^ 40 * 58801 * 2
def baseEnd_58801 : Nat := 30193175965129674517085

theorem tailTrace_58801 : CollatzResearch.WordTrace tailWord_58801 prefixEnd_58801 30193175965129674517085 := by
  unfold tailWord_58801
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144648659981494256392257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1429765773320996170928171 2144648659981494256392257)
  ·
    refine ⟨1608486494986120692294193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2144648659981494256392257 1608486494986120692294193)
    ·
      refine ⟨1206364871239590519220645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1608486494986120692294193 1206364871239590519220645)
      ·
        refine ⟨226193413357423222353871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1206364871239590519220645 226193413357423222353871)
        ·
          refine ⟨339290120036134833530807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226193413357423222353871 339290120036134833530807)
          ·
            refine ⟨508935180054202250296211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339290120036134833530807 508935180054202250296211)
            ·
              refine ⟨763402770081303375444317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508935180054202250296211 763402770081303375444317)
              ·
                refine ⟨286276038780488765791619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763402770081303375444317 286276038780488765791619)
                ·
                  refine ⟨429414058170733148687429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286276038780488765791619 429414058170733148687429)
                  ·
                    refine ⟨80515135907012465378893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429414058170733148687429 80515135907012465378893)
                    ·
                      refine ⟨30193175965129674517085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80515135907012465378893 30193175965129674517085)
                      ·
                        rfl

theorem cell23_58801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_58801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58801 prefixEnd_58801 := by exact prefixLift 58801
  have htrace : WordTrace (prefixWord ++ tailWord_58801) baseStart_58801 baseEnd_58801 := by
    simpa [prefixWord, tailWord_58801, baseEnd_58801] using wordTrace_append hprefix tailTrace_58801
  have hstable : (prefixWord ++ tailWord_58801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58801).length < 2 ^ (prefixWord ++ tailWord_58801).sum := by decide
  have hdescent : baseEnd_58801 < baseStart_58801 := by decide
  rcases family_descends (prefixWord ++ tailWord_58801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58908 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_58908 : Nat := 118140960795 + 58908 * 2 ^ 59
def prefixEnd_58908 : Nat := 4983230072969 + 3 ^ 40 * 58908 * 2
def baseEnd_58908 : Nat := 30248118395160755879093

theorem tailTrace_58908 : CollatzResearch.WordTrace tailWord_58908 prefixEnd_58908 30248118395160755879093 := by
  unfold tailWord_58908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074275635296925765268689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1432367513729234353691585 1074275635296925765268689)
  ·
    refine ⟨805706726472694323951517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1074275635296925765268689 805706726472694323951517)
    ·
      refine ⟨302140022427260371481819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 805706726472694323951517 302140022427260371481819)
      ·
        refine ⟨453210033640890557222729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302140022427260371481819 453210033640890557222729)
        ·
          refine ⟨339907525230667917917047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453210033640890557222729 339907525230667917917047)
          ·
            refine ⟨509861287846001876875571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339907525230667917917047 509861287846001876875571)
            ·
              refine ⟨764791931769002815313357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509861287846001876875571 764791931769002815313357)
              ·
                refine ⟨286796974413376055742509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 764791931769002815313357 286796974413376055742509)
                ·
                  refine ⟨107548865405016020903441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286796974413376055742509 107548865405016020903441)
                  ·
                    refine ⟨80661649053762015677581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107548865405016020903441 80661649053762015677581)
                    ·
                      refine ⟨30248118395160755879093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80661649053762015677581 30248118395160755879093)
                      ·
                        rfl

theorem cell23_58908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_58908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_58908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_58908 prefixEnd_58908 := by exact prefixLift 58908
  have htrace : WordTrace (prefixWord ++ tailWord_58908) baseStart_58908 baseEnd_58908 := by
    simpa [prefixWord, tailWord_58908, baseEnd_58908] using wordTrace_append hprefix tailTrace_58908
  have hstable : (prefixWord ++ tailWord_58908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58908).length < 2 ^ (prefixWord ++ tailWord_58908).sum := by decide
  have hdescent : baseEnd_58908 < baseStart_58908 := by decide
  rcases family_descends (prefixWord ++ tailWord_58908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59016 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_59016 : Nat := 118140960795 + 59016 * 2 ^ 59
def prefixEnd_59016 : Nat := 4983230072969 + 3 ^ 40 * 59016 * 2
def baseEnd_59016 : Nat := 30303574305846333328597

theorem tailTrace_59016 : CollatzResearch.WordTrace tailWord_59016 prefixEnd_59016 30303574305846333328597 := by
  unfold tailWord_59016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076245177101292987734451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1434993569468390650312601 1076245177101292987734451)
  ·
    refine ⟨1614367765651939481601677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076245177101292987734451 1614367765651939481601677)
    ·
      refine ⟨605387912119477305600629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1614367765651939481601677 605387912119477305600629)
      ·
        refine ⟨56755116761200997400059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 605387912119477305600629 56755116761200997400059)
        ·
          refine ⟨85132675141801496100089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56755116761200997400059 85132675141801496100089)
          ·
            refine ⟨63849506356351122075067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85132675141801496100089 63849506356351122075067)
            ·
              refine ⟨95774259534526683112601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63849506356351122075067 95774259534526683112601)
              ·
                refine ⟨71830694650895012334451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95774259534526683112601 71830694650895012334451)
                ·
                  refine ⟨107746041976342518501677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71830694650895012334451 107746041976342518501677)
                  ·
                    refine ⟨40404765741128444438129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107746041976342518501677 40404765741128444438129)
                    ·
                      refine ⟨30303574305846333328597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40404765741128444438129 30303574305846333328597)
                      ·
                        rfl

theorem cell23_59016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_59016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59016 prefixEnd_59016 := by exact prefixLift 59016
  have htrace : WordTrace (prefixWord ++ tailWord_59016) baseStart_59016 baseEnd_59016 := by
    simpa [prefixWord, tailWord_59016, baseEnd_59016] using wordTrace_append hprefix tailTrace_59016
  have hstable : (prefixWord ++ tailWord_59016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59016).length < 2 ^ (prefixWord ++ tailWord_59016).sum := by decide
  have hdescent : baseEnd_59016 < baseStart_59016 := by decide
  rcases family_descends (prefixWord ++ tailWord_59016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59058 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_59058 : Nat := 118140960795 + 59058 * 2 ^ 59
def prefixEnd_59058 : Nat := 4983230072969 + 3 ^ 40 * 59058 * 2
def baseEnd_59058 : Nat := 30325140493335169003403

theorem tailTrace_59058 : CollatzResearch.WordTrace tailWord_59058 prefixEnd_59058 30325140493335169003403 := by
  unfold tailWord_59058
  simp only [CollatzResearch.WordTrace]
  refine ⟨538505555012606787124457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1436014813366951432331885 538505555012606787124457)
  ·
    refine ⟨403879166259455090343343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538505555012606787124457 403879166259455090343343)
    ·
      refine ⟨605818749389182635515015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403879166259455090343343 605818749389182635515015)
      ·
        refine ⟨908728124083773953272523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605818749389182635515015 908728124083773953272523)
        ·
          refine ⟨1363092186125660929908785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908728124083773953272523 1363092186125660929908785)
          ·
            refine ⟨1022319139594245697431589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363092186125660929908785 1022319139594245697431589)
            ·
              refine ⟨191684838673921068268423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1022319139594245697431589 191684838673921068268423)
              ·
                refine ⟨287527258010881602402635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191684838673921068268423 287527258010881602402635)
                ·
                  refine ⟨431290887016322403603953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287527258010881602402635 431290887016322403603953)
                  ·
                    refine ⟨323468165262241802702965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 431290887016322403603953 323468165262241802702965)
                    ·
                      refine ⟨30325140493335169003403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 323468165262241802702965 30325140493335169003403)
                      ·
                        rfl

theorem cell23_59058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_59058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59058 prefixEnd_59058 := by exact prefixLift 59058
  have htrace : WordTrace (prefixWord ++ tailWord_59058) baseStart_59058 baseEnd_59058 := by
    simpa [prefixWord, tailWord_59058, baseEnd_59058] using wordTrace_append hprefix tailTrace_59058
  have hstable : (prefixWord ++ tailWord_59058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59058).length < 2 ^ (prefixWord ++ tailWord_59058).sum := by decide
  have hdescent : baseEnd_59058 < baseStart_59058 := by decide
  rcases family_descends (prefixWord ++ tailWord_59058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59062 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_59062 : Nat := 118140960795 + 59062 * 2 ^ 59
def prefixEnd_59062 : Nat := 4983230072969 + 3 ^ 40 * 59062 * 2
def baseEnd_59062 : Nat := 30327194415953153353385

theorem tailTrace_59062 : CollatzResearch.WordTrace tailWord_59062 prefixEnd_59062 30327194415953153353385 := by
  unfold tailWord_59062
  simp only [CollatzResearch.WordTrace]
  refine ⟨134635507002245989477715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1436112074690623887762293 134635507002245989477715)
  ·
    refine ⟨201953260503368984216573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134635507002245989477715 201953260503368984216573)
    ·
      refine ⟨75732472688763369081215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201953260503368984216573 75732472688763369081215)
      ·
        refine ⟨113598709033145053621823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75732472688763369081215 113598709033145053621823)
        ·
          refine ⟨170398063549717580432735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113598709033145053621823 170398063549717580432735)
          ·
            refine ⟨255597095324576370649103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170398063549717580432735 255597095324576370649103)
            ·
              refine ⟨383395642986864555973655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255597095324576370649103 383395642986864555973655)
              ·
                refine ⟨575093464480296833960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383395642986864555973655 575093464480296833960483)
                ·
                  refine ⟨862640196720445250940725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575093464480296833960483 862640196720445250940725)
                  ·
                    refine ⟨80872518442541742275693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 862640196720445250940725 80872518442541742275693)
                    ·
                      refine ⟨30327194415953153353385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 80872518442541742275693 30327194415953153353385)
                      ·
                        rfl

theorem cell23_59062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_59062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59062 prefixEnd_59062 := by exact prefixLift 59062
  have htrace : WordTrace (prefixWord ++ tailWord_59062) baseStart_59062 baseEnd_59062 := by
    simpa [prefixWord, tailWord_59062, baseEnd_59062] using wordTrace_append hprefix tailTrace_59062
  have hstable : (prefixWord ++ tailWord_59062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59062).length < 2 ^ (prefixWord ++ tailWord_59062).sum := by decide
  have hdescent : baseEnd_59062 < baseStart_59062 := by decide
  rcases family_descends (prefixWord ++ tailWord_59062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59082 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_59082 : Nat := 118140960795 + 59082 * 2 ^ 59
def prefixEnd_59082 : Nat := 4983230072969 + 3 ^ 40 * 59082 * 2
def baseEnd_59082 : Nat := 10112488009681025034431

theorem tailTrace_59082 : CollatzResearch.WordTrace tailWord_59082 prefixEnd_59082 10112488009681025034431 := by
  unfold tailWord_59082
  simp only [CollatzResearch.WordTrace]
  refine ⟨538724392990869811842875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1436598381308986164914333 538724392990869811842875)
  ·
    refine ⟨808086589486304717764313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538724392990869811842875 808086589486304717764313)
    ·
      refine ⟨606064942114728538323235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 808086589486304717764313 606064942114728538323235)
      ·
        refine ⟨909097413172092807484853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606064942114728538323235 909097413172092807484853)
        ·
          refine ⟨85227882484883700701705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 909097413172092807484853 85227882484883700701705)
          ·
            refine ⟨63920911863662775526279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85227882484883700701705 63920911863662775526279)
            ·
              refine ⟨95881367795494163289419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63920911863662775526279 95881367795494163289419)
              ·
                refine ⟨143822051693241244934129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95881367795494163289419 143822051693241244934129)
                ·
                  refine ⟨107866538769930933700597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143822051693241244934129 107866538769930933700597)
                  ·
                    refine ⟨10112488009681025034431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107866538769930933700597 10112488009681025034431)
                    ·
                      rfl

theorem cell23_59082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_59082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59082 prefixEnd_59082 := by exact prefixLift 59082
  have htrace : WordTrace (prefixWord ++ tailWord_59082) baseStart_59082 baseEnd_59082 := by
    simpa [prefixWord, tailWord_59082, baseEnd_59082] using wordTrace_append hprefix tailTrace_59082
  have hstable : (prefixWord ++ tailWord_59082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59082).length < 2 ^ (prefixWord ++ tailWord_59082).sum := by decide
  have hdescent : baseEnd_59082 < baseStart_59082 := by decide
  rcases family_descends (prefixWord ++ tailWord_59082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59098 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_59098 : Nat := 118140960795 + 59098 * 2 ^ 59
def prefixEnd_59098 : Nat := 4983230072969 + 3 ^ 40 * 59098 * 2
def baseEnd_59098 : Nat := 30345679719515012503219

theorem tailTrace_59098 : CollatzResearch.WordTrace tailWord_59098 prefixEnd_59098 30345679719515012503219 := by
  unfold tailWord_59098
  simp only [CollatzResearch.WordTrace]
  refine ⟨538870284976378494988487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1436987426603675986635965 538870284976378494988487)
  ·
    refine ⟨808305427464567742482731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538870284976378494988487 808305427464567742482731)
    ·
      refine ⟨1212458141196851613724097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808305427464567742482731 1212458141196851613724097)
      ·
        refine ⟨909343605897638710293073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212458141196851613724097 909343605897638710293073)
        ·
          refine ⟨682007704423229032719805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909343605897638710293073 682007704423229032719805)
          ·
            refine ⟨255752889158710887269927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682007704423229032719805 255752889158710887269927)
            ·
              refine ⟨383629333738066330904891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255752889158710887269927 383629333738066330904891)
              ·
                refine ⟨575444000607099496357337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383629333738066330904891 575444000607099496357337)
                ·
                  refine ⟨431583000455324622268003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 575444000607099496357337 431583000455324622268003)
                  ·
                    refine ⟨647374500682986933402005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 431583000455324622268003 647374500682986933402005)
                    ·
                      refine ⟨30345679719515012503219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 647374500682986933402005 30345679719515012503219)
                      ·
                        rfl

theorem cell23_59098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_59098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59098 prefixEnd_59098 := by exact prefixLift 59098
  have htrace : WordTrace (prefixWord ++ tailWord_59098) baseStart_59098 baseEnd_59098 := by
    simpa [prefixWord, tailWord_59098, baseEnd_59098] using wordTrace_append hprefix tailTrace_59098
  have hstable : (prefixWord ++ tailWord_59098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59098).length < 2 ^ (prefixWord ++ tailWord_59098).sum := by decide
  have hdescent : baseEnd_59098 < baseStart_59098 := by decide
  rcases family_descends (prefixWord ++ tailWord_59098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59108 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 8]
def baseStart_59108 : Nat := 118140960795 + 59108 * 2 ^ 59
def prefixEnd_59108 : Nat := 4983230072969 + 3 ^ 40 * 59108 * 2
def baseEnd_59108 : Nat := 3372312725117774819797

theorem tailTrace_59108 : CollatzResearch.WordTrace tailWord_59108 prefixEnd_59108 3372312725117774819797 := by
  unfold tailWord_59108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077922934934642843908989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1437230579912857125211985 1077922934934642843908989)
  ·
    refine ⟨404221100600491066465871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1077922934934642843908989 404221100600491066465871)
    ·
      refine ⟨606331650900736599698807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404221100600491066465871 606331650900736599698807)
      ·
        refine ⟨909497476351104899548211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606331650900736599698807 909497476351104899548211)
        ·
          refine ⟨1364246214526657349322317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909497476351104899548211 1364246214526657349322317)
          ·
            refine ⟨511592330447496505995869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1364246214526657349322317 511592330447496505995869)
            ·
              refine ⟨191847123917811189748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511592330447496505995869 191847123917811189748451)
              ·
                refine ⟨287770685876716784622677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191847123917811189748451 287770685876716784622677)
                ·
                  refine ⟨3372312725117774819797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 287770685876716784622677 3372312725117774819797)
                  ·
                    rfl

theorem cell23_59108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_59108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59108 prefixEnd_59108 := by exact prefixLift 59108
  have htrace : WordTrace (prefixWord ++ tailWord_59108) baseStart_59108 baseEnd_59108 := by
    simpa [prefixWord, tailWord_59108, baseEnd_59108] using wordTrace_append hprefix tailTrace_59108
  have hstable : (prefixWord ++ tailWord_59108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59108).length < 2 ^ (prefixWord ++ tailWord_59108).sum := by decide
  have hdescent : baseEnd_59108 < baseStart_59108 := by decide
  rcases family_descends (prefixWord ++ tailWord_59108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59112 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_59112 : Nat := 118140960795 + 59112 * 2 ^ 59
def prefixEnd_59112 : Nat := 4983230072969 + 3 ^ 40 * 59112 * 2
def baseEnd_59112 : Nat := 10117622816225985909385

theorem tailTrace_59112 : CollatzResearch.WordTrace tailWord_59112 prefixEnd_59112 10117622816225985909385 := by
  unfold tailWord_59112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077995880927397185481795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1437327841236529580642393 1077995880927397185481795)
  ·
    refine ⟨1616993821391095778222693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077995880927397185481795 1616993821391095778222693)
    ·
      refine ⟨303186341510830458416755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1616993821391095778222693 303186341510830458416755)
      ·
        refine ⟨454779512266245687625133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303186341510830458416755 454779512266245687625133)
        ·
          refine ⟨170542317099842132859425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454779512266245687625133 170542317099842132859425)
          ·
            refine ⟨127906737824881599644569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170542317099842132859425 127906737824881599644569)
            ·
              refine ⟨95930053368661199733427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127906737824881599644569 95930053368661199733427)
              ·
                refine ⟨143895080052991799600141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95930053368661199733427 143895080052991799600141)
                ·
                  refine ⟨53960655019871924850053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143895080052991799600141 53960655019871924850053)
                  ·
                    refine ⟨10117622816225985909385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53960655019871924850053 10117622816225985909385)
                    ·
                      rfl

theorem cell23_59112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_59112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59112 prefixEnd_59112 := by exact prefixLift 59112
  have htrace : WordTrace (prefixWord ++ tailWord_59112) baseStart_59112 baseEnd_59112 := by
    simpa [prefixWord, tailWord_59112, baseEnd_59112] using wordTrace_append hprefix tailTrace_59112
  have hstable : (prefixWord ++ tailWord_59112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59112).length < 2 ^ (prefixWord ++ tailWord_59112).sum := by decide
  have hdescent : baseEnd_59112 < baseStart_59112 := by decide
  rcases family_descends (prefixWord ++ tailWord_59112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59162 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_59162 : Nat := 118140960795 + 59162 * 2 ^ 59
def prefixEnd_59162 : Nat := 4983230072969 + 3 ^ 40 * 59162 * 2
def baseEnd_59162 : Nat := 30378542481402762102925

theorem tailTrace_59162 : CollatzResearch.WordTrace tailWord_59162 prefixEnd_59162 30378542481402762102925 := by
  unfold tailWord_59162
  simp only [CollatzResearch.WordTrace]
  refine ⟨539453852918413227570935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1438543607782435273522493 539453852918413227570935)
  ·
    refine ⟨809180779377619841356403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 539453852918413227570935 809180779377619841356403)
    ·
      refine ⟨1213771169066429762034605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809180779377619841356403 1213771169066429762034605)
      ·
        refine ⟨455164188399911160762977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1213771169066429762034605 455164188399911160762977)
        ·
          refine ⟨341373141299933370572233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455164188399911160762977 341373141299933370572233)
          ·
            refine ⟨256029855974950027929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341373141299933370572233 256029855974950027929175)
            ·
              refine ⟨384044783962425041893763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256029855974950027929175 384044783962425041893763)
              ·
                refine ⟨576067175943637562840645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384044783962425041893763 576067175943637562840645)
                ·
                  refine ⟨108012595489432043032621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576067175943637562840645 108012595489432043032621)
                  ·
                    refine ⟨40504723308537016137233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108012595489432043032621 40504723308537016137233)
                    ·
                      refine ⟨30378542481402762102925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40504723308537016137233 30378542481402762102925)
                      ·
                        rfl

theorem cell23_59162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_59162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59162 prefixEnd_59162 := by exact prefixLift 59162
  have htrace : WordTrace (prefixWord ++ tailWord_59162) baseStart_59162 baseEnd_59162 := by
    simpa [prefixWord, tailWord_59162, baseEnd_59162] using wordTrace_append hprefix tailTrace_59162
  have hstable : (prefixWord ++ tailWord_59162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59162).length < 2 ^ (prefixWord ++ tailWord_59162).sum := by decide
  have hdescent : baseEnd_59162 < baseStart_59162 := by decide
  rcases family_descends (prefixWord ++ tailWord_59162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59169 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_59169 : Nat := 118140960795 + 59169 * 2 ^ 59
def prefixEnd_59169 : Nat := 4983230072969 + 3 ^ 40 * 59169 * 2
def baseEnd_59169 : Nat := 30382136845984234715393

theorem tailTrace_59169 : CollatzResearch.WordTrace tailWord_59169 prefixEnd_59169 30382136845984234715393 := by
  unfold tailWord_59169
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158070722648293105788561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1438713815098862070525707 2158070722648293105788561)
  ·
    refine ⟨1618553041986219829341421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2158070722648293105788561 1618553041986219829341421)
    ·
      refine ⟨606957390744832436003033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1618553041986219829341421 606957390744832436003033)
      ·
        refine ⟨455218043058624327002275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606957390744832436003033 455218043058624327002275)
        ·
          refine ⟨682827064587936490503413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455218043058624327002275 682827064587936490503413)
          ·
            refine ⟨64015037305119045984695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 682827064587936490503413 64015037305119045984695)
            ·
              refine ⟨96022555957678568977043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64015037305119045984695 96022555957678568977043)
              ·
                refine ⟨144033833936517853465565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96022555957678568977043 144033833936517853465565)
                ·
                  refine ⟨54012687726194195049587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144033833936517853465565 54012687726194195049587)
                  ·
                    refine ⟨81019031589291292574381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54012687726194195049587 81019031589291292574381)
                    ·
                      refine ⟨30382136845984234715393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81019031589291292574381 30382136845984234715393)
                      ·
                        rfl

theorem cell23_59169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_59169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59169 prefixEnd_59169 := by exact prefixLift 59169
  have htrace : WordTrace (prefixWord ++ tailWord_59169) baseStart_59169 baseEnd_59169 := by
    simpa [prefixWord, tailWord_59169, baseEnd_59169] using wordTrace_append hprefix tailTrace_59169
  have hstable : (prefixWord ++ tailWord_59169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59169).length < 2 ^ (prefixWord ++ tailWord_59169).sum := by decide
  have hdescent : baseEnd_59169 < baseStart_59169 := by decide
  rcases family_descends (prefixWord ++ tailWord_59169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59189 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_59189 : Nat := 118140960795 + 59189 * 2 ^ 59
def prefixEnd_59189 : Nat := 4983230072969 + 3 ^ 40 * 59189 * 2
def baseEnd_59189 : Nat := 10130802153024718821767

theorem tailTrace_59189 : CollatzResearch.WordTrace tailWord_59189 prefixEnd_59189 10130802153024718821767 := by
  unfold tailWord_59189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158800182575836521516621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1439200121717224347677747 2158800182575836521516621)
  ·
    refine ⟨809550068465938695568733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2158800182575836521516621 809550068465938695568733)
    ·
      refine ⟨303581275674727010838275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 809550068465938695568733 303581275674727010838275)
      ·
        refine ⟨455371913512090516257413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303581275674727010838275 455371913512090516257413)
        ·
          refine ⟨85382233783516971798265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455371913512090516257413 85382233783516971798265)
          ·
            refine ⟨64036675337637728848699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85382233783516971798265 64036675337637728848699)
            ·
              refine ⟨96055013006456593273049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64036675337637728848699 96055013006456593273049)
              ·
                refine ⟨72041259754842444954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96055013006456593273049 72041259754842444954787)
                ·
                  refine ⟨108061889632263667432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72041259754842444954787 108061889632263667432181)
                  ·
                    refine ⟨10130802153024718821767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108061889632263667432181 10130802153024718821767)
                    ·
                      rfl

theorem cell23_59189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_59189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59189 prefixEnd_59189 := by exact prefixLift 59189
  have htrace : WordTrace (prefixWord ++ tailWord_59189) baseStart_59189 baseEnd_59189 := by
    simpa [prefixWord, tailWord_59189, baseEnd_59189] using wordTrace_append hprefix tailTrace_59189
  have hstable : (prefixWord ++ tailWord_59189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59189).length < 2 ^ (prefixWord ++ tailWord_59189).sum := by decide
  have hdescent : baseEnd_59189 < baseStart_59189 := by decide
  rcases family_descends (prefixWord ++ tailWord_59189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59192 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_59192 : Nat := 118140960795 + 59192 * 2 ^ 59
def prefixEnd_59192 : Nat := 4983230072969 + 3 ^ 40 * 59192 * 2
def baseEnd_59192 : Nat := 30393946901037644727787

theorem tailTrace_59192 : CollatzResearch.WordTrace tailWord_59192 prefixEnd_59192 30393946901037644727787 := by
  unfold tailWord_59192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079454800782484016937915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1439273067709978689250553 1079454800782484016937915)
  ·
    refine ⟨1619182201173726025406873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1079454800782484016937915 1619182201173726025406873)
    ·
      refine ⟨1214386650880294519055155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1619182201173726025406873 1214386650880294519055155)
      ·
        refine ⟨1821579976320441778582733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214386650880294519055155 1821579976320441778582733)
        ·
          refine ⟨683092491120165666968525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1821579976320441778582733 683092491120165666968525)
          ·
            refine ⟨256159684170062125113197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683092491120165666968525 256159684170062125113197)
            ·
              refine ⟨96059881563773296917449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256159684170062125113197 96059881563773296917449)
              ·
                refine ⟨72044911172829972688087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96059881563773296917449 72044911172829972688087)
                ·
                  refine ⟨108067366759244959032131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72044911172829972688087 108067366759244959032131)
                  ·
                    refine ⟨162101050138867438548197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108067366759244959032131 162101050138867438548197)
                    ·
                      refine ⟨30393946901037644727787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 162101050138867438548197 30393946901037644727787)
                      ·
                        rfl

theorem cell23_59192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_59192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59192 prefixEnd_59192 := by exact prefixLift 59192
  have htrace : WordTrace (prefixWord ++ tailWord_59192) baseStart_59192 baseEnd_59192 := by
    simpa [prefixWord, tailWord_59192, baseEnd_59192] using wordTrace_append hprefix tailTrace_59192
  have hstable : (prefixWord ++ tailWord_59192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59192).length < 2 ^ (prefixWord ++ tailWord_59192).sum := by decide
  have hdescent : baseEnd_59192 < baseStart_59192 := by decide
  rcases family_descends (prefixWord ++ tailWord_59192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59205 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_59205 : Nat := 118140960795 + 59205 * 2 ^ 59
def prefixEnd_59205 : Nat := 4983230072969 + 3 ^ 40 * 59205 * 2
def baseEnd_59205 : Nat := 30400622149546093865227

theorem tailTrace_59205 : CollatzResearch.WordTrace tailWord_59205 prefixEnd_59205 30400622149546093865227 := by
  unfold tailWord_59205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159383750517871254099069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1439589167011914169399379 2159383750517871254099069)
  ·
    refine ⟨809768906444201720287151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2159383750517871254099069 809768906444201720287151)
    ·
      refine ⟨1214653359666302580430727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809768906444201720287151 1214653359666302580430727)
      ·
        refine ⟨1821980039499453870646091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214653359666302580430727 1821980039499453870646091)
        ·
          refine ⟨2732970059249180805969137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821980039499453870646091 2732970059249180805969137)
          ·
            refine ⟨2049727544436885604476853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732970059249180805969137 2049727544436885604476853)
            ·
              refine ⟨192161957290958025419705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2049727544436885604476853 192161957290958025419705)
              ·
                refine ⟨144121467968218519064779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192161957290958025419705 144121467968218519064779)
                ·
                  refine ⟨216182201952327778597169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144121467968218519064779 216182201952327778597169)
                  ·
                    refine ⟨162136651464245833947877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 216182201952327778597169 162136651464245833947877)
                    ·
                      refine ⟨30400622149546093865227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 162136651464245833947877 30400622149546093865227)
                      ·
                        rfl

theorem cell23_59205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_59205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59205 prefixEnd_59205 := by exact prefixLift 59205
  have htrace : WordTrace (prefixWord ++ tailWord_59205) baseStart_59205 baseEnd_59205 := by
    simpa [prefixWord, tailWord_59205, baseEnd_59205] using wordTrace_append hprefix tailTrace_59205
  have hstable : (prefixWord ++ tailWord_59205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59205).length < 2 ^ (prefixWord ++ tailWord_59205).sum := by decide
  have hdescent : baseEnd_59205 < baseStart_59205 := by decide
  rcases family_descends (prefixWord ++ tailWord_59205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59225 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_59225 : Nat := 118140960795 + 59225 * 2 ^ 59
def prefixEnd_59225 : Nat := 4983230072969 + 3 ^ 40 * 59225 * 2
def baseEnd_59225 : Nat := 30410891762636015615135

theorem tailTrace_59225 : CollatzResearch.WordTrace tailWord_59225 prefixEnd_59225 30410891762636015615135 := by
  unfold tailWord_59225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160113210445414669827129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1440075473630276446551419 2160113210445414669827129)
  ·
    refine ⟨1620084907834061002370347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160113210445414669827129 1620084907834061002370347)
    ·
      refine ⟨2430127361751091503555521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620084907834061002370347 2430127361751091503555521)
      ·
        refine ⟨1822595521313318627666641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430127361751091503555521 1822595521313318627666641)
        ·
          refine ⟨1366946640984988970749981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822595521313318627666641 1366946640984988970749981)
          ·
            refine ⟨512604990369370864031243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366946640984988970749981 512604990369370864031243)
            ·
              refine ⟨768907485554056296046865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512604990369370864031243 768907485554056296046865)
              ·
                refine ⟨576680614165542222035149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768907485554056296046865 576680614165542222035149)
                ·
                  refine ⟨216255230312078333263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576680614165542222035149 216255230312078333263181)
                  ·
                    refine ⟨81095711367029374973693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216255230312078333263181 81095711367029374973693)
                    ·
                      refine ⟨30410891762636015615135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81095711367029374973693 30410891762636015615135)
                      ·
                        rfl

theorem cell23_59225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_59225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59225 prefixEnd_59225 := by exact prefixLift 59225
  have htrace : WordTrace (prefixWord ++ tailWord_59225) baseStart_59225 baseEnd_59225 := by
    simpa [prefixWord, tailWord_59225, baseEnd_59225] using wordTrace_append hprefix tailTrace_59225
  have hstable : (prefixWord ++ tailWord_59225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59225).length < 2 ^ (prefixWord ++ tailWord_59225).sum := by decide
  have hdescent : baseEnd_59225 < baseStart_59225 := by decide
  rcases family_descends (prefixWord ++ tailWord_59225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59226 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_59226 : Nat := 118140960795 + 59226 * 2 ^ 59
def prefixEnd_59226 : Nat := 4983230072969 + 3 ^ 40 * 59226 * 2
def baseEnd_59226 : Nat := 30411405243290511702631

theorem tailTrace_59226 : CollatzResearch.WordTrace tailWord_59226 prefixEnd_59226 30411405243290511702631 := by
  unfold tailWord_59226
  simp only [CollatzResearch.WordTrace]
  refine ⟨540037420860447960153383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1440099788961194560409021 540037420860447960153383)
  ·
    refine ⟨810056131290671940230075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540037420860447960153383 810056131290671940230075)
    ·
      refine ⟨1215084196936007910345113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810056131290671940230075 1215084196936007910345113)
      ·
        refine ⟨911313147702005932758835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215084196936007910345113 911313147702005932758835)
        ·
          refine ⟨1366969721553008899138253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911313147702005932758835 1366969721553008899138253)
          ·
            refine ⟨512613645582378337176845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1366969721553008899138253 512613645582378337176845)
            ·
              refine ⟨192230117093391876441317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512613645582378337176845 192230117093391876441317)
              ·
                refine ⟨36043146955010976832747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192230117093391876441317 36043146955010976832747)
                ·
                  refine ⟨54064720432516465249121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36043146955010976832747 54064720432516465249121)
                  ·
                    refine ⟨40548540324387348936841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54064720432516465249121 40548540324387348936841)
                    ·
                      refine ⟨30411405243290511702631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40548540324387348936841 30411405243290511702631)
                      ·
                        rfl

theorem cell23_59226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_59226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59226 prefixEnd_59226 := by exact prefixLift 59226
  have htrace : WordTrace (prefixWord ++ tailWord_59226) baseStart_59226 baseEnd_59226 := by
    simpa [prefixWord, tailWord_59226, baseEnd_59226] using wordTrace_append hprefix tailTrace_59226
  have hstable : (prefixWord ++ tailWord_59226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59226).length < 2 ^ (prefixWord ++ tailWord_59226).sum := by decide
  have hdescent : baseEnd_59226 < baseStart_59226 := by decide
  rcases family_descends (prefixWord ++ tailWord_59226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59269 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_59269 : Nat := 118140960795 + 59269 * 2 ^ 59
def prefixEnd_59269 : Nat := 4983230072969 + 3 ^ 40 * 59269 * 2
def baseEnd_59269 : Nat := 30433484911433843464933

theorem tailTrace_59269 : CollatzResearch.WordTrace tailWord_59269 prefixEnd_59269 30433484911433843464933 := by
  unfold tailWord_59269
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161718022286010184428861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1441145348190673456285907 2161718022286010184428861)
  ·
    refine ⟨810644258357253819160823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2161718022286010184428861 810644258357253819160823)
    ·
      refine ⟨1215966387535880728741235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810644258357253819160823 1215966387535880728741235)
      ·
        refine ⟨1823949581303821093111853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215966387535880728741235 1823949581303821093111853)
        ·
          refine ⟨683981092988932909916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823949581303821093111853 683981092988932909916945)
          ·
            refine ⟨512985819741699682437709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683981092988932909916945 512985819741699682437709)
            ·
              refine ⟨192369682403137380914141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512985819741699682437709 192369682403137380914141)
              ·
                refine ⟨72138630901176517842803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192369682403137380914141 72138630901176517842803)
                ·
                  refine ⟨108207946351764776764205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72138630901176517842803 108207946351764776764205)
                  ·
                    refine ⟨40577979881911791286577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108207946351764776764205 40577979881911791286577)
                    ·
                      refine ⟨30433484911433843464933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40577979881911791286577 30433484911433843464933)
                      ·
                        rfl

theorem cell23_59269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_59269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59269 prefixEnd_59269 := by exact prefixLift 59269
  have htrace : WordTrace (prefixWord ++ tailWord_59269) baseStart_59269 baseEnd_59269 := by
    simpa [prefixWord, tailWord_59269, baseEnd_59269] using wordTrace_append hprefix tailTrace_59269
  have hstable : (prefixWord ++ tailWord_59269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59269).length < 2 ^ (prefixWord ++ tailWord_59269).sum := by decide
  have hdescent : baseEnd_59269 < baseStart_59269 := by decide
  rcases family_descends (prefixWord ++ tailWord_59269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59292 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_59292 : Nat := 118140960795 + 59292 * 2 ^ 59
def prefixEnd_59292 : Nat := 4983230072969 + 3 ^ 40 * 59292 * 2
def baseEnd_59292 : Nat := 10148431655495751159109

theorem tailTrace_59292 : CollatzResearch.WordTrace tailWord_59292 prefixEnd_59292 10148431655495751159109 := by
  unfold tailWord_59292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081278450601342556258065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1441704600801790075010753 1081278450601342556258065)
  ·
    refine ⟨810958837951006917193549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1081278450601342556258065 810958837951006917193549)
    ·
      refine ⟨304109564231627593947581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 810958837951006917193549 304109564231627593947581)
      ·
        refine ⟨114041086586860347730343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304109564231627593947581 114041086586860347730343)
        ·
          refine ⟨171061629880290521595515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114041086586860347730343 171061629880290521595515)
          ·
            refine ⟨256592444820435782393273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171061629880290521595515 256592444820435782393273)
            ·
              refine ⟨192444333615326836794955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256592444820435782393273 192444333615326836794955)
              ·
                refine ⟨288666500422990255192433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192444333615326836794955 288666500422990255192433)
                ·
                  refine ⟨216499875317242691394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288666500422990255192433 216499875317242691394325)
                  ·
                    refine ⟨10148431655495751159109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216499875317242691394325 10148431655495751159109)
                    ·
                      rfl

theorem cell23_59292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_59292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59292 prefixEnd_59292 := by exact prefixLift 59292
  have htrace : WordTrace (prefixWord ++ tailWord_59292) baseStart_59292 baseEnd_59292 := by
    simpa [prefixWord, tailWord_59292, baseEnd_59292] using wordTrace_append hprefix tailTrace_59292
  have hstable : (prefixWord ++ tailWord_59292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59292).length < 2 ^ (prefixWord ++ tailWord_59292).sum := by decide
  have hdescent : baseEnd_59292 < baseStart_59292 := by decide
  rcases family_descends (prefixWord ++ tailWord_59292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59322 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 5]
def baseStart_59322 : Nat := 118140960795 + 59322 * 2 ^ 59
def prefixEnd_59322 : Nat := 4983230072969 + 3 ^ 40 * 59322 * 2
def baseEnd_59322 : Nat := 3384522154013570678021

theorem tailTrace_59322 : CollatzResearch.WordTrace tailWord_59322 prefixEnd_59322 3384522154013570678021 := by
  unfold tailWord_59322
  simp only [CollatzResearch.WordTrace]
  refine ⟨540912772773500059027055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1442434060729333490738813 540912772773500059027055)
  ·
    refine ⟨811369159160250088540583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540912772773500059027055 811369159160250088540583)
    ·
      refine ⟨1217053738740375132810875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811369159160250088540583 1217053738740375132810875)
      ·
        refine ⟨1825580608110562699216313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217053738740375132810875 1825580608110562699216313)
        ·
          refine ⟨1369185456082922024412235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825580608110562699216313 1369185456082922024412235)
          ·
            refine ⟨2053778184124383036618353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369185456082922024412235 2053778184124383036618353)
            ·
              refine ⟨1540333638093287277463765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053778184124383036618353 1540333638093287277463765)
              ·
                refine ⟨36101569642811420565557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1540333638093287277463765 36101569642811420565557)
                ·
                  refine ⟨3384522154013570678021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36101569642811420565557 3384522154013570678021)
                  ·
                    rfl

theorem cell23_59322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_59322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59322 prefixEnd_59322 := by exact prefixLift 59322
  have htrace : WordTrace (prefixWord ++ tailWord_59322) baseStart_59322 baseEnd_59322 := by
    simpa [prefixWord, tailWord_59322, baseEnd_59322] using wordTrace_append hprefix tailTrace_59322
  have hstable : (prefixWord ++ tailWord_59322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59322).length < 2 ^ (prefixWord ++ tailWord_59322).sum := by decide
  have hdescent : baseEnd_59322 < baseStart_59322 := by decide
  rcases family_descends (prefixWord ++ tailWord_59322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59339 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 5]
def baseStart_59339 : Nat := 118140960795 + 59339 * 2 ^ 59
def prefixEnd_59339 : Nat := 4983230072969 + 3 ^ 40 * 59339 * 2
def baseEnd_59339 : Nat := 3385492061916507732179

theorem tailTrace_59339 : CollatzResearch.WordTrace tailWord_59339 prefixEnd_59339 3385492061916507732179 := by
  unfold tailWord_59339
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164271132032412139477071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1442847421354941426318047 2164271132032412139477071)
  ·
    refine ⟨3246406698048618209215607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164271132032412139477071 3246406698048618209215607)
    ·
      refine ⟨4869610047072927313823411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246406698048618209215607 4869610047072927313823411)
      ·
        refine ⟨7304415070609390970735117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869610047072927313823411 7304415070609390970735117)
        ·
          refine ⟨2739155651478521614025669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7304415070609390970735117 2739155651478521614025669)
          ·
            refine ⟨513591684652222802629813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2739155651478521614025669 513591684652222802629813)
            ·
              refine ⟨48149220436145887746545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 513591684652222802629813 48149220436145887746545)
              ·
                refine ⟨36111915327109415809909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48149220436145887746545 36111915327109415809909)
                ·
                  refine ⟨3385492061916507732179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36111915327109415809909 3385492061916507732179)
                  ·
                    rfl

theorem cell23_59339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 5].length) (baseStart_59339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59339 prefixEnd_59339 := by exact prefixLift 59339
  have htrace : WordTrace (prefixWord ++ tailWord_59339) baseStart_59339 baseEnd_59339 := by
    simpa [prefixWord, tailWord_59339, baseEnd_59339] using wordTrace_append hprefix tailTrace_59339
  have hstable : (prefixWord ++ tailWord_59339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59339).length < 2 ^ (prefixWord ++ tailWord_59339).sum := by decide
  have hdescent : baseEnd_59339 < baseStart_59339 := by decide
  rcases family_descends (prefixWord ++ tailWord_59339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59350 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_59350 : Nat := 118140960795 + 59350 * 2 ^ 59
def prefixEnd_59350 : Nat := 4983230072969 + 3 ^ 40 * 59350 * 2
def baseEnd_59350 : Nat := 30475076844448026552061

theorem tailTrace_59350 : CollatzResearch.WordTrace tailWord_59350 prefixEnd_59350 30475076844448026552061 := by
  unfold tailWord_59350
  simp only [CollatzResearch.WordTrace]
  refine ⟨135292020937035063632969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1443114889995040678751669 135292020937035063632969)
  ·
    refine ⟨101469015702776297724727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135292020937035063632969 101469015702776297724727)
    ·
      refine ⟨152203523554164446587091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101469015702776297724727 152203523554164446587091)
      ·
        refine ⟨228305285331246669880637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152203523554164446587091 228305285331246669880637)
        ·
          refine ⟨85614481999217501205239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228305285331246669880637 85614481999217501205239)
          ·
            refine ⟨128421722998826251807859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85614481999217501205239 128421722998826251807859)
            ·
              refine ⟨192632584498239377711789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128421722998826251807859 192632584498239377711789)
              ·
                refine ⟨72237219186839766641921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192632584498239377711789 72237219186839766641921)
                ·
                  refine ⟨54177914390129824981441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72237219186839766641921 54177914390129824981441)
                  ·
                    refine ⟨40633435792597368736081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54177914390129824981441 40633435792597368736081)
                    ·
                      refine ⟨30475076844448026552061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40633435792597368736081 30475076844448026552061)
                      ·
                        rfl

theorem cell23_59350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_59350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59350 prefixEnd_59350 := by exact prefixLift 59350
  have htrace : WordTrace (prefixWord ++ tailWord_59350) baseStart_59350 baseEnd_59350 := by
    simpa [prefixWord, tailWord_59350, baseEnd_59350] using wordTrace_append hprefix tailTrace_59350
  have hstable : (prefixWord ++ tailWord_59350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59350).length < 2 ^ (prefixWord ++ tailWord_59350).sum := by decide
  have hdescent : baseEnd_59350 < baseStart_59350 := by decide
  rcases family_descends (prefixWord ++ tailWord_59350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_59392 : Nat := 118140960795 + 59392 * 2 ^ 59
def prefixEnd_59392 : Nat := 4983230072969 + 3 ^ 40 * 59392 * 2
def baseEnd_59392 : Nat := 30496643031936862226867

theorem tailTrace_59392 : CollatzResearch.WordTrace tailWord_59392 prefixEnd_59392 30496643031936862226867 := by
  unfold tailWord_59392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083102100420201095578215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1444136133893601460770953 1083102100420201095578215)
  ·
    refine ⟨1624653150630301643367323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1083102100420201095578215 1624653150630301643367323)
    ·
      refine ⟨2436979725945452465050985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624653150630301643367323 2436979725945452465050985)
      ·
        refine ⟨1827734794459089348788239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2436979725945452465050985 1827734794459089348788239)
        ·
          refine ⟨2741602191688634023182359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827734794459089348788239 2741602191688634023182359)
          ·
            refine ⟨4112403287532951034773539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741602191688634023182359 4112403287532951034773539)
            ·
              refine ⟨6168604931299426552160309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112403287532951034773539 6168604931299426552160309)
              ·
                refine ⟨578306712309321239265029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6168604931299426552160309 578306712309321239265029)
                ·
                  refine ⟨108432508557997732362193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578306712309321239265029 108432508557997732362193)
                  ·
                    refine ⟨81324381418498299271645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108432508557997732362193 81324381418498299271645)
                    ·
                      refine ⟨30496643031936862226867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81324381418498299271645 30496643031936862226867)
                      ·
                        rfl

theorem cell23_59392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_59392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59392 prefixEnd_59392 := by exact prefixLift 59392
  have htrace : WordTrace (prefixWord ++ tailWord_59392) baseStart_59392 baseEnd_59392 := by
    simpa [prefixWord, tailWord_59392, baseEnd_59392] using wordTrace_append hprefix tailTrace_59392
  have hstable : (prefixWord ++ tailWord_59392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59392).length < 2 ^ (prefixWord ++ tailWord_59392).sum := by decide
  have hdescent : baseEnd_59392 < baseStart_59392 := by decide
  rcases family_descends (prefixWord ++ tailWord_59392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59395 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 8]
def baseStart_59395 : Nat := 118140960795 + 59395 * 2 ^ 59
def prefixEnd_59395 : Nat := 4983230072969 + 3 ^ 40 * 59395 * 2
def baseEnd_59395 : Nat := 3388687052655594498817

theorem tailTrace_59395 : CollatzResearch.WordTrace tailWord_59395 prefixEnd_59395 3388687052655594498817 := by
  unfold tailWord_59395
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166313619829533703515639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1444209079886355802343759 2166313619829533703515639)
  ·
    refine ⟨3249470429744300555273459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166313619829533703515639 3249470429744300555273459)
    ·
      refine ⟨4874205644616450832910189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249470429744300555273459 4874205644616450832910189)
      ·
        refine ⟨1827827116731169062341321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4874205644616450832910189 1827827116731169062341321)
        ·
          refine ⟨1370870337548376796755991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827827116731169062341321 1370870337548376796755991)
          ·
            refine ⟨2056305506322565195133987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370870337548376796755991 2056305506322565195133987)
            ·
              refine ⟨3084458259483847792700981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056305506322565195133987 3084458259483847792700981)
              ·
                refine ⟨289167961826610730565717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3084458259483847792700981 289167961826610730565717)
                ·
                  refine ⟨3388687052655594498817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 289167961826610730565717 3388687052655594498817)
                  ·
                    rfl

theorem cell23_59395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 8].length) (baseStart_59395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59395 prefixEnd_59395 := by exact prefixLift 59395
  have htrace : WordTrace (prefixWord ++ tailWord_59395) baseStart_59395 baseEnd_59395 := by
    simpa [prefixWord, tailWord_59395, baseEnd_59395] using wordTrace_append hprefix tailTrace_59395
  have hstable : (prefixWord ++ tailWord_59395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59395).length < 2 ^ (prefixWord ++ tailWord_59395).sum := by decide
  have hdescent : baseEnd_59395 < baseStart_59395 := by decide
  rcases family_descends (prefixWord ++ tailWord_59395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59456 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_59456 : Nat := 118140960795 + 59456 * 2 ^ 59
def prefixEnd_59456 : Nat := 4983230072969 + 3 ^ 40 * 59456 * 2
def baseEnd_59456 : Nat := 30529505793824611826573

theorem tailTrace_59456 : CollatzResearch.WordTrace tailWord_59456 prefixEnd_59456 30529505793824611826573 := by
  unfold tailWord_59456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084269236304270560743111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1445692315072360747657481 1084269236304270560743111)
  ·
    refine ⟨1626403854456405841114667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1084269236304270560743111 1626403854456405841114667)
    ·
      refine ⟨2439605781684608761672001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626403854456405841114667 2439605781684608761672001)
      ·
        refine ⟨1829704336263456571254001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439605781684608761672001 1829704336263456571254001)
        ·
          refine ⟨1372278252197592428440501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1829704336263456571254001 1372278252197592428440501)
          ·
            refine ⟨128651086143524290166297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1372278252197592428440501 128651086143524290166297)
            ·
              refine ⟨96488314607643217624723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128651086143524290166297 96488314607643217624723)
              ·
                refine ⟨144732471911464826437085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96488314607643217624723 144732471911464826437085)
                ·
                  refine ⟨54274676966799309913907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144732471911464826437085 54274676966799309913907)
                  ·
                    refine ⟨81412015450198964870861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54274676966799309913907 81412015450198964870861)
                    ·
                      refine ⟨30529505793824611826573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81412015450198964870861 30529505793824611826573)
                      ·
                        rfl

theorem cell23_59456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_59456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59456 prefixEnd_59456 := by exact prefixLift 59456
  have htrace : WordTrace (prefixWord ++ tailWord_59456) baseStart_59456 baseEnd_59456 := by
    simpa [prefixWord, tailWord_59456, baseEnd_59456] using wordTrace_append hprefix tailTrace_59456
  have hstable : (prefixWord ++ tailWord_59456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59456).length < 2 ^ (prefixWord ++ tailWord_59456).sum := by decide
  have hdescent : baseEnd_59456 < baseStart_59456 := by decide
  rcases family_descends (prefixWord ++ tailWord_59456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59479 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_59479 : Nat := 118140960795 + 59479 * 2 ^ 59
def prefixEnd_59479 : Nat := 4983230072969 + 3 ^ 40 * 59479 * 2
def baseEnd_59479 : Nat := 30541315848878021838967

theorem tailTrace_59479 : CollatzResearch.WordTrace tailWord_59479 prefixEnd_59479 30541315848878021838967 := by
  unfold tailWord_59479
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169377351525216049573491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1446251567683477366382327 2169377351525216049573491)
  ·
    refine ⟨3254066027287824074360237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169377351525216049573491 3254066027287824074360237)
    ·
      refine ⟨1220274760232934027885089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3254066027287824074360237 1220274760232934027885089)
      ·
        refine ⟨915206070174700520913817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220274760232934027885089 915206070174700520913817)
        ·
          refine ⟨686404552631025390685363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915206070174700520913817 686404552631025390685363)
          ·
            refine ⟨1029606828946538086028045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686404552631025390685363 1029606828946538086028045)
            ·
              refine ⟨386102560854951782260517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029606828946538086028045 386102560854951782260517)
              ·
                refine ⟨72394230160303459173847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386102560854951782260517 72394230160303459173847)
                ·
                  refine ⟨108591345240455188760771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72394230160303459173847 108591345240455188760771)
                  ·
                    refine ⟨162887017860682783141157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108591345240455188760771 162887017860682783141157)
                    ·
                      refine ⟨30541315848878021838967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 162887017860682783141157 30541315848878021838967)
                      ·
                        rfl

theorem cell23_59479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_59479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59479 prefixEnd_59479 := by exact prefixLift 59479
  have htrace : WordTrace (prefixWord ++ tailWord_59479) baseStart_59479 baseEnd_59479 := by
    simpa [prefixWord, tailWord_59479, baseEnd_59479] using wordTrace_append hprefix tailTrace_59479
  have hstable : (prefixWord ++ tailWord_59479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59479).length < 2 ^ (prefixWord ++ tailWord_59479).sum := by decide
  have hdescent : baseEnd_59479 < baseStart_59479 := by decide
  rcases family_descends (prefixWord ++ tailWord_59479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59482 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_59482 : Nat := 118140960795 + 59482 * 2 ^ 59
def prefixEnd_59482 : Nat := 4983230072969 + 3 ^ 40 * 59482 * 2
def baseEnd_59482 : Nat := 30542856290841510101453

theorem tailTrace_59482 : CollatzResearch.WordTrace tailWord_59482 prefixEnd_59482 30542856290841510101453 := by
  unfold tailWord_59482
  simp only [CollatzResearch.WordTrace]
  refine ⟨542371692628586890483175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1446324513676231707955133 542371692628586890483175)
  ·
    refine ⟨813557538942880335724763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 542371692628586890483175 813557538942880335724763)
    ·
      refine ⟨1220336308414320503587145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813557538942880335724763 1220336308414320503587145)
      ·
        refine ⟨915252231310740377690359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220336308414320503587145 915252231310740377690359)
        ·
          refine ⟨1372878346966110566535539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915252231310740377690359 1372878346966110566535539)
          ·
            refine ⟨2059317520449165849803309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372878346966110566535539 2059317520449165849803309)
            ·
              refine ⟨772244070168437193676241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059317520449165849803309 772244070168437193676241)
              ·
                refine ⟨579183052626327895257181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772244070168437193676241 579183052626327895257181)
                ·
                  refine ⟨217193644734872960721443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579183052626327895257181 217193644734872960721443)
                  ·
                    refine ⟨325790467102309441082165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217193644734872960721443 325790467102309441082165)
                    ·
                      refine ⟨30542856290841510101453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 325790467102309441082165 30542856290841510101453)
                      ·
                        rfl

theorem cell23_59482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_59482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59482 prefixEnd_59482 := by exact prefixLift 59482
  have htrace : WordTrace (prefixWord ++ tailWord_59482) baseStart_59482 baseEnd_59482 := by
    simpa [prefixWord, tailWord_59482, baseEnd_59482] using wordTrace_append hprefix tailTrace_59482
  have hstable : (prefixWord ++ tailWord_59482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59482).length < 2 ^ (prefixWord ++ tailWord_59482).sum := by decide
  have hdescent : baseEnd_59482 < baseStart_59482 := by decide
  rcases family_descends (prefixWord ++ tailWord_59482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59513 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 3, 2, 2]
def baseStart_59513 : Nat := 118140960795 + 59513 * 2 ^ 59
def prefixEnd_59513 : Nat := 4983230072969 + 3 ^ 40 * 59513 * 2
def baseEnd_59513 : Nat := 30558774191130888813811

theorem tailTrace_59513 : CollatzResearch.WordTrace tailWord_59513 prefixEnd_59513 30558774191130888813811 := by
  unfold tailWord_59513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170617433402039856311193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1447078288934693237540795 2170617433402039856311193)
  ·
    refine ⟨1627963075051529892233395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170617433402039856311193 1627963075051529892233395)
    ·
      refine ⟨2441944612577294838350093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627963075051529892233395 2441944612577294838350093)
      ·
        refine ⟨915729229716485564381285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2441944612577294838350093 915729229716485564381285)
        ·
          refine ⟨171699230571841043321491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915729229716485564381285 171699230571841043321491)
          ·
            refine ⟨257548845857761564982237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171699230571841043321491 257548845857761564982237)
            ·
              refine ⟨96580817196660586868339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257548845857761564982237 96580817196660586868339)
              ·
                refine ⟨144871225794990880302509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96580817196660586868339 144871225794990880302509)
                ·
                  refine ⟨54326709673121580113441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144871225794990880302509 54326709673121580113441)
                  ·
                    refine ⟨40745032254841185085081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54326709673121580113441 40745032254841185085081)
                    ·
                      refine ⟨30558774191130888813811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40745032254841185085081 30558774191130888813811)
                      ·
                        rfl

theorem cell23_59513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_59513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59513 prefixEnd_59513 := by exact prefixLift 59513
  have htrace : WordTrace (prefixWord ++ tailWord_59513) baseStart_59513 baseEnd_59513 := by
    simpa [prefixWord, tailWord_59513, baseEnd_59513] using wordTrace_append hprefix tailTrace_59513
  have hstable : (prefixWord ++ tailWord_59513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59513).length < 2 ^ (prefixWord ++ tailWord_59513).sum := by decide
  have hdescent : baseEnd_59513 < baseStart_59513 := by decide
  rcases family_descends (prefixWord ++ tailWord_59513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59523 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 2, 4]
def baseStart_59523 : Nat := 118140960795 + 59523 * 2 ^ 59
def prefixEnd_59523 : Nat := 4983230072969 + 3 ^ 40 * 59523 * 2
def baseEnd_59523 : Nat := 10187969665891949896255

theorem tailTrace_59523 : CollatzResearch.WordTrace tailWord_59523 prefixEnd_59523 10187969665891949896255 := by
  unfold tailWord_59523
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170982163365811564175223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1447321442243874376116815 2170982163365811564175223)
  ·
    refine ⟨3256473245048717346262835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170982163365811564175223 3256473245048717346262835)
    ·
      refine ⟨4884709867573076019394253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256473245048717346262835 4884709867573076019394253)
      ·
        refine ⟨1831766200339903507272845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4884709867573076019394253 1831766200339903507272845)
        ·
          refine ⟨686912325127463815227317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1831766200339903507272845 686912325127463815227317)
          ·
            refine ⟨64398030480699732677561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 686912325127463815227317 64398030480699732677561)
            ·
              refine ⟨48298522860524799508171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64398030480699732677561 48298522860524799508171)
              ·
                refine ⟨72447784290787199262257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48298522860524799508171 72447784290787199262257)
                ·
                  refine ⟨54335838218090399446693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72447784290787199262257 54335838218090399446693)
                  ·
                    refine ⟨10187969665891949896255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54335838218090399446693 10187969665891949896255)
                    ·
                      rfl

theorem cell23_59523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 2, 4].length) (baseStart_59523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59523 prefixEnd_59523 := by exact prefixLift 59523
  have htrace : WordTrace (prefixWord ++ tailWord_59523) baseStart_59523 baseEnd_59523 := by
    simpa [prefixWord, tailWord_59523, baseEnd_59523] using wordTrace_append hprefix tailTrace_59523
  have hstable : (prefixWord ++ tailWord_59523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59523).length < 2 ^ (prefixWord ++ tailWord_59523).sum := by decide
  have hdescent : baseEnd_59523 < baseStart_59523 := by decide
  rcases family_descends (prefixWord ++ tailWord_59523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59529 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_59529 : Nat := 118140960795 + 59529 * 2 ^ 59
def prefixEnd_59529 : Nat := 4983230072969 + 3 ^ 40 * 59529 * 2
def baseEnd_59529 : Nat := 30566989881602826213737

theorem tailTrace_59529 : CollatzResearch.WordTrace tailWord_59529 prefixEnd_59529 30566989881602826213737 := by
  unfold tailWord_59529
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171201001344074588893641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1447467334229383059262427 2171201001344074588893641)
  ·
    refine ⟨1628400751008055941670231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2171201001344074588893641 1628400751008055941670231)
    ·
      refine ⟨2442601126512083912505347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628400751008055941670231 2442601126512083912505347)
      ·
        refine ⟨3663901689768125868758021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442601126512083912505347 3663901689768125868758021)
        ·
          refine ⟨686981566831523600392129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3663901689768125868758021 686981566831523600392129)
          ·
            refine ⟨515236175123642700294097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686981566831523600392129 515236175123642700294097)
            ·
              refine ⟨386427131342732025220573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515236175123642700294097 386427131342732025220573)
              ·
                refine ⟨144910174253524509457715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386427131342732025220573 144910174253524509457715)
                ·
                  refine ⟨217365261380286764186573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144910174253524509457715 217365261380286764186573)
                  ·
                    refine ⟨81511973017607536569965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217365261380286764186573 81511973017607536569965)
                    ·
                      refine ⟨30566989881602826213737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81511973017607536569965 30566989881602826213737)
                      ·
                        rfl

theorem cell23_59529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_59529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59529 prefixEnd_59529 := by exact prefixLift 59529
  have htrace : WordTrace (prefixWord ++ tailWord_59529) baseStart_59529 baseEnd_59529 := by
    simpa [prefixWord, tailWord_59529, baseEnd_59529] using wordTrace_append hprefix tailTrace_59529
  have hstable : (prefixWord ++ tailWord_59529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59529).length < 2 ^ (prefixWord ++ tailWord_59529).sum := by decide
  have hdescent : baseEnd_59529 < baseStart_59529 := by decide
  rcases family_descends (prefixWord ++ tailWord_59529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59550 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_59550 : Nat := 118140960795 + 59550 * 2 ^ 59
def prefixEnd_59550 : Nat := 4983230072969 + 3 ^ 40 * 59550 * 2
def baseEnd_59550 : Nat := 30577772975347244051141

theorem tailTrace_59550 : CollatzResearch.WordTrace tailWord_59550 prefixEnd_59550 30577772975347244051141 := by
  unfold tailWord_59550
  simp only [CollatzResearch.WordTrace]
  refine ⟨271495866783499396926013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1447977956178663450272069 271495866783499396926013)
  ·
    refine ⟨101810950043812273847255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271495866783499396926013 101810950043812273847255)
    ·
      refine ⟨152716425065718410770883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101810950043812273847255 152716425065718410770883)
      ·
        refine ⟨229074637598577616156325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152716425065718410770883 229074637598577616156325)
        ·
          refine ⟨42951494549733303029311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229074637598577616156325 42951494549733303029311)
          ·
            refine ⟨64427241824599954543967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42951494549733303029311 64427241824599954543967)
            ·
              refine ⟨96640862736899931815951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64427241824599954543967 96640862736899931815951)
              ·
                refine ⟨144961294105349897723927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96640862736899931815951 144961294105349897723927)
                ·
                  refine ⟨217441941158024846585891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144961294105349897723927 217441941158024846585891)
                  ·
                    refine ⟨326162911737037269878837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217441941158024846585891 326162911737037269878837)
                    ·
                      refine ⟨30577772975347244051141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 326162911737037269878837 30577772975347244051141)
                      ·
                        rfl

theorem cell23_59550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_59550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59550 prefixEnd_59550 := by exact prefixLift 59550
  have htrace : WordTrace (prefixWord ++ tailWord_59550) baseStart_59550 baseEnd_59550 := by
    simpa [prefixWord, tailWord_59550, baseEnd_59550] using wordTrace_append hprefix tailTrace_59550
  have hstable : (prefixWord ++ tailWord_59550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59550).length < 2 ^ (prefixWord ++ tailWord_59550).sum := by decide
  have hdescent : baseEnd_59550 < baseStart_59550 := by decide
  rcases family_descends (prefixWord ++ tailWord_59550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59626 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_59626 : Nat := 118140960795 + 59626 * 2 ^ 59
def prefixEnd_59626 : Nat := 4983230072969 + 3 ^ 40 * 59626 * 2
def baseEnd_59626 : Nat := 3401866389454327411199

theorem tailTrace_59626 : CollatzResearch.WordTrace tailWord_59626 prefixEnd_59626 3401866389454327411199 := by
  unfold tailWord_59626
  simp only [CollatzResearch.WordTrace]
  refine ⟨543684720498165038793683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1449825921328440103449821 543684720498165038793683)
  ·
    refine ⟨815527080747247558190525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543684720498165038793683 815527080747247558190525)
    ·
      refine ⟨305822655280217834321447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 815527080747247558190525 305822655280217834321447)
      ·
        refine ⟨458733982920326751482171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305822655280217834321447 458733982920326751482171)
        ·
          refine ⟨688100974380490127223257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458733982920326751482171 688100974380490127223257)
          ·
            refine ⟨516075730785367595417443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688100974380490127223257 516075730785367595417443)
            ·
              refine ⟨774113596178051393126165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516075730785367595417443 774113596178051393126165)
              ·
                refine ⟨36286574820846159052789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 774113596178051393126165 36286574820846159052789)
                ·
                  refine ⟨3401866389454327411199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36286574820846159052789 3401866389454327411199)
                  ·
                    rfl

theorem cell23_59626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_59626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59626 prefixEnd_59626 := by exact prefixLift 59626
  have htrace : WordTrace (prefixWord ++ tailWord_59626) baseStart_59626 baseEnd_59626 := by
    simpa [prefixWord, tailWord_59626, baseEnd_59626] using wordTrace_append hprefix tailTrace_59626
  have hstable : (prefixWord ++ tailWord_59626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59626).length < 2 ^ (prefixWord ++ tailWord_59626).sum := by decide
  have hdescent : baseEnd_59626 < baseStart_59626 := by decide
  rcases family_descends (prefixWord ++ tailWord_59626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59659 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_59659 : Nat := 118140960795 + 59659 * 2 ^ 59
def prefixEnd_59659 : Nat := 4983230072969 + 3 ^ 40 * 59659 * 2
def baseEnd_59659 : Nat := 30633742366687317588139

theorem tailTrace_59659 : CollatzResearch.WordTrace tailWord_59659 prefixEnd_59659 30633742366687317588139 := by
  unfold tailWord_59659
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175942490873106791126031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1450628327248737860750687 2175942490873106791126031)
  ·
    refine ⟨3263913736309660186689047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2175942490873106791126031 3263913736309660186689047)
    ·
      refine ⟨4895870604464490280033571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263913736309660186689047 4895870604464490280033571)
      ·
        refine ⟨7343805906696735420050357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895870604464490280033571 7343805906696735420050357)
        ·
          refine ⟨688481803752818945629721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7343805906696735420050357 688481803752818945629721)
          ·
            refine ⟨516361352814614209222291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688481803752818945629721 516361352814614209222291)
            ·
              refine ⟨774542029221921313833437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516361352814614209222291 774542029221921313833437)
              ·
                refine ⟨290453260958220492687539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 774542029221921313833437 290453260958220492687539)
                ·
                  refine ⟨435679891437330739031309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290453260958220492687539 435679891437330739031309)
                  ·
                    refine ⟨163379959288999027136741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 435679891437330739031309 163379959288999027136741)
                    ·
                      refine ⟨30633742366687317588139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 163379959288999027136741 30633742366687317588139)
                      ·
                        rfl

theorem cell23_59659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_59659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59659 prefixEnd_59659 := by exact prefixLift 59659
  have htrace : WordTrace (prefixWord ++ tailWord_59659) baseStart_59659 baseEnd_59659 := by
    simpa [prefixWord, tailWord_59659, baseEnd_59659] using wordTrace_append hprefix tailTrace_59659
  have hstable : (prefixWord ++ tailWord_59659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59659).length < 2 ^ (prefixWord ++ tailWord_59659).sum := by decide
  have hdescent : baseEnd_59659 < baseStart_59659 := by decide
  rcases family_descends (prefixWord ++ tailWord_59659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59733 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 6]
def baseStart_59733 : Nat := 118140960795 + 59733 * 2 ^ 59
def prefixEnd_59733 : Nat := 4983230072969 + 3 ^ 40 * 59733 * 2
def baseEnd_59733 : Nat := 3407971103902225340311

theorem tailTrace_59733 : CollatzResearch.WordTrace tailWord_59733 prefixEnd_59733 3407971103902225340311 := by
  unfold tailWord_59733
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178641492605017429319853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1452427661736678286213235 2178641492605017429319853)
  ·
    refine ⟨816990559726881535994945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2178641492605017429319853 816990559726881535994945)
    ·
      refine ⟨612742919795161151996209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 816990559726881535994945 612742919795161151996209)
      ·
        refine ⟨459557189846370863997157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612742919795161151996209 459557189846370863997157)
        ·
          refine ⟨86166973096194536999467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 459557189846370863997157 86166973096194536999467)
          ·
            refine ⟨129250459644291805499201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86166973096194536999467 129250459644291805499201)
            ·
              refine ⟨96937844733218854124401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129250459644291805499201 96937844733218854124401)
              ·
                refine ⟨72703383549914140593301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96937844733218854124401 72703383549914140593301)
                ·
                  refine ⟨3407971103902225340311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72703383549914140593301 3407971103902225340311)
                  ·
                    rfl

theorem cell23_59733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_59733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59733 prefixEnd_59733 := by exact prefixLift 59733
  have htrace : WordTrace (prefixWord ++ tailWord_59733) baseStart_59733 baseEnd_59733 := by
    simpa [prefixWord, tailWord_59733, baseEnd_59733] using wordTrace_append hprefix tailTrace_59733
  have hstable : (prefixWord ++ tailWord_59733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59733).length < 2 ^ (prefixWord ++ tailWord_59733).sum := by decide
  have hdescent : baseEnd_59733 < baseStart_59733 := by decide
  rcases family_descends (prefixWord ++ tailWord_59733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59777 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_59777 : Nat := 118140960795 + 59777 * 2 ^ 59
def prefixEnd_59777 : Nat := 4983230072969 + 3 ^ 40 * 59777 * 2
def baseEnd_59777 : Nat := 30694333083917855912597

theorem tailTrace_59777 : CollatzResearch.WordTrace tailWord_59777 prefixEnd_59777 30694333083917855912597 := by
  unfold tailWord_59777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180246304445612943921585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1453497536297075295947723 2180246304445612943921585)
  ·
    refine ⟨1635184728334209707941189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2180246304445612943921585 1635184728334209707941189)
    ·
      refine ⟨306597136562664320238973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1635184728334209707941189 306597136562664320238973)
      ·
        refine ⟨114973926210999120089615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306597136562664320238973 114973926210999120089615)
        ·
          refine ⟨172460889316498680134423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114973926210999120089615 172460889316498680134423)
          ·
            refine ⟨258691333974748020201635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172460889316498680134423 258691333974748020201635)
            ·
              refine ⟨388037000962122030302453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258691333974748020201635 388037000962122030302453)
              ·
                refine ⟨36378468840198940340855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388037000962122030302453 36378468840198940340855)
                ·
                  refine ⟨54567703260298410511283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36378468840198940340855 54567703260298410511283)
                  ·
                    refine ⟨81851554890447615766925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54567703260298410511283 81851554890447615766925)
                    ·
                      refine ⟨30694333083917855912597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81851554890447615766925 30694333083917855912597)
                      ·
                        rfl

theorem cell23_59777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_59777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59777 prefixEnd_59777 := by exact prefixLift 59777
  have htrace : WordTrace (prefixWord ++ tailWord_59777) baseStart_59777 baseEnd_59777 := by
    simpa [prefixWord, tailWord_59777, baseEnd_59777] using wordTrace_append hprefix tailTrace_59777
  have hstable : (prefixWord ++ tailWord_59777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59777).length < 2 ^ (prefixWord ++ tailWord_59777).sum := by decide
  have hdescent : baseEnd_59777 < baseStart_59777 := by decide
  rcases family_descends (prefixWord ++ tailWord_59777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59783 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_59783 : Nat := 118140960795 + 59783 * 2 ^ 59
def prefixEnd_59783 : Nat := 4983230072969 + 3 ^ 40 * 59783 * 2
def baseEnd_59783 : Nat := 30697413967844832437569

theorem tailTrace_59783 : CollatzResearch.WordTrace tailWord_59783 prefixEnd_59783 30697413967844832437569 := by
  unfold tailWord_59783
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180465142423875968640003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1453643428282583979093335 2180465142423875968640003)
  ·
    refine ⟨3270697713635813952960005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180465142423875968640003 3270697713635813952960005)
    ·
      refine ⟨613255821306715116180001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3270697713635813952960005 613255821306715116180001)
      ·
        refine ⟨459941865980036337135001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613255821306715116180001 459941865980036337135001)
        ·
          refine ⟨344956399485027252851251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459941865980036337135001 344956399485027252851251)
          ·
            refine ⟨517434599227540879276877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344956399485027252851251 517434599227540879276877)
            ·
              refine ⟨194037974710327829728829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 517434599227540879276877 194037974710327829728829)
              ·
                refine ⟨72764240516372936148311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194037974710327829728829 72764240516372936148311)
                ·
                  refine ⟨109146360774559404222467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72764240516372936148311 109146360774559404222467)
                  ·
                    refine ⟨163719541161839106333701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109146360774559404222467 163719541161839106333701)
                    ·
                      refine ⟨30697413967844832437569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 163719541161839106333701 30697413967844832437569)
                      ·
                        rfl

theorem cell23_59783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_59783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59783 prefixEnd_59783 := by exact prefixLift 59783
  have htrace : WordTrace (prefixWord ++ tailWord_59783) baseStart_59783 baseEnd_59783 := by
    simpa [prefixWord, tailWord_59783, baseEnd_59783] using wordTrace_append hprefix tailTrace_59783
  have hstable : (prefixWord ++ tailWord_59783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59783).length < 2 ^ (prefixWord ++ tailWord_59783).sum := by decide
  have hdescent : baseEnd_59783 < baseStart_59783 := by decide
  rcases family_descends (prefixWord ++ tailWord_59783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59828 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_59828 : Nat := 118140960795 + 59828 * 2 ^ 59
def prefixEnd_59828 : Nat := 4983230072969 + 3 ^ 40 * 59828 * 2
def baseEnd_59828 : Nat := 30720520597297156374863

theorem tailTrace_59828 : CollatzResearch.WordTrace tailWord_59828 prefixEnd_59828 30720520597297156374863 := by
  unfold tailWord_59828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091053213630424327014069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1454737618173899102685425 1091053213630424327014069)
  ·
    refine ⟨102286238777852280657569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1091053213630424327014069 102286238777852280657569)
    ·
      refine ⟨76714679083389210493177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102286238777852280657569 76714679083389210493177)
      ·
        refine ⟨57536009312541907869883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76714679083389210493177 57536009312541907869883)
        ·
          refine ⟨86304013968812861804825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57536009312541907869883 86304013968812861804825)
          ·
            refine ⟨64728010476609646353619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86304013968812861804825 64728010476609646353619)
            ·
              refine ⟨97092015714914469530429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64728010476609646353619 97092015714914469530429)
              ·
                refine ⟨36409505893092926073911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97092015714914469530429 36409505893092926073911)
                ·
                  refine ⟨54614258839639389110867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36409505893092926073911 54614258839639389110867)
                  ·
                    refine ⟨81921388259459083666301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54614258839639389110867 81921388259459083666301)
                    ·
                      refine ⟨30720520597297156374863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81921388259459083666301 30720520597297156374863)
                      ·
                        rfl

theorem cell23_59828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_59828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59828 prefixEnd_59828 := by exact prefixLift 59828
  have htrace : WordTrace (prefixWord ++ tailWord_59828) baseStart_59828 baseEnd_59828 := by
    simpa [prefixWord, tailWord_59828, baseEnd_59828] using wordTrace_append hprefix tailTrace_59828
  have hstable : (prefixWord ++ tailWord_59828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59828).length < 2 ^ (prefixWord ++ tailWord_59828).sum := by decide
  have hdescent : baseEnd_59828 < baseStart_59828 := by decide
  rcases family_descends (prefixWord ++ tailWord_59828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59843 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 5, 3, 2]
def baseStart_59843 : Nat := 118140960795 + 59843 * 2 ^ 59
def prefixEnd_59843 : Nat := 4983230072969 + 3 ^ 40 * 59843 * 2
def baseEnd_59843 : Nat := 30728222807114597687293

theorem tailTrace_59843 : CollatzResearch.WordTrace tailWord_59843 prefixEnd_59843 30728222807114597687293 := by
  unfold tailWord_59843
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182653522206506215824183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1455102348137670810549455 2182653522206506215824183)
  ·
    refine ⟨3273980283309759323736275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182653522206506215824183 3273980283309759323736275)
    ·
      refine ⟨4910970424964638985604413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273980283309759323736275 4910970424964638985604413)
      ·
        refine ⟨1841613909361739619601655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4910970424964638985604413 1841613909361739619601655)
        ·
          refine ⟨2762420864042609429402483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841613909361739619601655 2762420864042609429402483)
          ·
            refine ⟨4143631296063914144103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762420864042609429402483 4143631296063914144103725)
            ·
              refine ⟨1553861736023967804038897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143631296063914144103725 1553861736023967804038897)
              ·
                refine ⟨1165396302017975853029173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553861736023967804038897 1165396302017975853029173)
                ·
                  refine ⟨109255903314185236221485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165396302017975853029173 109255903314185236221485)
                  ·
                    refine ⟨40970963742819463583057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109255903314185236221485 40970963742819463583057)
                    ·
                      refine ⟨30728222807114597687293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40970963742819463583057 30728222807114597687293)
                      ·
                        rfl

theorem cell23_59843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_59843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59843 prefixEnd_59843 := by exact prefixLift 59843
  have htrace : WordTrace (prefixWord ++ tailWord_59843) baseStart_59843 baseEnd_59843 := by
    simpa [prefixWord, tailWord_59843, baseEnd_59843] using wordTrace_append hprefix tailTrace_59843
  have hstable : (prefixWord ++ tailWord_59843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59843).length < 2 ^ (prefixWord ++ tailWord_59843).sum := by decide
  have hdescent : baseEnd_59843 < baseStart_59843 := by decide
  rcases family_descends (prefixWord ++ tailWord_59843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59850 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_59850 : Nat := 118140960795 + 59850 * 2 ^ 59
def prefixEnd_59850 : Nat := 4983230072969 + 3 ^ 40 * 59850 * 2
def baseEnd_59850 : Nat := 30731817171696070299761

theorem tailTrace_59850 : CollatzResearch.WordTrace tailWord_59850 prefixEnd_59850 30731817171696070299761 := by
  unfold tailWord_59850
  simp only [CollatzResearch.WordTrace]
  refine ⟨545727208295286602832251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1455272555454097607552669 545727208295286602832251)
  ·
    refine ⟨818590812442929904248377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545727208295286602832251 818590812442929904248377)
    ·
      refine ⟨613943109332197428186283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818590812442929904248377 613943109332197428186283)
      ·
        refine ⟨920914663998296142279425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613943109332197428186283 920914663998296142279425)
        ·
          refine ⟨690685997998722106709569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920914663998296142279425 690685997998722106709569)
          ·
            refine ⟨518014498499041580032177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690685997998722106709569 518014498499041580032177)
            ·
              refine ⟨388510873874281185024133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518014498499041580032177 388510873874281185024133)
              ·
                refine ⟨72845788851427722192025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388510873874281185024133 72845788851427722192025)
                ·
                  refine ⟨54634341638570791644019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72845788851427722192025 54634341638570791644019)
                  ·
                    refine ⟨81951512457856187466029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54634341638570791644019 81951512457856187466029)
                    ·
                      refine ⟨30731817171696070299761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 81951512457856187466029 30731817171696070299761)
                      ·
                        rfl

theorem cell23_59850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_59850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59850 prefixEnd_59850 := by exact prefixLift 59850
  have htrace : WordTrace (prefixWord ++ tailWord_59850) baseStart_59850 baseEnd_59850 := by
    simpa [prefixWord, tailWord_59850, baseEnd_59850] using wordTrace_append hprefix tailTrace_59850
  have hstable : (prefixWord ++ tailWord_59850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59850).length < 2 ^ (prefixWord ++ tailWord_59850).sum := by decide
  have hdescent : baseEnd_59850 < baseStart_59850 := by decide
  rcases family_descends (prefixWord ++ tailWord_59850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59866 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_59866 : Nat := 118140960795 + 59866 * 2 ^ 59
def prefixEnd_59866 : Nat := 4983230072969 + 3 ^ 40 * 59866 * 2
def baseEnd_59866 : Nat := 10246677620722669233229

theorem tailTrace_59866 : CollatzResearch.WordTrace tailWord_59866 prefixEnd_59866 10246677620722669233229 := by
  unfold tailWord_59866
  simp only [CollatzResearch.WordTrace]
  refine ⟨545873100280795285977863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1455661600748787429274301 545873100280795285977863)
  ·
    refine ⟨818809650421192928966795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545873100280795285977863 818809650421192928966795)
    ·
      refine ⟨1228214475631789393450193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818809650421192928966795 1228214475631789393450193)
      ·
        refine ⟨921160856723842045087645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228214475631789393450193 921160856723842045087645)
        ·
          refine ⟨345435321271440766907867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921160856723842045087645 345435321271440766907867)
          ·
            refine ⟨518152981907161150361801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345435321271440766907867 518152981907161150361801)
            ·
              refine ⟨388614736430370862771351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518152981907161150361801 388614736430370862771351)
              ·
                refine ⟨582922104645556294157027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388614736430370862771351 582922104645556294157027)
                ·
                  refine ⟨874383156968334441235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582922104645556294157027 874383156968334441235541)
                  ·
                    refine ⟨10246677620722669233229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 874383156968334441235541 10246677620722669233229)
                    ·
                      rfl

theorem cell23_59866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_59866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59866 prefixEnd_59866 := by exact prefixLift 59866
  have htrace : WordTrace (prefixWord ++ tailWord_59866) baseStart_59866 baseEnd_59866 := by
    simpa [prefixWord, tailWord_59866, baseEnd_59866] using wordTrace_append hprefix tailTrace_59866
  have hstable : (prefixWord ++ tailWord_59866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59866).length < 2 ^ (prefixWord ++ tailWord_59866).sum := by decide
  have hdescent : baseEnd_59866 < baseStart_59866 := by decide
  rcases family_descends (prefixWord ++ tailWord_59866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59877 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_59877 : Nat := 118140960795 + 59877 * 2 ^ 59
def prefixEnd_59877 : Nat := 4983230072969 + 3 ^ 40 * 59877 * 2
def baseEnd_59877 : Nat := 30745681149367464662137

theorem tailTrace_59877 : CollatzResearch.WordTrace tailWord_59877 prefixEnd_59877 30745681149367464662137 := by
  unfold tailWord_59877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183893604083330022561885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1455929069388886681707923 2183893604083330022561885)
  ·
    refine ⟨818960101531248758460707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2183893604083330022561885 818960101531248758460707)
    ·
      refine ⟨1228440152296873137691061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818960101531248758460707 1228440152296873137691061)
      ·
        refine ⟨115166264277831856658537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1228440152296873137691061 115166264277831856658537)
        ·
          refine ⟨86374698208373892493903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115166264277831856658537 86374698208373892493903)
          ·
            refine ⟨129562047312560838740855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86374698208373892493903 129562047312560838740855)
            ·
              refine ⟨194343070968841258111283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129562047312560838740855 194343070968841258111283)
              ·
                refine ⟨291514606453261887166925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194343070968841258111283 291514606453261887166925)
                ·
                  refine ⟨109317977419973207687597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 291514606453261887166925 109317977419973207687597)
                  ·
                    refine ⟨40994241532489952882849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109317977419973207687597 40994241532489952882849)
                    ·
                      refine ⟨30745681149367464662137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 40994241532489952882849 30745681149367464662137)
                      ·
                        rfl

theorem cell23_59877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_59877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59877 prefixEnd_59877 := by exact prefixLift 59877
  have htrace : WordTrace (prefixWord ++ tailWord_59877) baseStart_59877 baseEnd_59877 := by
    simpa [prefixWord, tailWord_59877, baseEnd_59877] using wordTrace_append hprefix tailTrace_59877
  have hstable : (prefixWord ++ tailWord_59877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59877).length < 2 ^ (prefixWord ++ tailWord_59877).sum := by decide
  have hdescent : baseEnd_59877 < baseStart_59877 := by decide
  rcases family_descends (prefixWord ++ tailWord_59877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59894 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_59894 : Nat := 118140960795 + 59894 * 2 ^ 59
def prefixEnd_59894 : Nat := 4983230072969 + 3 ^ 40 * 59894 * 2
def baseEnd_59894 : Nat := 30754410320493898149559

theorem tailTrace_59894 : CollatzResearch.WordTrace tailWord_59894 prefixEnd_59894 30754410320493898149559 := by
  unfold tailWord_59894
  simp only [CollatzResearch.WordTrace]
  refine ⟨136532102813858870370671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1456342430014494617287157 136532102813858870370671)
  ·
    refine ⟨204798154220788305556007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136532102813858870370671 204798154220788305556007)
    ·
      refine ⟨307197231331182458334011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204798154220788305556007 307197231331182458334011)
      ·
        refine ⟨460795846996773687501017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307197231331182458334011 460795846996773687501017)
        ·
          refine ⟨345596885247580265625763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460795846996773687501017 345596885247580265625763)
          ·
            refine ⟨518395327871370398438645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345596885247580265625763 518395327871370398438645)
            ·
              refine ⟨48599561987940974853623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 518395327871370398438645 48599561987940974853623)
              ·
                refine ⟨72899342981911462280435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48599561987940974853623 72899342981911462280435)
                ·
                  refine ⟨109349014472867193420653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72899342981911462280435 109349014472867193420653)
                  ·
                    refine ⟨41005880427325197532745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109349014472867193420653 41005880427325197532745)
                    ·
                      refine ⟨30754410320493898149559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41005880427325197532745 30754410320493898149559)
                      ·
                        rfl

theorem cell23_59894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_59894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59894 prefixEnd_59894 := by exact prefixLift 59894
  have htrace : WordTrace (prefixWord ++ tailWord_59894) baseStart_59894 baseEnd_59894 := by
    simpa [prefixWord, tailWord_59894, baseEnd_59894] using wordTrace_append hprefix tailTrace_59894
  have hstable : (prefixWord ++ tailWord_59894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59894).length < 2 ^ (prefixWord ++ tailWord_59894).sum := by decide
  have hdescent : baseEnd_59894 < baseStart_59894 := by decide
  rcases family_descends (prefixWord ++ tailWord_59894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59907 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 2, 2, 2]
def baseStart_59907 : Nat := 118140960795 + 59907 * 2 ^ 59
def prefixEnd_59907 : Nat := 4983230072969 + 3 ^ 40 * 59907 * 2
def baseEnd_59907 : Nat := 30761085569002347286999

theorem tailTrace_59907 : CollatzResearch.WordTrace tailWord_59907 prefixEnd_59907 30761085569002347286999 := by
  unfold tailWord_59907
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184987793974645146153975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1456658529316430097435983 2184987793974645146153975)
  ·
    refine ⟨3277481690961967719230963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2184987793974645146153975 3277481690961967719230963)
    ·
      refine ⟨4916222536442951578846445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277481690961967719230963 4916222536442951578846445)
      ·
        refine ⟨1843583451166106842067417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916222536442951578846445 1843583451166106842067417)
        ·
          refine ⟨1382687588374580131550563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843583451166106842067417 1382687588374580131550563)
          ·
            refine ⟨2074031382561870197325845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382687588374580131550563 2074031382561870197325845)
            ·
              refine ⟨97220221057587665499649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2074031382561870197325845 97220221057587665499649)
              ·
                refine ⟨72915165793190749124737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97220221057587665499649 72915165793190749124737)
                ·
                  refine ⟨54686374344893061843553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72915165793190749124737 54686374344893061843553)
                  ·
                    refine ⟨41014780758669796382665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54686374344893061843553 41014780758669796382665)
                    ·
                      refine ⟨30761085569002347286999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41014780758669796382665 30761085569002347286999)
                      ·
                        rfl

theorem cell23_59907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_59907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59907 prefixEnd_59907 := by exact prefixLift 59907
  have htrace : WordTrace (prefixWord ++ tailWord_59907) baseStart_59907 baseEnd_59907 := by
    simpa [prefixWord, tailWord_59907, baseEnd_59907] using wordTrace_append hprefix tailTrace_59907
  have hstable : (prefixWord ++ tailWord_59907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59907).length < 2 ^ (prefixWord ++ tailWord_59907).sum := by decide
  have hdescent : baseEnd_59907 < baseStart_59907 := by decide
  rcases family_descends (prefixWord ++ tailWord_59907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59917 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_59917 : Nat := 118140960795 + 59917 * 2 ^ 59
def prefixEnd_59917 : Nat := 4983230072969 + 3 ^ 40 * 59917 * 2
def baseEnd_59917 : Nat := 10255406791849102720651

theorem tailTrace_59917 : CollatzResearch.WordTrace tailWord_59917 prefixEnd_59917 10255406791849102720651 := by
  unfold tailWord_59917
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185352523938416854018005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1456901682625611236012003 2185352523938416854018005)
  ·
    refine ⟨51219199779806645016047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2185352523938416854018005 51219199779806645016047)
    ·
      refine ⟨76828799669709967524071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51219199779806645016047 76828799669709967524071)
      ·
        refine ⟨115243199504564951286107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76828799669709967524071 115243199504564951286107)
        ·
          refine ⟨172864799256847426929161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115243199504564951286107 172864799256847426929161)
          ·
            refine ⟨129648599442635570196871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172864799256847426929161 129648599442635570196871)
            ·
              refine ⟨194472899163953355295307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129648599442635570196871 194472899163953355295307)
              ·
                refine ⟨291709348745930032942961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194472899163953355295307 291709348745930032942961)
                ·
                  refine ⟨218782011559447524707221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291709348745930032942961 218782011559447524707221)
                  ·
                    refine ⟨10255406791849102720651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 218782011559447524707221 10255406791849102720651)
                    ·
                      rfl

theorem cell23_59917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_59917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59917 prefixEnd_59917 := by exact prefixLift 59917
  have htrace : WordTrace (prefixWord ++ tailWord_59917) baseStart_59917 baseEnd_59917 := by
    simpa [prefixWord, tailWord_59917, baseEnd_59917] using wordTrace_append hprefix tailTrace_59917
  have hstable : (prefixWord ++ tailWord_59917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59917).length < 2 ^ (prefixWord ++ tailWord_59917).sum := by decide
  have hdescent : baseEnd_59917 < baseStart_59917 := by decide
  rcases family_descends (prefixWord ++ tailWord_59917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59923 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3]
def baseStart_59923 : Nat := 118140960795 + 59923 * 2 ^ 59
def prefixEnd_59923 : Nat := 4983230072969 + 3 ^ 40 * 59923 * 2
def baseEnd_59923 : Nat := 30769301259474284686925

theorem tailTrace_59923 : CollatzResearch.WordTrace tailWord_59923 prefixEnd_59923 30769301259474284686925 := by
  unfold tailWord_59923
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185571361916679878736423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1457047574611119919157615 2185571361916679878736423)
  ·
    refine ⟨3278357042875019818104635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185571361916679878736423 3278357042875019818104635)
    ·
      refine ⟨4917535564312529727156953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278357042875019818104635 4917535564312529727156953)
      ·
        refine ⟨3688151673234397295367715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4917535564312529727156953 3688151673234397295367715)
        ·
          refine ⟨5532227509851595943051573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688151673234397295367715 5532227509851595943051573)
          ·
            refine ⟨518646329048587119661085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5532227509851595943051573 518646329048587119661085)
            ·
              refine ⟨194492373393220169872907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518646329048587119661085 194492373393220169872907)
              ·
                refine ⟨291738560089830254809361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194492373393220169872907 291738560089830254809361)
                ·
                  refine ⟨218803920067372691107021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291738560089830254809361 218803920067372691107021)
                  ·
                    refine ⟨82051470025264759165133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218803920067372691107021 82051470025264759165133)
                    ·
                      refine ⟨30769301259474284686925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82051470025264759165133 30769301259474284686925)
                      ·
                        rfl

theorem cell23_59923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_59923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59923 prefixEnd_59923 := by exact prefixLift 59923
  have htrace : WordTrace (prefixWord ++ tailWord_59923) baseStart_59923 baseEnd_59923 := by
    simpa [prefixWord, tailWord_59923, baseEnd_59923] using wordTrace_append hprefix tailTrace_59923
  have hstable : (prefixWord ++ tailWord_59923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59923).length < 2 ^ (prefixWord ++ tailWord_59923).sum := by decide
  have hdescent : baseEnd_59923 < baseStart_59923 := by decide
  rcases family_descends (prefixWord ++ tailWord_59923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59924 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_59924 : Nat := 118140960795 + 59924 * 2 ^ 59
def prefixEnd_59924 : Nat := 4983230072969 + 3 ^ 40 * 59924 * 2
def baseEnd_59924 : Nat := 30769814740128780774421

theorem tailTrace_59924 : CollatzResearch.WordTrace tailWord_59924 prefixEnd_59924 30769814740128780774421 := by
  unfold tailWord_59924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092803917456528524761413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1457071889942038033015217 1092803917456528524761413)
  ·
    refine ⟨204900734523099098392765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1092803917456528524761413 204900734523099098392765)
    ·
      refine ⟨76837775446162161897287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204900734523099098392765 76837775446162161897287)
      ·
        refine ⟨115256663169243242845931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76837775446162161897287 115256663169243242845931)
        ·
          refine ⟨172884994753864864268897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115256663169243242845931 172884994753864864268897)
          ·
            refine ⟨129663746065398648201673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172884994753864864268897 129663746065398648201673)
            ·
              refine ⟨97247809549048986151255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129663746065398648201673 97247809549048986151255)
              ·
                refine ⟨145871714323573479226883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97247809549048986151255 145871714323573479226883)
                ·
                  refine ⟨218807571485360218840325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145871714323573479226883 218807571485360218840325)
                  ·
                    refine ⟨41026419653505041032561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 218807571485360218840325 41026419653505041032561)
                    ·
                      refine ⟨30769814740128780774421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41026419653505041032561 30769814740128780774421)
                      ·
                        rfl

theorem cell23_59924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_59924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59924 prefixEnd_59924 := by exact prefixLift 59924
  have htrace : WordTrace (prefixWord ++ tailWord_59924) baseStart_59924 baseEnd_59924 := by
    simpa [prefixWord, tailWord_59924, baseEnd_59924] using wordTrace_append hprefix tailTrace_59924
  have hstable : (prefixWord ++ tailWord_59924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59924).length < 2 ^ (prefixWord ++ tailWord_59924).sum := by decide
  have hdescent : baseEnd_59924 < baseStart_59924 := by decide
  rcases family_descends (prefixWord ++ tailWord_59924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59980 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_59980 : Nat := 118140960795 + 59980 * 2 ^ 59
def prefixEnd_59980 : Nat := 4983230072969 + 3 ^ 40 * 59980 * 2
def baseEnd_59980 : Nat := 30798569656780561674163

theorem tailTrace_59980 : CollatzResearch.WordTrace tailWord_59980 prefixEnd_59980 30798569656780561674163 := by
  unfold tailWord_59980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093825161355089306780697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1458433548473452409040929 1093825161355089306780697)
  ·
    refine ⟨820368871016316980085523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1093825161355089306780697 820368871016316980085523)
    ·
      refine ⟨1230553306524475470128285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 820368871016316980085523 1230553306524475470128285)
      ·
        refine ⟨461457489946678301298107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1230553306524475470128285 461457489946678301298107)
        ·
          refine ⟨692186234920017451947161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461457489946678301298107 692186234920017451947161)
          ·
            refine ⟨519139676190013088960371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692186234920017451947161 519139676190013088960371)
            ·
              refine ⟨778709514285019633440557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519139676190013088960371 778709514285019633440557)
              ·
                refine ⟨292016067856882362540209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778709514285019633440557 292016067856882362540209)
                ·
                  refine ⟨219012050892661771905157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292016067856882362540209 219012050892661771905157)
                  ·
                    refine ⟨41064759542374082232217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219012050892661771905157 41064759542374082232217)
                    ·
                      refine ⟨30798569656780561674163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41064759542374082232217 30798569656780561674163)
                      ·
                        rfl

theorem cell23_59980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_59980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59980 prefixEnd_59980 := by exact prefixLift 59980
  have htrace : WordTrace (prefixWord ++ tailWord_59980) baseStart_59980 baseEnd_59980 := by
    simpa [prefixWord, tailWord_59980, baseEnd_59980] using wordTrace_append hprefix tailTrace_59980
  have hstable : (prefixWord ++ tailWord_59980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59980).length < 2 ^ (prefixWord ++ tailWord_59980).sum := by decide
  have hdescent : baseEnd_59980 < baseStart_59980 := by decide
  rcases family_descends (prefixWord ++ tailWord_59980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59983 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_59983 : Nat := 118140960795 + 59983 * 2 ^ 59
def prefixEnd_59983 : Nat := 4983230072969 + 3 ^ 40 * 59983 * 2
def baseEnd_59983 : Nat := 30800110098744049936649

theorem tailTrace_59983 : CollatzResearch.WordTrace tailWord_59983 prefixEnd_59983 30800110098744049936649 := by
  unfold tailWord_59983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187759741699310125920603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1458506494466206750613735 2187759741699310125920603)
  ·
    refine ⟨3281639612548965188880905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187759741699310125920603 3281639612548965188880905)
    ·
      refine ⟨2461229709411723891660679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3281639612548965188880905 2461229709411723891660679)
      ·
        refine ⟨3691844564117585837491019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461229709411723891660679 3691844564117585837491019)
        ·
          refine ⟨5537766846176378756236529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691844564117585837491019 5537766846176378756236529)
          ·
            refine ⟨4153325134632284067177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537766846176378756236529 4153325134632284067177397)
            ·
              refine ⟨389374231371776631297881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4153325134632284067177397 389374231371776631297881)
              ·
                refine ⟨292030673528832473473411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389374231371776631297881 292030673528832473473411)
                ·
                  refine ⟨438046010293248710210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292030673528832473473411 438046010293248710210117)
                  ·
                    refine ⟨82133626929984133164397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438046010293248710210117 82133626929984133164397)
                    ·
                      refine ⟨30800110098744049936649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82133626929984133164397 30800110098744049936649)
                      ·
                        rfl

theorem cell23_59983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_59983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59983 prefixEnd_59983 := by exact prefixLift 59983
  have htrace : WordTrace (prefixWord ++ tailWord_59983) baseStart_59983 baseEnd_59983 := by
    simpa [prefixWord, tailWord_59983, baseEnd_59983] using wordTrace_append hprefix tailTrace_59983
  have hstable : (prefixWord ++ tailWord_59983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59983).length < 2 ^ (prefixWord ++ tailWord_59983).sum := by decide
  have hdescent : baseEnd_59983 < baseStart_59983 := by decide
  rcases family_descends (prefixWord ++ tailWord_59983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59998 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_59998 : Nat := 118140960795 + 59998 * 2 ^ 59
def prefixEnd_59998 : Nat := 4983230072969 + 3 ^ 40 * 59998 * 2
def baseEnd_59998 : Nat := 3423090256506832361009

theorem tailTrace_59998 : CollatzResearch.WordTrace tailWord_59998 prefixEnd_59998 3423090256506832361009 := by
  unfold tailWord_59998
  simp only [CollatzResearch.WordTrace]
  refine ⟨273538354580620960964581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1458871224429978458477765 273538354580620960964581)
  ·
    refine ⟨51288441483866430180859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273538354580620960964581 51288441483866430180859)
    ·
      refine ⟨76932662225799645271289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51288441483866430180859 76932662225799645271289)
      ·
        refine ⟨57699496669349733953467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76932662225799645271289 57699496669349733953467)
        ·
          refine ⟨86549245004024600930201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57699496669349733953467 86549245004024600930201)
          ·
            refine ⟨64911933753018450697651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86549245004024600930201 64911933753018450697651)
            ·
              refine ⟨97367900629527676046477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64911933753018450697651 97367900629527676046477)
              ·
                refine ⟨36512962736072878517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97367900629527676046477 36512962736072878517429)
                ·
                  refine ⟨3423090256506832361009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36512962736072878517429 3423090256506832361009)
                  ·
                    rfl

theorem cell23_59998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_59998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_59998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_59998 prefixEnd_59998 := by exact prefixLift 59998
  have htrace : WordTrace (prefixWord ++ tailWord_59998) baseStart_59998 baseEnd_59998 := by
    simpa [prefixWord, tailWord_59998, baseEnd_59998] using wordTrace_append hprefix tailTrace_59998
  have hstable : (prefixWord ++ tailWord_59998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59998).length < 2 ^ (prefixWord ++ tailWord_59998).sum := by decide
  have hdescent : baseEnd_59998 < baseStart_59998 := by decide
  rcases family_descends (prefixWord ++ tailWord_59998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60037 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 6]
def baseStart_60037 : Nat := 118140960795 + 60037 * 2 ^ 59
def prefixEnd_60037 : Nat := 4983230072969 + 3 ^ 40 * 60037 * 2
def baseEnd_60037 : Nat := 3425315339342982073489

theorem tailTrace_60037 : CollatzResearch.WordTrace tailWord_60037 prefixEnd_60037 3425315339342982073489 := by
  unfold tailWord_60037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189729283503677348386365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1459819522335784898924243 2189729283503677348386365)
  ·
    refine ⟨821148481313879005644887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2189729283503677348386365 821148481313879005644887)
    ·
      refine ⟨1231722721970818508467331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821148481313879005644887 1231722721970818508467331)
      ·
        refine ⟨1847584082956227762700997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231722721970818508467331 1847584082956227762700997)
        ·
          refine ⟨346422015554292705506437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1847584082956227762700997 346422015554292705506437)
          ·
            refine ⟨64954127916429882282457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346422015554292705506437 64954127916429882282457)
            ·
              refine ⟨48715595937322411711843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64954127916429882282457 48715595937322411711843)
              ·
                refine ⟨73073393905983617567765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48715595937322411711843 73073393905983617567765)
                ·
                  refine ⟨3425315339342982073489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73073393905983617567765 3425315339342982073489)
                  ·
                    rfl

theorem cell23_60037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_60037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60037 prefixEnd_60037 := by exact prefixLift 60037
  have htrace : WordTrace (prefixWord ++ tailWord_60037) baseStart_60037 baseEnd_60037 := by
    simpa [prefixWord, tailWord_60037, baseEnd_60037] using wordTrace_append hprefix tailTrace_60037
  have hstable : (prefixWord ++ tailWord_60037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60037).length < 2 ^ (prefixWord ++ tailWord_60037).sum := by decide
  have hdescent : baseEnd_60037 < baseStart_60037 := by decide
  rcases family_descends (prefixWord ++ tailWord_60037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60057 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 2, 3, 2]
def baseStart_60057 : Nat := 118140960795 + 60057 * 2 ^ 59
def prefixEnd_60057 : Nat := 4983230072969 + 3 ^ 40 * 60057 * 2
def baseEnd_60057 : Nat := 30838107667176760411309

theorem tailTrace_60057 : CollatzResearch.WordTrace tailWord_60057 prefixEnd_60057 30838107667176760411309 := by
  unfold tailWord_60057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190458743431220764114425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460305828954147176076283 2190458743431220764114425)
  ·
    refine ⟨1642844057573415573085819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2190458743431220764114425 1642844057573415573085819)
    ·
      refine ⟨2464266086360123359628729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1642844057573415573085819 2464266086360123359628729)
      ·
        refine ⟨1848199564770092519721547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2464266086360123359628729 1848199564770092519721547)
        ·
          refine ⟨2772299347155138779582321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848199564770092519721547 2772299347155138779582321)
          ·
            refine ⟨2079224510366354084686741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2772299347155138779582321 2079224510366354084686741)
            ·
              refine ⟨97463648923422847719691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2079224510366354084686741 97463648923422847719691)
              ·
                refine ⟨146195473385134271579537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97463648923422847719691 146195473385134271579537)
                ·
                  refine ⟨109646605038850703684653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146195473385134271579537 109646605038850703684653)
                  ·
                    refine ⟨41117476889569013881745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109646605038850703684653 41117476889569013881745)
                    ·
                      refine ⟨30838107667176760411309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41117476889569013881745 30838107667176760411309)
                      ·
                        rfl

theorem cell23_60057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_60057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60057 prefixEnd_60057 := by exact prefixLift 60057
  have htrace : WordTrace (prefixWord ++ tailWord_60057) baseStart_60057 baseEnd_60057 := by
    simpa [prefixWord, tailWord_60057, baseEnd_60057] using wordTrace_append hprefix tailTrace_60057
  have hstable : (prefixWord ++ tailWord_60057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60057).length < 2 ^ (prefixWord ++ tailWord_60057).sum := by decide
  have hdescent : baseEnd_60057 < baseStart_60057 := by decide
  rcases family_descends (prefixWord ++ tailWord_60057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60090 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_60090 : Nat := 118140960795 + 60090 * 2 ^ 59
def prefixEnd_60090 : Nat := 4983230072969 + 3 ^ 40 * 60090 * 2
def baseEnd_60090 : Nat := 30855052528775131298657

theorem tailTrace_60090 : CollatzResearch.WordTrace tailWord_60090 prefixEnd_60090 30855052528775131298657 := by
  unfold tailWord_60090
  simp only [CollatzResearch.WordTrace]
  refine ⟨547915588077916850016431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1461108234874444933377149 547915588077916850016431)
  ·
    refine ⟨821873382116875275024647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547915588077916850016431 821873382116875275024647)
    ·
      refine ⟨1232810073175312912536971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 821873382116875275024647 1232810073175312912536971)
      ·
        refine ⟨1849215109762969368805457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232810073175312912536971 1849215109762969368805457)
        ·
          refine ⟨1386911332322227026604093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849215109762969368805457 1386911332322227026604093)
          ·
            refine ⟨520091749620835134976535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1386911332322227026604093 520091749620835134976535)
            ·
              refine ⟨780137624431252702464803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520091749620835134976535 780137624431252702464803)
              ·
                refine ⟨1170206436646879053697205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780137624431252702464803 1170206436646879053697205)
                ·
                  refine ⟨109706853435644911284113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1170206436646879053697205 109706853435644911284113)
                  ·
                    refine ⟨82280140076733683463085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109706853435644911284113 82280140076733683463085)
                    ·
                      refine ⟨30855052528775131298657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82280140076733683463085 30855052528775131298657)
                      ·
                        rfl

theorem cell23_60090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_60090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60090 prefixEnd_60090 := by exact prefixLift 60090
  have htrace : WordTrace (prefixWord ++ tailWord_60090) baseStart_60090 baseEnd_60090 := by
    simpa [prefixWord, tailWord_60090, baseEnd_60090] using wordTrace_append hprefix tailTrace_60090
  have hstable : (prefixWord ++ tailWord_60090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60090).length < 2 ^ (prefixWord ++ tailWord_60090).sum := by decide
  have hdescent : baseEnd_60090 < baseStart_60090 := by decide
  rcases family_descends (prefixWord ++ tailWord_60090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60104 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_60104 : Nat := 118140960795 + 60104 * 2 ^ 59
def prefixEnd_60104 : Nat := 4983230072969 + 3 ^ 40 * 60104 * 2
def baseEnd_60104 : Nat := 30862241257938076523593

theorem tailTrace_60104 : CollatzResearch.WordTrace tailWord_60104 prefixEnd_60104 30862241257938076523593 := by
  unfold tailWord_60104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096086487130473895537683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1461448649507298527383577 1096086487130473895537683)
  ·
    refine ⟨1644129730695710843306525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096086487130473895537683 1644129730695710843306525)
    ·
      refine ⟨616548649010891566239947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1644129730695710843306525 616548649010891566239947)
      ·
        refine ⟨924822973516337349359921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616548649010891566239947 924822973516337349359921)
        ·
          refine ⟨693617230137253012019941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924822973516337349359921 693617230137253012019941)
          ·
            refine ⟨130053230650734939753739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693617230137253012019941 130053230650734939753739)
            ·
              refine ⟨195079845976102409630609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130053230650734939753739 195079845976102409630609)
              ·
                refine ⟨146309884482076807222957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195079845976102409630609 146309884482076807222957)
                ·
                  refine ⟨54866206680778802708609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146309884482076807222957 54866206680778802708609)
                  ·
                    refine ⟨41149655010584102031457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54866206680778802708609 41149655010584102031457)
                    ·
                      refine ⟨30862241257938076523593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41149655010584102031457 30862241257938076523593)
                      ·
                        rfl

theorem cell23_60104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_60104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60104 prefixEnd_60104 := by exact prefixLift 60104
  have htrace : WordTrace (prefixWord ++ tailWord_60104) baseStart_60104 baseEnd_60104 := by
    simpa [prefixWord, tailWord_60104, baseEnd_60104] using wordTrace_append hprefix tailTrace_60104
  have hstable : (prefixWord ++ tailWord_60104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60104).length < 2 ^ (prefixWord ++ tailWord_60104).sum := by decide
  have hdescent : baseEnd_60104 < baseStart_60104 := by decide
  rcases family_descends (prefixWord ++ tailWord_60104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60121 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 1, 2, 2]
def baseStart_60121 : Nat := 118140960795 + 60121 * 2 ^ 59
def prefixEnd_60121 : Nat := 4983230072969 + 3 ^ 40 * 60121 * 2
def baseEnd_60121 : Nat := 30870970429064510011015

theorem tailTrace_60121 : CollatzResearch.WordTrace tailWord_60121 prefixEnd_60121 30870970429064510011015 := by
  unfold tailWord_60121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192793015199359694444217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1461862010132906462962811 2192793015199359694444217)
  ·
    refine ⟨1644594761399519770833163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192793015199359694444217 1644594761399519770833163)
    ·
      refine ⟨2466892142099279656249745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644594761399519770833163 2466892142099279656249745)
      ·
        refine ⟨1850169106574459742187309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466892142099279656249745 1850169106574459742187309)
        ·
          refine ⟨693813414965422403320241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1850169106574459742187309 693813414965422403320241)
          ·
            refine ⟨520360061224066802490181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693813414965422403320241 520360061224066802490181)
            ·
              refine ⟨97567511479512525466909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520360061224066802490181 97567511479512525466909)
              ·
                refine ⟨36587816804817197050091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97567511479512525466909 36587816804817197050091)
                ·
                  refine ⟨54881725207225795575137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36587816804817197050091 54881725207225795575137)
                  ·
                    refine ⟨41161293905419346681353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54881725207225795575137 41161293905419346681353)
                    ·
                      refine ⟨30870970429064510011015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41161293905419346681353 30870970429064510011015)
                      ·
                        rfl

theorem cell23_60121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_60121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60121 prefixEnd_60121 := by exact prefixLift 60121
  have htrace : WordTrace (prefixWord ++ tailWord_60121) baseStart_60121 baseEnd_60121 := by
    simpa [prefixWord, tailWord_60121, baseEnd_60121] using wordTrace_append hprefix tailTrace_60121
  have hstable : (prefixWord ++ tailWord_60121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60121).length < 2 ^ (prefixWord ++ tailWord_60121).sum := by decide
  have hdescent : baseEnd_60121 < baseStart_60121 := by decide
  rcases family_descends (prefixWord ++ tailWord_60121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60148 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_60148 : Nat := 118140960795 + 60148 * 2 ^ 59
def prefixEnd_60148 : Nat := 4983230072969 + 3 ^ 40 * 60148 * 2
def baseEnd_60148 : Nat := 10294944802245301457797

theorem tailTrace_60148 : CollatzResearch.WordTrace tailWord_60148 prefixEnd_60148 10294944802245301457797 := by
  unfold tailWord_60148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096888893050771652838549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1462518524067695537118065 1096888893050771652838549)
  ·
    refine ⟨51416666861754921226807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1096888893050771652838549 51416666861754921226807)
    ·
      refine ⟨77125000292632381840211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51416666861754921226807 77125000292632381840211)
      ·
        refine ⟨115687500438948572760317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77125000292632381840211 115687500438948572760317)
        ·
          refine ⟨43382812664605714785119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115687500438948572760317 43382812664605714785119)
          ·
            refine ⟨65074218996908572177679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43382812664605714785119 65074218996908572177679)
            ·
              refine ⟨97611328495362858266519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65074218996908572177679 97611328495362858266519)
              ·
                refine ⟨146416992743044287399779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97611328495362858266519 146416992743044287399779)
                ·
                  refine ⟨219625489114566431099669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146416992743044287399779 219625489114566431099669)
                  ·
                    refine ⟨10294944802245301457797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 219625489114566431099669 10294944802245301457797)
                    ·
                      rfl

theorem cell23_60148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_60148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60148 prefixEnd_60148 := by exact prefixLift 60148
  have htrace : WordTrace (prefixWord ++ tailWord_60148) baseStart_60148 baseEnd_60148 := by
    simpa [prefixWord, tailWord_60148, baseEnd_60148] using wordTrace_append hprefix tailTrace_60148
  have hstable : (prefixWord ++ tailWord_60148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60148).length < 2 ^ (prefixWord ++ tailWord_60148).sum := by decide
  have hdescent : baseEnd_60148 < baseStart_60148 := by decide
  rcases family_descends (prefixWord ++ tailWord_60148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60177 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_60177 : Nat := 118140960795 + 60177 * 2 ^ 59
def prefixEnd_60177 : Nat := 4983230072969 + 3 ^ 40 * 60177 * 2
def baseEnd_60177 : Nat := 30899725345716290910757

theorem tailTrace_60177 : CollatzResearch.WordTrace tailWord_60177 prefixEnd_60177 30899725345716290910757 := by
  unfold tailWord_60177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194835502996481258482785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1463223668664320838988523 2194835502996481258482785)
  ·
    refine ⟨1646126627247360943862089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2194835502996481258482785 1646126627247360943862089)
    ·
      refine ⟨1234594970435520707896567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1646126627247360943862089 1234594970435520707896567)
      ·
        refine ⟨1851892455653281061844851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234594970435520707896567 1851892455653281061844851)
        ·
          refine ⟨2777838683479921592767277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851892455653281061844851 2777838683479921592767277)
          ·
            refine ⟨1041689506304970597287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2777838683479921592767277 1041689506304970597287729)
            ·
              refine ⟨781267129728727947965797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041689506304970597287729 781267129728727947965797)
              ·
                refine ⟨146487586824136490243587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781267129728727947965797 146487586824136490243587)
                ·
                  refine ⟨219731380236204735365381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146487586824136490243587 219731380236204735365381)
                  ·
                    refine ⟨41199633794288387881009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219731380236204735365381 41199633794288387881009)
                    ·
                      refine ⟨30899725345716290910757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41199633794288387881009 30899725345716290910757)
                      ·
                        rfl

theorem cell23_60177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_60177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60177 prefixEnd_60177 := by exact prefixLift 60177
  have htrace : WordTrace (prefixWord ++ tailWord_60177) baseStart_60177 baseEnd_60177 := by
    simpa [prefixWord, tailWord_60177, baseEnd_60177] using wordTrace_append hprefix tailTrace_60177
  have hstable : (prefixWord ++ tailWord_60177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60177).length < 2 ^ (prefixWord ++ tailWord_60177).sum := by decide
  have hdescent : baseEnd_60177 < baseStart_60177 := by decide
  rcases family_descends (prefixWord ++ tailWord_60177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60211 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 2, 2, 2]
def baseStart_60211 : Nat := 118140960795 + 60211 * 2 ^ 59
def prefixEnd_60211 : Nat := 4983230072969 + 3 ^ 40 * 60211 * 2
def baseEnd_60211 : Nat := 30917183687969157885601

theorem tailTrace_60211 : CollatzResearch.WordTrace tailWord_60211 prefixEnd_60211 30917183687969157885601 := by
  unfold tailWord_60211
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196075584873305065220487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1464050389915536710146991 2196075584873305065220487)
  ·
    refine ⟨3294113377309957597830731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196075584873305065220487 3294113377309957597830731)
    ·
      refine ⟨4941170065964936396746097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294113377309957597830731 4941170065964936396746097)
      ·
        refine ⟨3705877549473702297559573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941170065964936396746097 3705877549473702297559573)
        ·
          refine ⟨173713010131579795198105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3705877549473702297559573 173713010131579795198105)
          ·
            refine ⟨130284757598684846398579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173713010131579795198105 130284757598684846398579)
            ·
              refine ⟨195427136398027269597869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130284757598684846398579 195427136398027269597869)
              ·
                refine ⟨73285176149260226099201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195427136398027269597869 73285176149260226099201)
                ·
                  refine ⟨54963882111945169574401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73285176149260226099201 54963882111945169574401)
                  ·
                    refine ⟨41222911583958877180801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54963882111945169574401 41222911583958877180801)
                    ·
                      refine ⟨30917183687969157885601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41222911583958877180801 30917183687969157885601)
                      ·
                        rfl

theorem cell23_60211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2, 2].length) (baseStart_60211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60211 prefixEnd_60211 := by exact prefixLift 60211
  have htrace : WordTrace (prefixWord ++ tailWord_60211) baseStart_60211 baseEnd_60211 := by
    simpa [prefixWord, tailWord_60211, baseEnd_60211] using wordTrace_append hprefix tailTrace_60211
  have hstable : (prefixWord ++ tailWord_60211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60211).length < 2 ^ (prefixWord ++ tailWord_60211).sum := by decide
  have hdescent : baseEnd_60211 < baseStart_60211 := by decide
  rcases family_descends (prefixWord ++ tailWord_60211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60228 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_60228 : Nat := 118140960795 + 60228 * 2 ^ 59
def prefixEnd_60228 : Nat := 4983230072969 + 3 ^ 40 * 60228 * 2
def baseEnd_60228 : Nat := 30925912859095591373023

theorem tailTrace_60228 : CollatzResearch.WordTrace tailWord_60228 prefixEnd_60228 30925912859095591373023 := by
  unfold tailWord_60228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098347812905858484294669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1464463750541144645726225 1098347812905858484294669)
  ·
    refine ⟨411880429839696931610501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1098347812905858484294669 411880429839696931610501)
    ·
      refine ⟨77227580594943174676969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411880429839696931610501 77227580594943174676969)
      ·
        refine ⟨57920685446207381007727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77227580594943174676969 57920685446207381007727)
        ·
          refine ⟨86881028169311071511591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57920685446207381007727 86881028169311071511591)
          ·
            refine ⟨130321542253966607267387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86881028169311071511591 130321542253966607267387)
            ·
              refine ⟨195482313380949910901081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130321542253966607267387 195482313380949910901081)
              ·
                refine ⟨146611735035712433175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195482313380949910901081 146611735035712433175811)
                ·
                  refine ⟨219917602553568649763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146611735035712433175811 219917602553568649763717)
                  ·
                    refine ⟨41234550478794121830697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219917602553568649763717 41234550478794121830697)
                    ·
                      refine ⟨30925912859095591373023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41234550478794121830697 30925912859095591373023)
                      ·
                        rfl

theorem cell23_60228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_60228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60228 prefixEnd_60228 := by exact prefixLift 60228
  have htrace : WordTrace (prefixWord ++ tailWord_60228) baseStart_60228 baseEnd_60228 := by
    simpa [prefixWord, tailWord_60228, baseEnd_60228] using wordTrace_append hprefix tailTrace_60228
  have hstable : (prefixWord ++ tailWord_60228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60228).length < 2 ^ (prefixWord ++ tailWord_60228).sum := by decide
  have hdescent : baseEnd_60228 < baseStart_60228 := by decide
  rcases family_descends (prefixWord ++ tailWord_60228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60240 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_60240 : Nat := 118140960795 + 60240 * 2 ^ 59
def prefixEnd_60240 : Nat := 4983230072969 + 3 ^ 40 * 60240 * 2
def baseEnd_60240 : Nat := 30932074626949544422967

theorem tailTrace_60240 : CollatzResearch.WordTrace tailWord_60240 prefixEnd_60240 30932074626949544422967 := by
  unfold tailWord_60240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098566650884121509013087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1464755534512162012017449 1098566650884121509013087)
  ·
    refine ⟨1647849976326182263519631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098566650884121509013087 1647849976326182263519631)
    ·
      refine ⟨2471774964489273395279447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647849976326182263519631 2471774964489273395279447)
      ·
        refine ⟨3707662446733910092919171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471774964489273395279447 3707662446733910092919171)
        ·
          refine ⟨5561493670100865139378757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707662446733910092919171 5561493670100865139378757)
          ·
            refine ⟨1042780063143912213633517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5561493670100865139378757 1042780063143912213633517)
            ·
              refine ⟨391042523678967080112569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1042780063143912213633517 391042523678967080112569)
              ·
                refine ⟨293281892759225310084427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391042523678967080112569 293281892759225310084427)
                ·
                  refine ⟨439922839138837965126641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293281892759225310084427 439922839138837965126641)
                  ·
                    refine ⟨329942129354128473844981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 439922839138837965126641 329942129354128473844981)
                    ·
                      refine ⟨30932074626949544422967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 329942129354128473844981 30932074626949544422967)
                      ·
                        rfl

theorem cell23_60240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_60240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60240 prefixEnd_60240 := by exact prefixLift 60240
  have htrace : WordTrace (prefixWord ++ tailWord_60240) baseStart_60240 baseEnd_60240 := by
    simpa [prefixWord, tailWord_60240, baseEnd_60240] using wordTrace_append hprefix tailTrace_60240
  have hstable : (prefixWord ++ tailWord_60240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60240).length < 2 ^ (prefixWord ++ tailWord_60240).sum := by decide
  have hdescent : baseEnd_60240 < baseStart_60240 := by decide
  rcases family_descends (prefixWord ++ tailWord_60240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60247 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 2, 5]
def baseStart_60247 : Nat := 118140960795 + 60247 * 2 ^ 59
def prefixEnd_60247 : Nat := 4983230072969 + 3 ^ 40 * 60247 * 2
def baseEnd_60247 : Nat := 10311889663843672345145

theorem tailTrace_60247 : CollatzResearch.WordTrace tailWord_60247 prefixEnd_60247 10311889663843672345145 := by
  unfold tailWord_60247
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197388612742883213530995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1464925741828588809020663 2197388612742883213530995)
  ·
    refine ⟨3296082919114324820296493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197388612742883213530995 3296082919114324820296493)
    ·
      refine ⟨1236031094667871807611185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3296082919114324820296493 1236031094667871807611185)
      ·
        refine ⟨927023321000903855708389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236031094667871807611185 927023321000903855708389)
        ·
          refine ⟨173816872687669472945323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 927023321000903855708389 173816872687669472945323)
          ·
            refine ⟨260725309031504209417985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173816872687669472945323 260725309031504209417985)
            ·
              refine ⟨195543981773628157063489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260725309031504209417985 195543981773628157063489)
              ·
                refine ⟨146657986330221117797617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195543981773628157063489 146657986330221117797617)
                ·
                  refine ⟨109993489747665838348213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146657986330221117797617 109993489747665838348213)
                  ·
                    refine ⟨10311889663843672345145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109993489747665838348213 10311889663843672345145)
                    ·
                      rfl

theorem cell23_60247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_60247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60247 prefixEnd_60247 := by exact prefixLift 60247
  have htrace : WordTrace (prefixWord ++ tailWord_60247) baseStart_60247 baseEnd_60247 := by
    simpa [prefixWord, tailWord_60247, baseEnd_60247] using wordTrace_append hprefix tailTrace_60247
  have hstable : (prefixWord ++ tailWord_60247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60247).length < 2 ^ (prefixWord ++ tailWord_60247).sum := by decide
  have hdescent : baseEnd_60247 < baseStart_60247 := by decide
  rcases family_descends (prefixWord ++ tailWord_60247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60267 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 6, 2]
def baseStart_60267 : Nat := 118140960795 + 60267 * 2 ^ 59
def prefixEnd_60267 : Nat := 4983230072969 + 3 ^ 40 * 60267 * 2
def baseEnd_60267 : Nat := 30945938604620938785343

theorem tailTrace_60267 : CollatzResearch.WordTrace tailWord_60267 prefixEnd_60267 30945938604620938785343 := by
  unfold tailWord_60267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198118072670426629259055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465412048446951086172703 2198118072670426629259055)
  ·
    refine ⟨3297177109005639943888583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2198118072670426629259055 3297177109005639943888583)
    ·
      refine ⟨4945765663508459915832875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297177109005639943888583 4945765663508459915832875)
      ·
        refine ⟨7418648495262689873749313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945765663508459915832875 7418648495262689873749313)
        ·
          refine ⟨5563986371447017405311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7418648495262689873749313 5563986371447017405311985)
          ·
            refine ⟨4172989778585263053983989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563986371447017405311985 4172989778585263053983989)
            ·
              refine ⟨391217791742368411310999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4172989778585263053983989 391217791742368411310999)
              ·
                refine ⟨586826687613552616966499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391217791742368411310999 586826687613552616966499)
                ·
                  refine ⟨880240031420328925449749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586826687613552616966499 880240031420328925449749)
                  ·
                    refine ⟨41261251472827918380457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 880240031420328925449749 41261251472827918380457)
                    ·
                      refine ⟨30945938604620938785343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41261251472827918380457 30945938604620938785343)
                      ·
                        rfl

theorem cell23_60267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6, 2].length) (baseStart_60267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60267 prefixEnd_60267 := by exact prefixLift 60267
  have htrace : WordTrace (prefixWord ++ tailWord_60267) baseStart_60267 baseEnd_60267 := by
    simpa [prefixWord, tailWord_60267, baseEnd_60267] using wordTrace_append hprefix tailTrace_60267
  have hstable : (prefixWord ++ tailWord_60267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60267).length < 2 ^ (prefixWord ++ tailWord_60267).sum := by decide
  have hdescent : baseEnd_60267 < baseStart_60267 := by decide
  rcases family_descends (prefixWord ++ tailWord_60267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60280 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_60280 : Nat := 118140960795 + 60280 * 2 ^ 59
def prefixEnd_60280 : Nat := 4983230072969 + 3 ^ 40 * 60280 * 2
def baseEnd_60280 : Nat := 30952613853129387922783

theorem tailTrace_60280 : CollatzResearch.WordTrace tailWord_60280 prefixEnd_60280 30952613853129387922783 := by
  unfold tailWord_60280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099296110811664924741147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1465728147748886566321529 1099296110811664924741147)
  ·
    refine ⟨1648944166217497387111721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099296110811664924741147 1648944166217497387111721)
    ·
      refine ⟨1236708124663123040333791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1648944166217497387111721 1236708124663123040333791)
      ·
        refine ⟨1855062186994684560500687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236708124663123040333791 1855062186994684560500687)
        ·
          refine ⟨2782593280492026840751031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855062186994684560500687 2782593280492026840751031)
          ·
            refine ⟨4173889920738040261126547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782593280492026840751031 4173889920738040261126547)
            ·
              refine ⟨6260834881107060391689821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173889920738040261126547 6260834881107060391689821)
              ·
                refine ⟨2347813080415147646883683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6260834881107060391689821 2347813080415147646883683)
                ·
                  refine ⟨3521719620622721470325525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347813080415147646883683 3521719620622721470325525)
                  ·
                    refine ⟨165080607216690068921509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3521719620622721470325525 165080607216690068921509)
                    ·
                      refine ⟨30952613853129387922783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 165080607216690068921509 30952613853129387922783)
                      ·
                        rfl

theorem cell23_60280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_60280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60280 prefixEnd_60280 := by exact prefixLift 60280
  have htrace : WordTrace (prefixWord ++ tailWord_60280) baseStart_60280 baseEnd_60280 := by
    simpa [prefixWord, tailWord_60280, baseEnd_60280] using wordTrace_append hprefix tailTrace_60280
  have hstable : (prefixWord ++ tailWord_60280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60280).length < 2 ^ (prefixWord ++ tailWord_60280).sum := by decide
  have hdescent : baseEnd_60280 < baseStart_60280 := by decide
  rcases family_descends (prefixWord ++ tailWord_60280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60324 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 6]
def baseStart_60324 : Nat := 118140960795 + 60324 * 2 ^ 59
def prefixEnd_60324 : Nat := 4983230072969 + 3 ^ 40 * 60324 * 2
def baseEnd_60324 : Nat := 3441689666880801752509

theorem tailTrace_60324 : CollatzResearch.WordTrace tailWord_60324 prefixEnd_60324 3441689666880801752509 := by
  unfold tailWord_60324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100098516731962682042013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1466798022309283576056017 1100098516731962682042013)
  ·
    refine ⟨412536943774486005765755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1100098516731962682042013 412536943774486005765755)
    ·
      refine ⟨618805415661729008648633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412536943774486005765755 618805415661729008648633)
      ·
        refine ⟨464104061746296756486475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618805415661729008648633 464104061746296756486475)
        ·
          refine ⟨696156092619445134729713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464104061746296756486475 696156092619445134729713)
          ·
            refine ⟨522117069464583851047285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696156092619445134729713 522117069464583851047285)
            ·
              refine ⟨48948475262304736035683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522117069464583851047285 48948475262304736035683)
              ·
                refine ⟨73422712893457104053525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48948475262304736035683 73422712893457104053525)
                ·
                  refine ⟨3441689666880801752509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73422712893457104053525 3441689666880801752509)
                  ·
                    rfl

theorem cell23_60324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_60324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60324 prefixEnd_60324 := by exact prefixLift 60324
  have htrace : WordTrace (prefixWord ++ tailWord_60324) baseStart_60324 baseEnd_60324 := by
    simpa [prefixWord, tailWord_60324, baseEnd_60324] using wordTrace_append hprefix tailTrace_60324
  have hstable : (prefixWord ++ tailWord_60324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60324).length < 2 ^ (prefixWord ++ tailWord_60324).sum := by decide
  have hdescent : baseEnd_60324 < baseStart_60324 := by decide
  rcases family_descends (prefixWord ++ tailWord_60324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60344 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2]
def baseStart_60344 : Nat := 118140960795 + 60344 * 2 ^ 59
def prefixEnd_60344 : Nat := 4983230072969 + 3 ^ 40 * 60344 * 2
def baseEnd_60344 : Nat := 30985476615017137522489

theorem tailTrace_60344 : CollatzResearch.WordTrace tailWord_60344 prefixEnd_60344 30985476615017137522489 := by
  unfold tailWord_60344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100463246695734389906043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1467284328927645853208057 1100463246695734389906043)
  ·
    refine ⟨1650694870043601584859065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100463246695734389906043 1650694870043601584859065)
    ·
      refine ⟨1238021152532701188644299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650694870043601584859065 1238021152532701188644299)
      ·
        refine ⟨1857031728799051782966449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238021152532701188644299 1857031728799051782966449)
        ·
          refine ⟨1392773796599288837224837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857031728799051782966449 1392773796599288837224837)
          ·
            refine ⟨261145086862366656979657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1392773796599288837224837 261145086862366656979657)
            ·
              refine ⟨195858815146774992734743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261145086862366656979657 195858815146774992734743)
              ·
                refine ⟨293788222720162489102115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195858815146774992734743 293788222720162489102115)
                ·
                  refine ⟨440682334080243733653173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293788222720162489102115 440682334080243733653173)
                  ·
                    refine ⟨41313968820022850029985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 440682334080243733653173 41313968820022850029985)
                    ·
                      refine ⟨30985476615017137522489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41313968820022850029985 30985476615017137522489)
                      ·
                        rfl

theorem cell23_60344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 5, 2].length) (baseStart_60344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60344 prefixEnd_60344 := by exact prefixLift 60344
  have htrace : WordTrace (prefixWord ++ tailWord_60344) baseStart_60344 baseEnd_60344 := by
    simpa [prefixWord, tailWord_60344, baseEnd_60344] using wordTrace_append hprefix tailTrace_60344
  have hstable : (prefixWord ++ tailWord_60344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60344).length < 2 ^ (prefixWord ++ tailWord_60344).sum := by decide
  have hdescent : baseEnd_60344 < baseStart_60344 := by decide
  rcases family_descends (prefixWord ++ tailWord_60344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60351 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 1, 1, 3]
def baseStart_60351 : Nat := 118140960795 + 60351 * 2 ^ 59
def prefixEnd_60351 : Nat := 4983230072969 + 3 ^ 40 * 60351 * 2
def baseEnd_60351 : Nat := 30989070979598610134957

theorem tailTrace_60351 : CollatzResearch.WordTrace tailWord_60351 prefixEnd_60351 30989070979598610134957 := by
  unfold tailWord_60351
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201181804366108975316907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1467454536244072650211271 2201181804366108975316907)
  ·
    refine ⟨3301772706549163462975361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201181804366108975316907 3301772706549163462975361)
    ·
      refine ⟨2476329529911872597231521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3301772706549163462975361 2476329529911872597231521)
      ·
        refine ⟨1857247147433904447923641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2476329529911872597231521 1857247147433904447923641)
        ·
          refine ⟨1392935360575428335942731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857247147433904447923641 1392935360575428335942731)
          ·
            refine ⟨2089403040863142503914097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1392935360575428335942731 2089403040863142503914097)
            ·
              refine ⟨1567052280647356877935573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089403040863142503914097 1567052280647356877935573)
              ·
                refine ⟨36727787827672426826615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1567052280647356877935573 36727787827672426826615)
                ·
                  refine ⟨55091681741508640239923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36727787827672426826615 55091681741508640239923)
                  ·
                    refine ⟨82637522612262960359885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55091681741508640239923 82637522612262960359885)
                    ·
                      refine ⟨30989070979598610134957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82637522612262960359885 30989070979598610134957)
                      ·
                        rfl

theorem cell23_60351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_60351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60351 prefixEnd_60351 := by exact prefixLift 60351
  have htrace : WordTrace (prefixWord ++ tailWord_60351) baseStart_60351 baseEnd_60351 := by
    simpa [prefixWord, tailWord_60351, baseEnd_60351] using wordTrace_append hprefix tailTrace_60351
  have hstable : (prefixWord ++ tailWord_60351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60351).length < 2 ^ (prefixWord ++ tailWord_60351).sum := by decide
  have hdescent : baseEnd_60351 < baseStart_60351 := by decide
  rcases family_descends (prefixWord ++ tailWord_60351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60387 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_60387 : Nat := 118140960795 + 60387 * 2 ^ 59
def prefixEnd_60387 : Nat := 4983230072969 + 3 ^ 40 * 60387 * 2
def baseEnd_60387 : Nat := 31007556283160469284791

theorem tailTrace_60387 : CollatzResearch.WordTrace tailWord_60387 prefixEnd_60387 31007556283160469284791 := by
  unfold tailWord_60387
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202494832235687123627415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1468329888157124749084943 2202494832235687123627415)
  ·
    refine ⟨3303742248353530685441123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202494832235687123627415 3303742248353530685441123)
    ·
      refine ⟨4955613372530296028161685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303742248353530685441123 4955613372530296028161685)
      ·
        refine ⟨232294376837357626320079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4955613372530296028161685 232294376837357626320079)
        ·
          refine ⟨348441565256036439480119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232294376837357626320079 348441565256036439480119)
          ·
            refine ⟨522662347884054659220179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348441565256036439480119 522662347884054659220179)
            ·
              refine ⟨783993521826081988830269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522662347884054659220179 783993521826081988830269)
              ·
                refine ⟨293997570684780745811351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 783993521826081988830269 293997570684780745811351)
                ·
                  refine ⟨440996356027171118717027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293997570684780745811351 440996356027171118717027)
                  ·
                    refine ⟨661494534040756678075541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 440996356027171118717027 661494534040756678075541)
                    ·
                      refine ⟨31007556283160469284791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 661494534040756678075541 31007556283160469284791)
                      ·
                        rfl

theorem cell23_60387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_60387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60387 prefixEnd_60387 := by exact prefixLift 60387
  have htrace : WordTrace (prefixWord ++ tailWord_60387) baseStart_60387 baseEnd_60387 := by
    simpa [prefixWord, tailWord_60387, baseEnd_60387] using wordTrace_append hprefix tailTrace_60387
  have hstable : (prefixWord ++ tailWord_60387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60387).length < 2 ^ (prefixWord ++ tailWord_60387).sum := by decide
  have hdescent : baseEnd_60387 < baseStart_60387 := by decide
  rcases family_descends (prefixWord ++ tailWord_60387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60391 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_60391 : Nat := 118140960795 + 60391 * 2 ^ 59
def prefixEnd_60391 : Nat := 4983230072969 + 3 ^ 40 * 60391 * 2
def baseEnd_60391 : Nat := 31009610205778453634773

theorem tailTrace_60391 : CollatzResearch.WordTrace tailWord_60391 prefixEnd_60391 31009610205778453634773 := by
  unfold tailWord_60391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202640724221195806773027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1468427149480797204515351 2202640724221195806773027)
  ·
    refine ⟨3303961086331793710159541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202640724221195806773027 3303961086331793710159541)
    ·
      refine ⟨309746351843605660327457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3303961086331793710159541 309746351843605660327457)
      ·
        refine ⟨232309763882704245245593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309746351843605660327457 232309763882704245245593)
        ·
          refine ⟨174232322912028183934195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232309763882704245245593 174232322912028183934195)
          ·
            refine ⟨261348484368042275901293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174232322912028183934195 261348484368042275901293)
            ·
              refine ⟨98005681638015853462985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261348484368042275901293 98005681638015853462985)
              ·
                refine ⟨73504261228511890097239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98005681638015853462985 73504261228511890097239)
                ·
                  refine ⟨110256391842767835145859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73504261228511890097239 110256391842767835145859)
                  ·
                    refine ⟨165384587764151752718789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110256391842767835145859 165384587764151752718789)
                    ·
                      refine ⟨31009610205778453634773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 165384587764151752718789 31009610205778453634773)
                      ·
                        rfl

theorem cell23_60391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_60391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60391 prefixEnd_60391 := by exact prefixLift 60391
  have htrace : WordTrace (prefixWord ++ tailWord_60391) baseStart_60391 baseEnd_60391 := by
    simpa [prefixWord, tailWord_60391, baseEnd_60391] using wordTrace_append hprefix tailTrace_60391
  have hstable : (prefixWord ++ tailWord_60391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60391).length < 2 ^ (prefixWord ++ tailWord_60391).sum := by decide
  have hdescent : baseEnd_60391 < baseStart_60391 := by decide
  rcases family_descends (prefixWord ++ tailWord_60391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60405 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_60405 : Nat := 118140960795 + 60405 * 2 ^ 59
def prefixEnd_60405 : Nat := 4983230072969 + 3 ^ 40 * 60405 * 2
def baseEnd_60405 : Nat := 10338932978313799619903

theorem tailTrace_60405 : CollatzResearch.WordTrace tailWord_60405 prefixEnd_60405 10338932978313799619903 := by
  unfold tailWord_60405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203151346170476197782669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1468767564113650798521779 2203151346170476197782669)
  ·
    refine ⟨826181754813928574168501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2203151346170476197782669 826181754813928574168501)
    ·
      refine ⟨77454539513805803828297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 826181754813928574168501 77454539513805803828297)
      ·
        refine ⟨58090904635354352871223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77454539513805803828297 58090904635354352871223)
        ·
          refine ⟨87136356953031529306835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58090904635354352871223 87136356953031529306835)
          ·
            refine ⟨130704535429547293960253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87136356953031529306835 130704535429547293960253)
            ·
              refine ⟨49014200786080235235095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130704535429547293960253 49014200786080235235095)
              ·
                refine ⟨73521301179120352852643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49014200786080235235095 73521301179120352852643)
                ·
                  refine ⟨110281951768680529278965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73521301179120352852643 110281951768680529278965)
                  ·
                    refine ⟨10338932978313799619903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110281951768680529278965 10338932978313799619903)
                    ·
                      rfl

theorem cell23_60405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_60405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60405 prefixEnd_60405 := by exact prefixLift 60405
  have htrace : WordTrace (prefixWord ++ tailWord_60405) baseStart_60405 baseEnd_60405 := by
    simpa [prefixWord, tailWord_60405, baseEnd_60405] using wordTrace_append hprefix tailTrace_60405
  have hstable : (prefixWord ++ tailWord_60405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60405).length < 2 ^ (prefixWord ++ tailWord_60405).sum := by decide
  have hdescent : baseEnd_60405 < baseStart_60405 := by decide
  rcases family_descends (prefixWord ++ tailWord_60405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60408 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 1, 2, 2]
def baseStart_60408 : Nat := 118140960795 + 60408 * 2 ^ 59
def prefixEnd_60408 : Nat := 4983230072969 + 3 ^ 40 * 60408 * 2
def baseEnd_60408 : Nat := 31018339376904887122195

theorem tailTrace_60408 : CollatzResearch.WordTrace tailWord_60408 prefixEnd_60408 31018339376904887122195 := by
  unfold tailWord_60408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101630382579803855070939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1468840510106405140094585 1101630382579803855070939)
  ·
    refine ⟨1652445573869705782606409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101630382579803855070939 1652445573869705782606409)
    ·
      refine ⟨1239334180402279336954807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1652445573869705782606409 1239334180402279336954807)
      ·
        refine ⟨1859001270603419005432211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239334180402279336954807 1859001270603419005432211)
        ·
          refine ⟨2788501905905128508148317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859001270603419005432211 2788501905905128508148317)
          ·
            refine ⟨1045688214714423190555619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2788501905905128508148317 1045688214714423190555619)
            ·
              refine ⟨1568532322071634785833429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045688214714423190555619 1568532322071634785833429)
              ·
                refine ⟨36762476298553940292971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1568532322071634785833429 36762476298553940292971)
                ·
                  refine ⟨55143714447830910439457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36762476298553940292971 55143714447830910439457)
                  ·
                    refine ⟨41357785835873182829593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55143714447830910439457 41357785835873182829593)
                    ·
                      refine ⟨31018339376904887122195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41357785835873182829593 31018339376904887122195)
                      ·
                        rfl

theorem cell23_60408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 2, 2].length) (baseStart_60408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60408 prefixEnd_60408 := by exact prefixLift 60408
  have htrace : WordTrace (prefixWord ++ tailWord_60408) baseStart_60408 baseEnd_60408 := by
    simpa [prefixWord, tailWord_60408, baseEnd_60408] using wordTrace_append hprefix tailTrace_60408
  have hstable : (prefixWord ++ tailWord_60408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60408).length < 2 ^ (prefixWord ++ tailWord_60408).sum := by decide
  have hdescent : baseEnd_60408 < baseStart_60408 := by decide
  rcases family_descends (prefixWord ++ tailWord_60408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60414 : List Nat := [4, 2, 2, 2, 2, 11]
def baseStart_60414 : Nat := 118140960795 + 60414 * 2 ^ 59
def prefixEnd_60414 : Nat := 4983230072969 + 3 ^ 40 * 60414 * 2
def baseEnd_60414 : Nat := 127660165682435652869

theorem tailTrace_60414 : CollatzResearch.WordTrace tailWord_60414 prefixEnd_60414 127660165682435652869 := by
  unfold tailWord_60414
  simp only [CollatzResearch.WordTrace]
  refine ⟨275434950392233841857537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1468986402091913823240197 275434950392233841857537)
  ·
    refine ⟨206576212794175381393153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275434950392233841857537 206576212794175381393153)
    ·
      refine ⟨154932159595631536044865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206576212794175381393153 154932159595631536044865)
      ·
        refine ⟨116199119696723652033649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154932159595631536044865 116199119696723652033649)
        ·
          refine ⟨87149339772542739025237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116199119696723652033649 87149339772542739025237)
          ·
            refine ⟨127660165682435652869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 87149339772542739025237 127660165682435652869)
            ·
              rfl

theorem cell23_60414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 11].length) (baseStart_60414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60414 prefixEnd_60414 := by exact prefixLift 60414
  have htrace : WordTrace (prefixWord ++ tailWord_60414) baseStart_60414 baseEnd_60414 := by
    simpa [prefixWord, tailWord_60414, baseEnd_60414] using wordTrace_append hprefix tailTrace_60414
  have hstable : (prefixWord ++ tailWord_60414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60414).length < 2 ^ (prefixWord ++ tailWord_60414).sum := by decide
  have hdescent : baseEnd_60414 < baseStart_60414 := by decide
  rcases family_descends (prefixWord ++ tailWord_60414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60427 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 7]
def baseStart_60427 : Nat := 118140960795 + 60427 * 2 ^ 59
def prefixEnd_60427 : Nat := 4983230072969 + 3 ^ 40 * 60427 * 2
def baseEnd_60427 : Nat := 10342698503113437594869

theorem tailTrace_60427 : CollatzResearch.WordTrace tailWord_60427 prefixEnd_60427 10342698503113437594869 := by
  unfold tailWord_60427
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203953752090773955083535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469302501393849303389023 2203953752090773955083535)
  ·
    refine ⟨3305930628136160932625303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2203953752090773955083535 3305930628136160932625303)
    ·
      refine ⟨4958895942204241398937955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3305930628136160932625303 4958895942204241398937955)
      ·
        refine ⟨7438343913306362098406933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958895942204241398937955 7438343913306362098406933)
        ·
          refine ⟨348672370936235723362825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7438343913306362098406933 348672370936235723362825)
          ·
            refine ⟨261504278202176792522119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348672370936235723362825 261504278202176792522119)
            ·
              refine ⟨392256417303265188783179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261504278202176792522119 392256417303265188783179)
              ·
                refine ⟨588384625954897783174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392256417303265188783179 588384625954897783174769)
                ·
                  refine ⟨441288469466173337381077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588384625954897783174769 441288469466173337381077)
                  ·
                    refine ⟨10342698503113437594869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 441288469466173337381077 10342698503113437594869)
                    ·
                      rfl

theorem cell23_60427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_60427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60427 prefixEnd_60427 := by exact prefixLift 60427
  have htrace : WordTrace (prefixWord ++ tailWord_60427) baseStart_60427 baseEnd_60427 := by
    simpa [prefixWord, tailWord_60427, baseEnd_60427] using wordTrace_append hprefix tailTrace_60427
  have hstable : (prefixWord ++ tailWord_60427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60427).length < 2 ^ (prefixWord ++ tailWord_60427).sum := by decide
  have hdescent : baseEnd_60427 < baseStart_60427 := by decide
  rcases family_descends (prefixWord ++ tailWord_60427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60441 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_60441 : Nat := 118140960795 + 60441 * 2 ^ 59
def prefixEnd_60441 : Nat := 4983230072969 + 3 ^ 40 * 60441 * 2
def baseEnd_60441 : Nat := 31035284238503258009543

theorem tailTrace_60441 : CollatzResearch.WordTrace tailWord_60441 prefixEnd_60441 31035284238503258009543 := by
  unfold tailWord_60441
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204464374040054346093177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469642916026702897395451 2204464374040054346093177)
  ·
    refine ⟨1653348280530040759569883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2204464374040054346093177 1653348280530040759569883)
    ·
      refine ⟨2480022420795061139354825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653348280530040759569883 2480022420795061139354825)
      ·
        refine ⟨1860016815596295854516119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480022420795061139354825 1860016815596295854516119)
        ·
          refine ⟨2790025223394443781774179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860016815596295854516119 2790025223394443781774179)
          ·
            refine ⟨4185037835091665672661269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790025223394443781774179 4185037835091665672661269)
            ·
              refine ⟨196173648519921828405997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4185037835091665672661269 196173648519921828405997)
              ·
                refine ⟨73565118194970685652249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196173648519921828405997 73565118194970685652249)
                ·
                  refine ⟨55173838646228014239187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73565118194970685652249 55173838646228014239187)
                  ·
                    refine ⟨82760757969342021358781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55173838646228014239187 82760757969342021358781)
                    ·
                      refine ⟨31035284238503258009543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82760757969342021358781 31035284238503258009543)
                      ·
                        rfl

theorem cell23_60441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_60441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60441 prefixEnd_60441 := by exact prefixLift 60441
  have htrace : WordTrace (prefixWord ++ tailWord_60441) baseStart_60441 baseEnd_60441 := by
    simpa [prefixWord, tailWord_60441, baseEnd_60441] using wordTrace_append hprefix tailTrace_60441
  have hstable : (prefixWord ++ tailWord_60441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60441).length < 2 ^ (prefixWord ++ tailWord_60441).sum := by decide
  have hdescent : baseEnd_60441 < baseStart_60441 := by decide
  rcases family_descends (prefixWord ++ tailWord_60441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60451 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 3, 3, 2]
def baseStart_60451 : Nat := 118140960795 + 60451 * 2 ^ 59
def prefixEnd_60451 : Nat := 4983230072969 + 3 ^ 40 * 60451 * 2
def baseEnd_60451 : Nat := 31040419045048218884497

theorem tailTrace_60451 : CollatzResearch.WordTrace tailWord_60451 prefixEnd_60451 31040419045048218884497 := by
  unfold tailWord_60451
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204829104003826053957207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469886069335884035971471 2204829104003826053957207)
  ·
    refine ⟨3307243656005739080935811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204829104003826053957207 3307243656005739080935811)
    ·
      refine ⟨4960865484008608621403717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3307243656005739080935811 4960865484008608621403717)
      ·
        refine ⟨930162278251614116513197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4960865484008608621403717 930162278251614116513197)
        ·
          refine ⟨348810854344355293692449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930162278251614116513197 348810854344355293692449)
          ·
            refine ⟨261608140758266470269337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348810854344355293692449 261608140758266470269337)
            ·
              refine ⟨196206105568699852702003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261608140758266470269337 196206105568699852702003)
              ·
                refine ⟨294309158353049779053005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196206105568699852702003 294309158353049779053005)
                ·
                  refine ⟨110365934382393667144877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294309158353049779053005 110365934382393667144877)
                  ·
                    refine ⟨41387225393397625179329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110365934382393667144877 41387225393397625179329)
                    ·
                      refine ⟨31040419045048218884497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41387225393397625179329 31040419045048218884497)
                      ·
                        rfl

theorem cell23_60451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_60451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60451 prefixEnd_60451 := by exact prefixLift 60451
  have htrace : WordTrace (prefixWord ++ tailWord_60451) baseStart_60451 baseEnd_60451 := by
    simpa [prefixWord, tailWord_60451, baseEnd_60451] using wordTrace_append hprefix tailTrace_60451
  have hstable : (prefixWord ++ tailWord_60451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60451).length < 2 ^ (prefixWord ++ tailWord_60451).sum := by decide
  have hdescent : baseEnd_60451 < baseStart_60451 := by decide
  rcases family_descends (prefixWord ++ tailWord_60451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60467 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_60467 : Nat := 118140960795 + 60467 * 2 ^ 59
def prefixEnd_60467 : Nat := 4983230072969 + 3 ^ 40 * 60467 * 2
def baseEnd_60467 : Nat := 31048634735520156284423

theorem tailTrace_60467 : CollatzResearch.WordTrace tailWord_60467 prefixEnd_60467 31048634735520156284423 := by
  unfold tailWord_60467
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205412671945860786539655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1470275114630573857693103 2205412671945860786539655)
  ·
    refine ⟨3308119007918791179809483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2205412671945860786539655 3308119007918791179809483)
    ·
      refine ⟨4962178511878186769714225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308119007918791179809483 4962178511878186769714225)
      ·
        refine ⟨3721633883908640077285669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962178511878186769714225 3721633883908640077285669)
        ·
          refine ⟨697806353232870014491063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3721633883908640077285669 697806353232870014491063)
          ·
            refine ⟨1046709529849305021736595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697806353232870014491063 1046709529849305021736595)
            ·
              refine ⟨1570064294773957532604893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046709529849305021736595 1570064294773957532604893)
              ·
                refine ⟨588774110540234074726835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1570064294773957532604893 588774110540234074726835)
                ·
                  refine ⟨883161165810351112090253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588774110540234074726835 883161165810351112090253)
                  ·
                    refine ⟨331185437178881667033845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883161165810351112090253 331185437178881667033845)
                    ·
                      refine ⟨31048634735520156284423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 331185437178881667033845 31048634735520156284423)
                      ·
                        rfl

theorem cell23_60467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_60467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60467 prefixEnd_60467 := by exact prefixLift 60467
  have htrace : WordTrace (prefixWord ++ tailWord_60467) baseStart_60467 baseEnd_60467 := by
    simpa [prefixWord, tailWord_60467, baseEnd_60467] using wordTrace_append hprefix tailTrace_60467
  have hstable : (prefixWord ++ tailWord_60467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60467).length < 2 ^ (prefixWord ++ tailWord_60467).sum := by decide
  have hdescent : baseEnd_60467 < baseStart_60467 := by decide
  rcases family_descends (prefixWord ++ tailWord_60467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60494 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_60494 : Nat := 118140960795 + 60494 * 2 ^ 59
def prefixEnd_60494 : Nat := 4983230072969 + 3 ^ 40 * 60494 * 2
def baseEnd_60494 : Nat := 31062498713191550646799

theorem tailTrace_60494 : CollatzResearch.WordTrace tailWord_60494 prefixEnd_60494 31062498713191550646799 := by
  unfold tailWord_60494
  simp only [CollatzResearch.WordTrace]
  refine ⟨275799680356005549721567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1470931628565362931848357 275799680356005549721567)
  ·
    refine ⟨413699520534008324582351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275799680356005549721567 413699520534008324582351)
    ·
      refine ⟨620549280801012486873527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413699520534008324582351 620549280801012486873527)
      ·
        refine ⟨930823921201518730310291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620549280801012486873527 930823921201518730310291)
        ·
          refine ⟨1396235881802278095465437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930823921201518730310291 1396235881802278095465437)
          ·
            refine ⟨523588455675854285799539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1396235881802278095465437 523588455675854285799539)
            ·
              refine ⟨785382683513781428699309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523588455675854285799539 785382683513781428699309)
              ·
                refine ⟨294518506317668035762241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 785382683513781428699309 294518506317668035762241)
                ·
                  refine ⟨220888879738251026821681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294518506317668035762241 220888879738251026821681)
                  ·
                    refine ⟨165666659803688270116261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220888879738251026821681 165666659803688270116261)
                    ·
                      refine ⟨31062498713191550646799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 165666659803688270116261 31062498713191550646799)
                      ·
                        rfl

theorem cell23_60494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_60494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60494 prefixEnd_60494 := by exact prefixLift 60494
  have htrace : WordTrace (prefixWord ++ tailWord_60494) baseStart_60494 baseEnd_60494 := by
    simpa [prefixWord, tailWord_60494, baseEnd_60494] using wordTrace_append hprefix tailTrace_60494
  have hstable : (prefixWord ++ tailWord_60494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60494).length < 2 ^ (prefixWord ++ tailWord_60494).sum := by decide
  have hdescent : baseEnd_60494 < baseStart_60494 := by decide
  rcases family_descends (prefixWord ++ tailWord_60494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60498 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_60498 : Nat := 118140960795 + 60498 * 2 ^ 59
def prefixEnd_60498 : Nat := 4983230072969 + 3 ^ 40 * 60498 * 2
def baseEnd_60498 : Nat := 31064552635809534996781

theorem tailTrace_60498 : CollatzResearch.WordTrace tailWord_60498 prefixEnd_60498 31064552635809534996781 := by
  unfold tailWord_60498
  simp only [CollatzResearch.WordTrace]
  refine ⟨551635833708388270229537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1471028889889035387278765 551635833708388270229537)
  ·
    refine ⟨413726875281291202672153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 551635833708388270229537 413726875281291202672153)
    ·
      refine ⟨310295156460968402004115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413726875281291202672153 310295156460968402004115)
      ·
        refine ⟨465442734691452603006173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310295156460968402004115 465442734691452603006173)
        ·
          refine ⟨174541025509294726127315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465442734691452603006173 174541025509294726127315)
          ·
            refine ⟨261811538263942089190973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174541025509294726127315 261811538263942089190973)
            ·
              refine ⟨98179326848978283446615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261811538263942089190973 98179326848978283446615)
              ·
                refine ⟨147268990273467425169923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98179326848978283446615 147268990273467425169923)
                ·
                  refine ⟨220903485410201137754885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147268990273467425169923 220903485410201137754885)
                  ·
                    refine ⟨41419403514412713329041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220903485410201137754885 41419403514412713329041)
                    ·
                      refine ⟨31064552635809534996781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41419403514412713329041 31064552635809534996781)
                      ·
                        rfl

theorem cell23_60498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_60498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60498 prefixEnd_60498 := by exact prefixLift 60498
  have htrace : WordTrace (prefixWord ++ tailWord_60498) baseStart_60498 baseEnd_60498 := by
    simpa [prefixWord, tailWord_60498, baseEnd_60498] using wordTrace_append hprefix tailTrace_60498
  have hstable : (prefixWord ++ tailWord_60498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60498).length < 2 ^ (prefixWord ++ tailWord_60498).sum := by decide
  have hdescent : baseEnd_60498 < baseStart_60498 := by decide
  rcases family_descends (prefixWord ++ tailWord_60498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60521 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 5]
def baseStart_60521 : Nat := 118140960795 + 60521 * 2 ^ 59
def prefixEnd_60521 : Nat := 4983230072969 + 3 ^ 40 * 60521 * 2
def baseEnd_60521 : Nat := 3452929187873660556575

theorem tailTrace_60521 : CollatzResearch.WordTrace tailWord_60521 prefixEnd_60521 3452929187873660556575 := by
  unfold tailWord_60521
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207382213750228009005417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1471588142500152006003611 2207382213750228009005417)
  ·
    refine ⟨1655536660312671006754063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2207382213750228009005417 1655536660312671006754063)
    ·
      refine ⟨2483304990469006510131095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655536660312671006754063 2483304990469006510131095)
      ·
        refine ⟨3724957485703509765196643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483304990469006510131095 3724957485703509765196643)
        ·
          refine ⟨5587436228555264647794965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724957485703509765196643 5587436228555264647794965)
          ·
            refine ⟨261911073213528030365389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5587436228555264647794965 261911073213528030365389)
            ·
              refine ⟨98216652455073011387021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261911073213528030365389 98216652455073011387021)
              ·
                refine ⟨36831244670652379270133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98216652455073011387021 36831244670652379270133)
                ·
                  refine ⟨3452929187873660556575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36831244670652379270133 3452929187873660556575)
                  ·
                    rfl

theorem cell23_60521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 5].length) (baseStart_60521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60521 prefixEnd_60521 := by exact prefixLift 60521
  have htrace : WordTrace (prefixWord ++ tailWord_60521) baseStart_60521 baseEnd_60521 := by
    simpa [prefixWord, tailWord_60521, baseEnd_60521] using wordTrace_append hprefix tailTrace_60521
  have hstable : (prefixWord ++ tailWord_60521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60521).length < 2 ^ (prefixWord ++ tailWord_60521).sum := by decide
  have hdescent : baseEnd_60521 < baseStart_60521 := by decide
  rcases family_descends (prefixWord ++ tailWord_60521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60541 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_60541 : Nat := 118140960795 + 60541 * 2 ^ 59
def prefixEnd_60541 : Nat := 4983230072969 + 3 ^ 40 * 60541 * 2
def baseEnd_60541 : Nat := 31086632303952866759083

theorem tailTrace_60541 : CollatzResearch.WordTrace tailWord_60541 prefixEnd_60541 31086632303952866759083 := by
  unfold tailWord_60541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208111673677771424733477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1472074449118514283155651 2208111673677771424733477)
  ·
    refine ⟨414020938814582142137527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2208111673677771424733477 414020938814582142137527)
    ·
      refine ⟨621031408221873213206291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414020938814582142137527 621031408221873213206291)
      ·
        refine ⟨931547112332809819809437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621031408221873213206291 931547112332809819809437)
        ·
          refine ⟨349330167124803682428539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 931547112332809819809437 349330167124803682428539)
          ·
            refine ⟨523995250687205523642809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349330167124803682428539 523995250687205523642809)
            ·
              refine ⟨392996438015404142732107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 523995250687205523642809 392996438015404142732107)
              ·
                refine ⟨589494657023106214098161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392996438015404142732107 589494657023106214098161)
                ·
                  refine ⟨442120992767329660573621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 589494657023106214098161 442120992767329660573621)
                  ·
                    refine ⟨41448843071937155678777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 442120992767329660573621 41448843071937155678777)
                    ·
                      refine ⟨31086632303952866759083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41448843071937155678777 31086632303952866759083)
                      ·
                        rfl

theorem cell23_60541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_60541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60541 prefixEnd_60541 := by exact prefixLift 60541
  have htrace : WordTrace (prefixWord ++ tailWord_60541) baseStart_60541 baseEnd_60541 := by
    simpa [prefixWord, tailWord_60541, baseEnd_60541] using wordTrace_append hprefix tailTrace_60541
  have hstable : (prefixWord ++ tailWord_60541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60541).length < 2 ^ (prefixWord ++ tailWord_60541).sum := by decide
  have hdescent : baseEnd_60541 < baseStart_60541 := by decide
  rcases family_descends (prefixWord ++ tailWord_60541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60549 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_60549 : Nat := 118140960795 + 60549 * 2 ^ 59
def prefixEnd_60549 : Nat := 4983230072969 + 3 ^ 40 * 60549 * 2
def baseEnd_60549 : Nat := 31090740149188835459047

theorem tailTrace_60549 : CollatzResearch.WordTrace tailWord_60549 prefixEnd_60549 31090740149188835459047 := by
  unfold tailWord_60549
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208403457648788791024701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1472268971765859194016467 2208403457648788791024701)
  ·
    refine ⟨828151296618295796634263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2208403457648788791024701 828151296618295796634263)
    ·
      refine ⟨1242226944927443694951395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828151296618295796634263 1242226944927443694951395)
      ·
        refine ⟨1863340417391165542427093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242226944927443694951395 1863340417391165542427093)
        ·
          refine ⟨43672041032605442400635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1863340417391165542427093 43672041032605442400635)
          ·
            refine ⟨65508061548908163600953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43672041032605442400635 65508061548908163600953)
            ·
              refine ⟨49131046161681122700715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65508061548908163600953 49131046161681122700715)
              ·
                refine ⟨73696569242521684051073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49131046161681122700715 73696569242521684051073)
                ·
                  refine ⟨55272426931891263038305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73696569242521684051073 55272426931891263038305)
                  ·
                    refine ⟨41454320198918447278729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55272426931891263038305 41454320198918447278729)
                    ·
                      refine ⟨31090740149188835459047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41454320198918447278729 31090740149188835459047)
                      ·
                        rfl

theorem cell23_60549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_60549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60549 prefixEnd_60549 := by exact prefixLift 60549
  have htrace : WordTrace (prefixWord ++ tailWord_60549) baseStart_60549 baseEnd_60549 := by
    simpa [prefixWord, tailWord_60549, baseEnd_60549] using wordTrace_append hprefix tailTrace_60549
  have hstable : (prefixWord ++ tailWord_60549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60549).length < 2 ^ (prefixWord ++ tailWord_60549).sum := by decide
  have hdescent : baseEnd_60549 < baseStart_60549 := by decide
  rcases family_descends (prefixWord ++ tailWord_60549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60591 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_60591 : Nat := 118140960795 + 60591 * 2 ^ 59
def prefixEnd_60591 : Nat := 4983230072969 + 3 ^ 40 * 60591 * 2
def baseEnd_60591 : Nat := 31112306336677671133853

theorem tailTrace_60591 : CollatzResearch.WordTrace tailWord_60591 prefixEnd_60591 31112306336677671133853 := by
  unfold tailWord_60591
  simp only [CollatzResearch.WordTrace]
  refine ⟨2209935323496629964053627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1473290215664419976035751 2209935323496629964053627)
  ·
    refine ⟨3314902985244944946080441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2209935323496629964053627 3314902985244944946080441)
    ·
      refine ⟨2486177238933708709560331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3314902985244944946080441 2486177238933708709560331)
      ·
        refine ⟨3729265858400563064340497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486177238933708709560331 3729265858400563064340497)
        ·
          refine ⟨2796949393800422298255373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3729265858400563064340497 2796949393800422298255373)
          ·
            refine ⟨1048856022675158361845765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2796949393800422298255373 1048856022675158361845765)
            ·
              refine ⟨196660504251592192846081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1048856022675158361845765 196660504251592192846081)
              ·
                refine ⟨147495378188694144634561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196660504251592192846081 147495378188694144634561)
                ·
                  refine ⟨110621533641520608475921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147495378188694144634561 110621533641520608475921)
                  ·
                    refine ⟨82966150231140456356941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110621533641520608475921 82966150231140456356941)
                    ·
                      refine ⟨31112306336677671133853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 82966150231140456356941 31112306336677671133853)
                      ·
                        rfl

theorem cell23_60591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_60591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60591 prefixEnd_60591 := by exact prefixLift 60591
  have htrace : WordTrace (prefixWord ++ tailWord_60591) baseStart_60591 baseEnd_60591 := by
    simpa [prefixWord, tailWord_60591, baseEnd_60591] using wordTrace_append hprefix tailTrace_60591
  have hstable : (prefixWord ++ tailWord_60591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60591).length < 2 ^ (prefixWord ++ tailWord_60591).sum := by decide
  have hdescent : baseEnd_60591 < baseStart_60591 := by decide
  rcases family_descends (prefixWord ++ tailWord_60591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60634 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_60634 : Nat := 118140960795 + 60634 * 2 ^ 59
def prefixEnd_60634 : Nat := 4983230072969 + 3 ^ 40 * 60634 * 2
def baseEnd_60634 : Nat := 31134386004821002896155

theorem tailTrace_60634 : CollatzResearch.WordTrace tailWord_60634 prefixEnd_60634 31134386004821002896155 := by
  unfold tailWord_60634
  simp only [CollatzResearch.WordTrace]
  refine ⟨552875915585212076967239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1474335774893898871912637 552875915585212076967239)
  ·
    refine ⟨829313873377818115450859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552875915585212076967239 829313873377818115450859)
    ·
      refine ⟨1243970810066727173176289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829313873377818115450859 1243970810066727173176289)
      ·
        refine ⟨932978107550045379882217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243970810066727173176289 932978107550045379882217)
        ·
          refine ⟨699733580662534034911663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932978107550045379882217 699733580662534034911663)
          ·
            refine ⟨1049600370993801052367495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699733580662534034911663 1049600370993801052367495)
            ·
              refine ⟨1574400556490701578551243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049600370993801052367495 1574400556490701578551243)
              ·
                refine ⟨2361600834736052367826865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1574400556490701578551243 2361600834736052367826865)
                ·
                  refine ⟨1771200626052039275870149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2361600834736052367826865 1771200626052039275870149)
                  ·
                    refine ⟨332100117384757364225653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1771200626052039275870149 332100117384757364225653)
                    ·
                      refine ⟨31134386004821002896155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 332100117384757364225653 31134386004821002896155)
                      ·
                        rfl

theorem cell23_60634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_60634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60634 prefixEnd_60634 := by exact prefixLift 60634
  have htrace : WordTrace (prefixWord ++ tailWord_60634) baseStart_60634 baseEnd_60634 := by
    simpa [prefixWord, tailWord_60634, baseEnd_60634] using wordTrace_append hprefix tailTrace_60634
  have hstable : (prefixWord ++ tailWord_60634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60634).length < 2 ^ (prefixWord ++ tailWord_60634).sum := by decide
  have hdescent : baseEnd_60634 < baseStart_60634 := by decide
  rcases family_descends (prefixWord ++ tailWord_60634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60645 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 6]
def baseStart_60645 : Nat := 118140960795 + 60645 * 2 ^ 59
def prefixEnd_60645 : Nat := 4983230072969 + 3 ^ 40 * 60645 * 2
def baseEnd_60645 : Nat := 3460003810224495539845

theorem tailTrace_60645 : CollatzResearch.WordTrace tailWord_60645 prefixEnd_60645 3460003810224495539845 := by
  unfold tailWord_60645
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211904865300997186519389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1474603243533998124346259 2211904865300997186519389)
  ·
    refine ⟨829464324487873944944771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2211904865300997186519389 829464324487873944944771)
    ·
      refine ⟨1244196486731810917417157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829464324487873944944771 1244196486731810917417157)
      ·
        refine ⟨233286841262214547015717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1244196486731810917417157 233286841262214547015717)
        ·
          refine ⟨43741282736665227565447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233286841262214547015717 43741282736665227565447)
          ·
            refine ⟨65611924104997841348171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43741282736665227565447 65611924104997841348171)
            ·
              refine ⟨98417886157496762022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65611924104997841348171 98417886157496762022257)
              ·
                refine ⟨73813414618122571516693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98417886157496762022257 73813414618122571516693)
                ·
                  refine ⟨3460003810224495539845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73813414618122571516693 3460003810224495539845)
                  ·
                    rfl

theorem cell23_60645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_60645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60645 prefixEnd_60645 := by exact prefixLift 60645
  have htrace : WordTrace (prefixWord ++ tailWord_60645) baseStart_60645 baseEnd_60645 := by
    simpa [prefixWord, tailWord_60645, baseEnd_60645] using wordTrace_append hprefix tailTrace_60645
  have hstable : (prefixWord ++ tailWord_60645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60645).length < 2 ^ (prefixWord ++ tailWord_60645).sum := by decide
  have hdescent : baseEnd_60645 < baseStart_60645 := by decide
  rcases family_descends (prefixWord ++ tailWord_60645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60648 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_60648 : Nat := 118140960795 + 60648 * 2 ^ 59
def prefixEnd_60648 : Nat := 4983230072969 + 3 ^ 40 * 60648 * 2
def baseEnd_60648 : Nat := 31141574733983948121091

theorem tailTrace_60648 : CollatzResearch.WordTrace tailWord_60648 prefixEnd_60648 31141574733983948121091 := by
  unfold tailWord_60648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106007142145064349439299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1474676189526752465919065 1106007142145064349439299)
  ·
    refine ⟨1659010713217596524158949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1106007142145064349439299 1659010713217596524158949)
    ·
      refine ⟨311064508728299348279803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1659010713217596524158949 311064508728299348279803)
      ·
        refine ⟨466596763092449022419705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311064508728299348279803 466596763092449022419705)
        ·
          refine ⟨349947572319336766814779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466596763092449022419705 349947572319336766814779)
          ·
            refine ⟨524921358479005150222169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349947572319336766814779 524921358479005150222169)
            ·
              refine ⟨393691018859253862666627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524921358479005150222169 393691018859253862666627)
              ·
                refine ⟨590536528288880793999941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393691018859253862666627 590536528288880793999941)
                ·
                  refine ⟨110725599054165148874989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 590536528288880793999941 110725599054165148874989)
                  ·
                    refine ⟨41522099645311930828121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110725599054165148874989 41522099645311930828121)
                    ·
                      refine ⟨31141574733983948121091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41522099645311930828121 31141574733983948121091)
                      ·
                        rfl

theorem cell23_60648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_60648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60648 prefixEnd_60648 := by exact prefixLift 60648
  have htrace : WordTrace (prefixWord ++ tailWord_60648) baseStart_60648 baseEnd_60648 := by
    simpa [prefixWord, tailWord_60648, baseEnd_60648] using wordTrace_append hprefix tailTrace_60648
  have hstable : (prefixWord ++ tailWord_60648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60648).length < 2 ^ (prefixWord ++ tailWord_60648).sum := by decide
  have hdescent : baseEnd_60648 < baseStart_60648 := by decide
  rcases family_descends (prefixWord ++ tailWord_60648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60655 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 3]
def baseStart_60655 : Nat := 118140960795 + 60655 * 2 ^ 59
def prefixEnd_60655 : Nat := 4983230072969 + 3 ^ 40 * 60655 * 2
def baseEnd_60655 : Nat := 31145169098565420733559

theorem tailTrace_60655 : CollatzResearch.WordTrace tailWord_60655 prefixEnd_60655 31145169098565420733559 := by
  unfold tailWord_60655
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212269595264768894383419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1474846396843179262922279 2212269595264768894383419)
  ·
    refine ⟨3318404392897153341575129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212269595264768894383419 3318404392897153341575129)
    ·
      refine ⟨2488803294672865006181347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3318404392897153341575129 2488803294672865006181347)
      ·
        refine ⟨3733204942009297509272021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488803294672865006181347 3733204942009297509272021)
        ·
          refine ⟨87496990828342910373563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3733204942009297509272021 87496990828342910373563)
          ·
            refine ⟨131245486242514365560345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87496990828342910373563 131245486242514365560345)
            ·
              refine ⟨98434114681885774170259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131245486242514365560345 98434114681885774170259)
              ·
                refine ⟨147651172022828661255389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98434114681885774170259 147651172022828661255389)
                ·
                  refine ⟨55369189508560747970771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147651172022828661255389 55369189508560747970771)
                  ·
                    refine ⟨83053784262841121956157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55369189508560747970771 83053784262841121956157)
                    ·
                      refine ⟨31145169098565420733559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 83053784262841121956157 31145169098565420733559)
                      ·
                        rfl

theorem cell23_60655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_60655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60655 prefixEnd_60655 := by exact prefixLift 60655
  have htrace : WordTrace (prefixWord ++ tailWord_60655) baseStart_60655 baseEnd_60655 := by
    simpa [prefixWord, tailWord_60655, baseEnd_60655] using wordTrace_append hprefix tailTrace_60655
  have hstable : (prefixWord ++ tailWord_60655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60655).length < 2 ^ (prefixWord ++ tailWord_60655).sum := by decide
  have hdescent : baseEnd_60655 < baseStart_60655 := by decide
  rcases family_descends (prefixWord ++ tailWord_60655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60671 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 6]
def baseStart_60671 : Nat := 118140960795 + 60671 * 2 ^ 59
def prefixEnd_60671 : Nat := 4983230072969 + 3 ^ 40 * 60671 * 2
def baseEnd_60671 : Nat := 10384461596345786044495

theorem tailTrace_60671 : CollatzResearch.WordTrace tailWord_60671 prefixEnd_60671 10384461596345786044495 := by
  unfold tailWord_60671
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212853163206803626965867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1475235442137869084643911 2212853163206803626965867)
  ·
    refine ⟨3319279744810205440448801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212853163206803626965867 3319279744810205440448801)
    ·
      refine ⟨2489459808607654080336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3319279744810205440448801 2489459808607654080336601)
      ·
        refine ⟨1867094856455740560252451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2489459808607654080336601 1867094856455740560252451)
        ·
          refine ⟨2800642284683610840378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1867094856455740560252451 2800642284683610840378677)
          ·
            refine ⟨262560214189088516285501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2800642284683610840378677 262560214189088516285501)
            ·
              refine ⟨98460080320908193607063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262560214189088516285501 98460080320908193607063)
              ·
                refine ⟨147690120481362290410595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98460080320908193607063 147690120481362290410595)
                ·
                  refine ⟨221535180722043435615893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147690120481362290410595 221535180722043435615893)
                  ·
                    refine ⟨10384461596345786044495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221535180722043435615893 10384461596345786044495)
                    ·
                      rfl

theorem cell23_60671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_60671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60671 prefixEnd_60671 := by exact prefixLift 60671
  have htrace : WordTrace (prefixWord ++ tailWord_60671) baseStart_60671 baseEnd_60671 := by
    simpa [prefixWord, tailWord_60671, baseEnd_60671] using wordTrace_append hprefix tailTrace_60671
  have hstable : (prefixWord ++ tailWord_60671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60671).length < 2 ^ (prefixWord ++ tailWord_60671).sum := by decide
  have hdescent : baseEnd_60671 < baseStart_60671 := by decide
  rcases family_descends (prefixWord ++ tailWord_60671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60698 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_60698 : Nat := 118140960795 + 60698 * 2 ^ 59
def prefixEnd_60698 : Nat := 4983230072969 + 3 ^ 40 * 60698 * 2
def baseEnd_60698 : Nat := 31167248766708752495861

theorem tailTrace_60698 : CollatzResearch.WordTrace tailWord_60698 prefixEnd_60698 31167248766708752495861 := by
  unfold tailWord_60698
  simp only [CollatzResearch.WordTrace]
  refine ⟨553459483527246809549687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1475891956072658158799165 553459483527246809549687)
  ·
    refine ⟨830189225290870214324531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553459483527246809549687 830189225290870214324531)
    ·
      refine ⟨1245283837936305321486797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830189225290870214324531 1245283837936305321486797)
      ·
        refine ⟨466981439226114495557549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1245283837936305321486797 466981439226114495557549)
        ·
          refine ⟨175118039709792935834081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466981439226114495557549 175118039709792935834081)
          ·
            refine ⟨131338529782344701875561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175118039709792935834081 131338529782344701875561)
            ·
              refine ⟨98503897336758526406671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131338529782344701875561 98503897336758526406671)
              ·
                refine ⟨147755846005137789610007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98503897336758526406671 147755846005137789610007)
                ·
                  refine ⟨221633769007706684415011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147755846005137789610007 221633769007706684415011)
                  ·
                    refine ⟨332450653511560026622517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221633769007706684415011 332450653511560026622517)
                    ·
                      refine ⟨31167248766708752495861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 332450653511560026622517 31167248766708752495861)
                      ·
                        rfl

theorem cell23_60698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_60698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60698 prefixEnd_60698 := by exact prefixLift 60698
  have htrace : WordTrace (prefixWord ++ tailWord_60698) baseStart_60698 baseEnd_60698 := by
    simpa [prefixWord, tailWord_60698, baseEnd_60698] using wordTrace_append hprefix tailTrace_60698
  have hstable : (prefixWord ++ tailWord_60698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60698).length < 2 ^ (prefixWord ++ tailWord_60698).sum := by decide
  have hdescent : baseEnd_60698 < baseStart_60698 := by decide
  rcases family_descends (prefixWord ++ tailWord_60698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60701 : List Nat := [1, 4, 2, 3, 1, 1, 11]
def baseStart_60701 : Nat := 118140960795 + 60701 * 2 ^ 59
def prefixEnd_60701 : Nat := 4983230072969 + 3 ^ 40 * 60701 * 2
def baseEnd_60701 : Nat := 384799866773731367387

theorem tailTrace_60701 : CollatzResearch.WordTrace tailWord_60701 prefixEnd_60701 384799866773731367387 := by
  unfold tailWord_60701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213947353098118750557957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1475964902065412500371971 2213947353098118750557957)
  ·
    refine ⟨415115128705897265729617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2213947353098118750557957 415115128705897265729617)
    ·
      refine ⟨311336346529422949297213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415115128705897265729617 311336346529422949297213)
      ·
        refine ⟨116751129948533605986455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311336346529422949297213 116751129948533605986455)
        ·
          refine ⟨175126694922800408979683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116751129948533605986455 175126694922800408979683)
          ·
            refine ⟨262690042384200613469525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175126694922800408979683 262690042384200613469525)
            ·
              refine ⟨384799866773731367387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 262690042384200613469525 384799866773731367387)
              ·
                rfl

theorem cell23_60701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 11].length) (baseStart_60701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60701 prefixEnd_60701 := by exact prefixLift 60701
  have htrace : WordTrace (prefixWord ++ tailWord_60701) baseStart_60701 baseEnd_60701 := by
    simpa [prefixWord, tailWord_60701, baseEnd_60701] using wordTrace_append hprefix tailTrace_60701
  have hstable : (prefixWord ++ tailWord_60701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60701).length < 2 ^ (prefixWord ++ tailWord_60701).sum := by decide
  have hdescent : baseEnd_60701 < baseStart_60701 := by decide
  rcases family_descends (prefixWord ++ tailWord_60701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60712 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_60712 : Nat := 118140960795 + 60712 * 2 ^ 59
def prefixEnd_60712 : Nat := 4983230072969 + 3 ^ 40 * 60712 * 2
def baseEnd_60712 : Nat := 31174437495871697720797

theorem tailTrace_60712 : CollatzResearch.WordTrace tailWord_60712 prefixEnd_60712 31174437495871697720797 := by
  unfold tailWord_60712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107174278029133814604195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1476232370705511752805593 1107174278029133814604195)
  ·
    refine ⟨1660761417043700721906293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1107174278029133814604195 1660761417043700721906293)
    ·
      refine ⟨155696382847846942678715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1660761417043700721906293 155696382847846942678715)
      ·
        refine ⟨233544574271770414018073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155696382847846942678715 233544574271770414018073)
        ·
          refine ⟨175158430703827810513555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233544574271770414018073 175158430703827810513555)
          ·
            refine ⟨262737646055741715770333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175158430703827810513555 262737646055741715770333)
            ·
              refine ⟨98526617270903143413875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262737646055741715770333 98526617270903143413875)
              ·
                refine ⟨147789925906354715120813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98526617270903143413875 147789925906354715120813)
                ·
                  refine ⟨55421222214883018170305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147789925906354715120813 55421222214883018170305)
                  ·
                    refine ⟨41565916661162263627729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55421222214883018170305 41565916661162263627729)
                    ·
                      refine ⟨31174437495871697720797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41565916661162263627729 31174437495871697720797)
                      ·
                        rfl

theorem cell23_60712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_60712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60712 prefixEnd_60712 := by exact prefixLift 60712
  have htrace : WordTrace (prefixWord ++ tailWord_60712) baseStart_60712 baseEnd_60712 := by
    simpa [prefixWord, tailWord_60712, baseEnd_60712] using wordTrace_append hprefix tailTrace_60712
  have hstable : (prefixWord ++ tailWord_60712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60712).length < 2 ^ (prefixWord ++ tailWord_60712).sum := by decide
  have hdescent : baseEnd_60712 < baseStart_60712 := by decide
  rcases family_descends (prefixWord ++ tailWord_60712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60722 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_60722 : Nat := 118140960795 + 60722 * 2 ^ 59
def prefixEnd_60722 : Nat := 4983230072969 + 3 ^ 40 * 60722 * 2
def baseEnd_60722 : Nat := 10393190767472219531917

theorem tailTrace_60722 : CollatzResearch.WordTrace tailWord_60722 prefixEnd_60722 10393190767472219531917 := by
  unfold tailWord_60722
  simp only [CollatzResearch.WordTrace]
  refine ⟨553678321505509834268105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1476475524014692891381613 553678321505509834268105)
  ·
    refine ⟨415258741129132375701079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 553678321505509834268105 415258741129132375701079)
    ·
      refine ⟨622888111693698563551619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415258741129132375701079 622888111693698563551619)
      ·
        refine ⟨934332167540547845327429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622888111693698563551619 934332167540547845327429)
        ·
          refine ⟨175187281413852720998893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 934332167540547845327429 175187281413852720998893)
          ·
            refine ⟨65695230530194770374585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175187281413852720998893 65695230530194770374585)
            ·
              refine ⟨49271422897646077780939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65695230530194770374585 49271422897646077780939)
              ·
                refine ⟨73907134346469116671409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49271422897646077780939 73907134346469116671409)
                ·
                  refine ⟨55430350759851837503557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73907134346469116671409 55430350759851837503557)
                  ·
                    refine ⟨10393190767472219531917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55430350759851837503557 10393190767472219531917)
                    ·
                      rfl

theorem cell23_60722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_60722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60722 prefixEnd_60722 := by exact prefixLift 60722
  have htrace : WordTrace (prefixWord ++ tailWord_60722) baseStart_60722 baseEnd_60722 := by
    simpa [prefixWord, tailWord_60722, baseEnd_60722] using wordTrace_append hprefix tailTrace_60722
  have hstable : (prefixWord ++ tailWord_60722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60722).length < 2 ^ (prefixWord ++ tailWord_60722).sum := by decide
  have hdescent : baseEnd_60722 < baseStart_60722 := by decide
  rcases family_descends (prefixWord ++ tailWord_60722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60749 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_60749 : Nat := 118140960795 + 60749 * 2 ^ 59
def prefixEnd_60749 : Nat := 4983230072969 + 3 ^ 40 * 60749 * 2
def baseEnd_60749 : Nat := 31193436280088052958127

theorem tailTrace_60749 : CollatzResearch.WordTrace tailWord_60749 prefixEnd_60749 31193436280088052958127 := by
  unfold tailWord_60749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215698056924222948305301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1477132037949481965536867 2215698056924222948305301)
  ·
    refine ⟨103860846418322950701811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2215698056924222948305301 103860846418322950701811)
    ·
      refine ⟨155791269627484426052717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103860846418322950701811 155791269627484426052717)
      ·
        refine ⟨58421726110306659769769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155791269627484426052717 58421726110306659769769)
        ·
          refine ⟨43816294582729994827327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58421726110306659769769 43816294582729994827327)
          ·
            refine ⟨65724441874094992240991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43816294582729994827327 65724441874094992240991)
            ·
              refine ⟨98586662811142488361487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65724441874094992240991 98586662811142488361487)
              ·
                refine ⟨147879994216713732542231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98586662811142488361487 147879994216713732542231)
                ·
                  refine ⟨221819991325070598813347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147879994216713732542231 221819991325070598813347)
                  ·
                    refine ⟨332729986987605898220021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221819991325070598813347 332729986987605898220021)
                    ·
                      refine ⟨31193436280088052958127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 332729986987605898220021 31193436280088052958127)
                      ·
                        rfl

theorem cell23_60749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_60749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60749 prefixEnd_60749 := by exact prefixLift 60749
  have htrace : WordTrace (prefixWord ++ tailWord_60749) baseStart_60749 baseEnd_60749 := by
    simpa [prefixWord, tailWord_60749, baseEnd_60749] using wordTrace_append hprefix tailTrace_60749
  have hstable : (prefixWord ++ tailWord_60749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60749).length < 2 ^ (prefixWord ++ tailWord_60749).sum := by decide
  have hdescent : baseEnd_60749 < baseStart_60749 := by decide
  rcases family_descends (prefixWord ++ tailWord_60749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60791 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 7]
def baseStart_60791 : Nat := 118140960795 + 60791 * 2 ^ 59
def prefixEnd_60791 : Nat := 4983230072969 + 3 ^ 40 * 60791 * 2
def baseEnd_60791 : Nat := 3468333607508543181437

theorem tailTrace_60791 : CollatzResearch.WordTrace tailWord_60791 prefixEnd_60791 3468333607508543181437 := by
  unfold tailWord_60791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217229922772064121334227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1478153281848042747556151 2217229922772064121334227)
  ·
    refine ⟨3325844884158096182001341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217229922772064121334227 3325844884158096182001341)
    ·
      refine ⟨1247191831559286068250503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3325844884158096182001341 1247191831559286068250503)
      ·
        refine ⟨1870787747338929102375755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247191831559286068250503 1870787747338929102375755)
        ·
          refine ⟨2806181621008393653563633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1870787747338929102375755 2806181621008393653563633)
          ·
            refine ⟨2104636215756295240172725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2806181621008393653563633 2104636215756295240172725)
            ·
              refine ⟨197309645227152678766193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2104636215756295240172725 197309645227152678766193)
              ·
                refine ⟨147982233920364509074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197309645227152678766193 147982233920364509074645)
                ·
                  refine ⟨3468333607508543181437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 147982233920364509074645 3468333607508543181437)
                  ·
                    rfl

theorem cell23_60791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 7].length) (baseStart_60791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60791 prefixEnd_60791 := by exact prefixLift 60791
  have htrace : WordTrace (prefixWord ++ tailWord_60791) baseStart_60791 baseEnd_60791 := by
    simpa [prefixWord, tailWord_60791, baseEnd_60791] using wordTrace_append hprefix tailTrace_60791
  have hstable : (prefixWord ++ tailWord_60791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60791).length < 2 ^ (prefixWord ++ tailWord_60791).sum := by decide
  have hdescent : baseEnd_60791 < baseStart_60791 := by decide
  rcases family_descends (prefixWord ++ tailWord_60791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60932 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 6]
def baseStart_60932 : Nat := 118140960795 + 60932 * 2 ^ 59
def prefixEnd_60932 : Nat := 4983230072969 + 3 ^ 40 * 60932 * 2
def baseEnd_60932 : Nat := 3476378137762315218865

theorem tailTrace_60932 : CollatzResearch.WordTrace tailWord_60932 prefixEnd_60932 3476378137762315218865 := by
  unfold tailWord_60932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111186307630622601108525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1481581743507496801478033 1111186307630622601108525)
  ·
    refine ⟨416694865361483475415697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1111186307630622601108525 416694865361483475415697)
    ·
      refine ⟨312521149021112606561773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416694865361483475415697 312521149021112606561773)
      ·
        refine ⟨117195430882917227460665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312521149021112606561773 117195430882917227460665)
        ·
          refine ⟨87896573162187920595499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117195430882917227460665 87896573162187920595499)
          ·
            refine ⟨131844859743281880893249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87896573162187920595499 131844859743281880893249)
            ·
              refine ⟨98883644807461410669937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131844859743281880893249 98883644807461410669937)
              ·
                refine ⟨74162733605596058002453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98883644807461410669937 74162733605596058002453)
                ·
                  refine ⟨3476378137762315218865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74162733605596058002453 3476378137762315218865)
                  ·
                    rfl

theorem cell23_60932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_60932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60932 prefixEnd_60932 := by exact prefixLift 60932
  have htrace : WordTrace (prefixWord ++ tailWord_60932) baseStart_60932 baseEnd_60932 := by
    simpa [prefixWord, tailWord_60932, baseEnd_60932] using wordTrace_append hprefix tailTrace_60932
  have hstable : (prefixWord ++ tailWord_60932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60932).length < 2 ^ (prefixWord ++ tailWord_60932).sum := by decide
  have hdescent : baseEnd_60932 < baseStart_60932 := by decide
  rcases family_descends (prefixWord ++ tailWord_60932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60965 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_60965 : Nat := 118140960795 + 60965 * 2 ^ 59
def prefixEnd_60965 : Nat := 4983230072969 + 3 ^ 40 * 60965 * 2
def baseEnd_60965 : Nat := 31304348101459207857133

theorem tailTrace_60965 : CollatzResearch.WordTrace tailWord_60965 prefixEnd_60965 31304348101459207857133 := by
  unfold tailWord_60965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223576224141691838168349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1482384149427794558778899 2223576224141691838168349)
  ·
    refine ⟨833841084053134439313131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2223576224141691838168349 833841084053134439313131)
    ·
      refine ⟨1250761626079701658969697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833841084053134439313131 1250761626079701658969697)
      ·
        refine ⟨938071219559776244227273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250761626079701658969697 938071219559776244227273)
        ·
          refine ⟨703553414669832183170455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938071219559776244227273 703553414669832183170455)
          ·
            refine ⟨1055330122004748274755683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703553414669832183170455 1055330122004748274755683)
            ·
              refine ⟨1582995183007122412133525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055330122004748274755683 1582995183007122412133525)
              ·
                refine ⟨74202899203458863068759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1582995183007122412133525 74202899203458863068759)
                ·
                  refine ⟨111304348805188294603139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74202899203458863068759 111304348805188294603139)
                  ·
                    refine ⟨166956523207782441904709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111304348805188294603139 166956523207782441904709)
                    ·
                      refine ⟨31304348101459207857133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 166956523207782441904709 31304348101459207857133)
                      ·
                        rfl

theorem cell23_60965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_60965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60965 prefixEnd_60965 := by exact prefixLift 60965
  have htrace : WordTrace (prefixWord ++ tailWord_60965) baseStart_60965 baseEnd_60965 := by
    simpa [prefixWord, tailWord_60965, baseEnd_60965] using wordTrace_append hprefix tailTrace_60965
  have hstable : (prefixWord ++ tailWord_60965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60965).length < 2 ^ (prefixWord ++ tailWord_60965).sum := by decide
  have hdescent : baseEnd_60965 < baseStart_60965 := by decide
  rcases family_descends (prefixWord ++ tailWord_60965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60978 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_60978 : Nat := 118140960795 + 60978 * 2 ^ 59
def prefixEnd_60978 : Nat := 4983230072969 + 3 ^ 40 * 60978 * 2
def baseEnd_60978 : Nat := 31311023349967656994573

theorem tailTrace_60978 : CollatzResearch.WordTrace tailWord_60978 prefixEnd_60978 31311023349967656994573 := by
  unfold tailWord_60978
  simp only [CollatzResearch.WordTrace]
  refine ⟨556012593273648764597897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1482700248729730038927725 556012593273648764597897)
  ·
    refine ⟨417009444955236573448423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 556012593273648764597897 417009444955236573448423)
    ·
      refine ⟨625514167432854860172635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417009444955236573448423 625514167432854860172635)
      ·
        refine ⟨938271251149282290258953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625514167432854860172635 938271251149282290258953)
        ·
          refine ⟨703703438361961717694215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938271251149282290258953 703703438361961717694215)
          ·
            refine ⟨1055555157542942576541323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703703438361961717694215 1055555157542942576541323)
            ·
              refine ⟨1583332736314413864811985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055555157542942576541323 1583332736314413864811985)
              ·
                refine ⟨1187499552235810398608989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583332736314413864811985 1187499552235810398608989)
                ·
                  refine ⟨445312332088428899478371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187499552235810398608989 445312332088428899478371)
                  ·
                    refine ⟨667968498132643349217557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 445312332088428899478371 667968498132643349217557)
                    ·
                      refine ⟨31311023349967656994573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 667968498132643349217557 31311023349967656994573)
                      ·
                        rfl

theorem cell23_60978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_60978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_60978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_60978 prefixEnd_60978 := by exact prefixLift 60978
  have htrace : WordTrace (prefixWord ++ tailWord_60978) baseStart_60978 baseEnd_60978 := by
    simpa [prefixWord, tailWord_60978, baseEnd_60978] using wordTrace_append hprefix tailTrace_60978
  have hstable : (prefixWord ++ tailWord_60978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60978).length < 2 ^ (prefixWord ++ tailWord_60978).sum := by decide
  have hdescent : baseEnd_60978 < baseStart_60978 := by decide
  rcases family_descends (prefixWord ++ tailWord_60978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61018 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_61018 : Nat := 118140960795 + 61018 * 2 ^ 59
def prefixEnd_61018 : Nat := 4983230072969 + 3 ^ 40 * 61018 * 2
def baseEnd_61018 : Nat := 10443854192049166831463

theorem tailTrace_61018 : CollatzResearch.WordTrace tailWord_61018 prefixEnd_61018 10443854192049166831463 := by
  unfold tailWord_61018
  simp only [CollatzResearch.WordTrace]
  refine ⟨556377323237420472461927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1483672861966454593231805 556377323237420472461927)
  ·
    refine ⟨834565984856130708692891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556377323237420472461927 834565984856130708692891)
    ·
      refine ⟨1251848977284196063039337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834565984856130708692891 1251848977284196063039337)
      ·
        refine ⟨938886732963147047279503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251848977284196063039337 938886732963147047279503)
        ·
          refine ⟨1408330099444720570919255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938886732963147047279503 1408330099444720570919255)
          ·
            refine ⟨2112495149167080856378883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408330099444720570919255 2112495149167080856378883)
            ·
              refine ⟨3168742723750621284568325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112495149167080856378883 3168742723750621284568325)
              ·
                refine ⟨594139260703241490856561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3168742723750621284568325 594139260703241490856561)
                ·
                  refine ⟨445604445527431118142421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594139260703241490856561 445604445527431118142421)
                  ·
                    refine ⟨10443854192049166831463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 445604445527431118142421 10443854192049166831463)
                    ·
                      rfl

theorem cell23_61018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_61018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61018 prefixEnd_61018 := by exact prefixLift 61018
  have htrace : WordTrace (prefixWord ++ tailWord_61018) baseStart_61018 baseEnd_61018 := by
    simpa [prefixWord, tailWord_61018, baseEnd_61018] using wordTrace_append hprefix tailTrace_61018
  have hstable : (prefixWord ++ tailWord_61018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61018).length < 2 ^ (prefixWord ++ tailWord_61018).sum := by decide
  have hdescent : baseEnd_61018 < baseStart_61018 := by decide
  rcases family_descends (prefixWord ++ tailWord_61018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61066 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_61066 : Nat := 118140960795 + 61066 * 2 ^ 59
def prefixEnd_61066 : Nat := 4983230072969 + 3 ^ 40 * 61066 * 2
def baseEnd_61066 : Nat := 31356209647563312694169

theorem tailTrace_61066 : CollatzResearch.WordTrace tailWord_61066 prefixEnd_61066 31356209647563312694169 := by
  unfold tailWord_61066
  simp only [CollatzResearch.WordTrace]
  refine ⟨556814999193946521898763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1484839997850524058396701 556814999193946521898763)
  ·
    refine ⟨835222498790919782848145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556814999193946521898763 835222498790919782848145)
    ·
      refine ⟨626416874093189837136109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835222498790919782848145 626416874093189837136109)
      ·
        refine ⟨234906327784946188926041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626416874093189837136109 234906327784946188926041)
        ·
          refine ⟨176179745838709641694531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234906327784946188926041 176179745838709641694531)
          ·
            refine ⟨264269618758064462541797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176179745838709641694531 264269618758064462541797)
            ·
              refine ⟨49550553517137086726587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264269618758064462541797 49550553517137086726587)
              ·
                refine ⟨74325830275705630089881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49550553517137086726587 74325830275705630089881)
                ·
                  refine ⟨55744372706779222567411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74325830275705630089881 55744372706779222567411)
                  ·
                    refine ⟨83616559060168833851117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55744372706779222567411 83616559060168833851117)
                    ·
                      refine ⟨31356209647563312694169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 83616559060168833851117 31356209647563312694169)
                      ·
                        rfl

theorem cell23_61066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_61066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61066 prefixEnd_61066 := by exact prefixLift 61066
  have htrace : WordTrace (prefixWord ++ tailWord_61066) baseStart_61066 baseEnd_61066 := by
    simpa [prefixWord, tailWord_61066, baseEnd_61066] using wordTrace_append hprefix tailTrace_61066
  have hstable : (prefixWord ++ tailWord_61066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61066).length < 2 ^ (prefixWord ++ tailWord_61066).sum := by decide
  have hdescent : baseEnd_61066 < baseStart_61066 := by decide
  rcases family_descends (prefixWord ++ tailWord_61066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61076 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_61076 : Nat := 118140960795 + 61076 * 2 ^ 59
def prefixEnd_61076 : Nat := 4983230072969 + 3 ^ 40 * 61076 * 2
def baseEnd_61076 : Nat := 31361344454108273569123

theorem tailTrace_61076 : CollatzResearch.WordTrace tailWord_61076 prefixEnd_61076 31361344454108273569123 := by
  unfold tailWord_61076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113812363369778897729541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1485083151159705196972721 1113812363369778897729541)
  ·
    refine ⟨208839818131833543324289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1113812363369778897729541 208839818131833543324289)
    ·
      refine ⟨156629863598875157493217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208839818131833543324289 156629863598875157493217)
      ·
        refine ⟨117472397699156368119913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156629863598875157493217 117472397699156368119913)
        ·
          refine ⟨88104298274367276089935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117472397699156368119913 88104298274367276089935)
          ·
            refine ⟨132156447411550914134903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88104298274367276089935 132156447411550914134903)
            ·
              refine ⟨198234671117326371202355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132156447411550914134903 198234671117326371202355)
              ·
                refine ⟨297352006675989556803533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198234671117326371202355 297352006675989556803533)
                ·
                  refine ⟨111507002503496083801325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297352006675989556803533 111507002503496083801325)
                  ·
                    refine ⟨41815125938811031425497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111507002503496083801325 41815125938811031425497)
                    ·
                      refine ⟨31361344454108273569123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41815125938811031425497 31361344454108273569123)
                      ·
                        rfl

theorem cell23_61076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_61076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61076 prefixEnd_61076 := by exact prefixLift 61076
  have htrace : WordTrace (prefixWord ++ tailWord_61076) baseStart_61076 baseEnd_61076 := by
    simpa [prefixWord, tailWord_61076, baseEnd_61076] using wordTrace_append hprefix tailTrace_61076
  have hstable : (prefixWord ++ tailWord_61076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61076).length < 2 ^ (prefixWord ++ tailWord_61076).sum := by decide
  have hdescent : baseEnd_61076 < baseStart_61076 := by decide
  rcases family_descends (prefixWord ++ tailWord_61076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61085 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_61085 : Nat := 118140960795 + 61085 * 2 ^ 59
def prefixEnd_61085 : Nat := 4983230072969 + 3 ^ 40 * 61085 * 2
def baseEnd_61085 : Nat := 31365965779998738356581

theorem tailTrace_61085 : CollatzResearch.WordTrace tailWord_61085 prefixEnd_61085 31365965779998738356581 := by
  unfold tailWord_61085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227952983706952332536709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1485301989137968221691139 2227952983706952332536709)
  ·
    refine ⟨417741184445053562350633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2227952983706952332536709 417741184445053562350633)
    ·
      refine ⟨313305888333790171762975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417741184445053562350633 313305888333790171762975)
      ·
        refine ⟨469958832500685257644463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313305888333790171762975 469958832500685257644463)
        ·
          refine ⟨704938248751027886466695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469958832500685257644463 704938248751027886466695)
          ·
            refine ⟨1057407373126541829700043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704938248751027886466695 1057407373126541829700043)
            ·
              refine ⟨1586111059689812744550065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057407373126541829700043 1586111059689812744550065)
              ·
                refine ⟨1189583294767359558412549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586111059689812744550065 1189583294767359558412549)
                ·
                  refine ⟨223046867768879917202353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1189583294767359558412549 223046867768879917202353)
                  ·
                    refine ⟨167285150826659937901765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223046867768879917202353 167285150826659937901765)
                    ·
                      refine ⟨31365965779998738356581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 167285150826659937901765 31365965779998738356581)
                      ·
                        rfl

theorem cell23_61085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_61085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61085 prefixEnd_61085 := by exact prefixLift 61085
  have htrace : WordTrace (prefixWord ++ tailWord_61085) baseStart_61085 baseEnd_61085 := by
    simpa [prefixWord, tailWord_61085, baseEnd_61085] using wordTrace_append hprefix tailTrace_61085
  have hstable : (prefixWord ++ tailWord_61085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61085).length < 2 ^ (prefixWord ++ tailWord_61085).sum := by decide
  have hdescent : baseEnd_61085 < baseStart_61085 := by decide
  rcases family_descends (prefixWord ++ tailWord_61085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61089 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_61089 : Nat := 118140960795 + 61089 * 2 ^ 59
def prefixEnd_61089 : Nat := 4983230072969 + 3 ^ 40 * 61089 * 2
def baseEnd_61089 : Nat := 31368019702616722706563

theorem tailTrace_61089 : CollatzResearch.WordTrace tailWord_61089 prefixEnd_61089 31368019702616722706563 := by
  unfold tailWord_61089
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228098875692461015682321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1485399250461640677121547 2228098875692461015682321)
  ·
    refine ⟨1671074156769345761761741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2228098875692461015682321 1671074156769345761761741)
    ·
      refine ⟨626652808788504660660653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1671074156769345761761741 626652808788504660660653)
      ·
        refine ⟨234994803295689247747745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626652808788504660660653 234994803295689247747745)
        ·
          refine ⟨176246102471766935810809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234994803295689247747745 176246102471766935810809)
          ·
            refine ⟨132184576853825201858107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176246102471766935810809 132184576853825201858107)
            ·
              refine ⟨198276865280737802787161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132184576853825201858107 198276865280737802787161)
              ·
                refine ⟨148707648960553352090371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198276865280737802787161 148707648960553352090371)
                ·
                  refine ⟨223061473440830028135557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148707648960553352090371 223061473440830028135557)
                  ·
                    refine ⟨41824026270155630275417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223061473440830028135557 41824026270155630275417)
                    ·
                      refine ⟨31368019702616722706563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41824026270155630275417 31368019702616722706563)
                      ·
                        rfl

theorem cell23_61089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_61089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61089 prefixEnd_61089 := by exact prefixLift 61089
  have htrace : WordTrace (prefixWord ++ tailWord_61089) baseStart_61089 baseEnd_61089 := by
    simpa [prefixWord, tailWord_61089, baseEnd_61089] using wordTrace_append hprefix tailTrace_61089
  have hstable : (prefixWord ++ tailWord_61089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61089).length < 2 ^ (prefixWord ++ tailWord_61089).sum := by decide
  have hdescent : baseEnd_61089 < baseStart_61089 := by decide
  rcases family_descends (prefixWord ++ tailWord_61089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61162 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_61162 : Nat := 118140960795 + 61162 * 2 ^ 59
def prefixEnd_61162 : Nat := 4983230072969 + 3 ^ 40 * 61162 * 2
def baseEnd_61162 : Nat := 31405503790394937093727

theorem tailTrace_61162 : CollatzResearch.WordTrace tailWord_61162 prefixEnd_61162 31405503790394937093727 := by
  unfold tailWord_61162
  simp only [CollatzResearch.WordTrace]
  refine ⟨557690351106998620772435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1487174269618662988726493 557690351106998620772435)
  ·
    refine ⟨836535526660497931158653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557690351106998620772435 836535526660497931158653)
    ·
      refine ⟨313700822497686724184495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 836535526660497931158653 313700822497686724184495)
      ·
        refine ⟨470551233746530086276743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313700822497686724184495 470551233746530086276743)
        ·
          refine ⟨705826850619795129415115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470551233746530086276743 705826850619795129415115)
          ·
            refine ⟨1058740275929692694122673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705826850619795129415115 1058740275929692694122673)
            ·
              refine ⟨794055206947269520592005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058740275929692694122673 794055206947269520592005)
              ·
                refine ⟨148885351302613035111001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794055206947269520592005 148885351302613035111001)
                ·
                  refine ⟨111664013476959776333251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148885351302613035111001 111664013476959776333251)
                  ·
                    refine ⟨167496020215439664499877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111664013476959776333251 167496020215439664499877)
                    ·
                      refine ⟨31405503790394937093727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 167496020215439664499877 31405503790394937093727)
                      ·
                        rfl

theorem cell23_61162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_61162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61162 prefixEnd_61162 := by exact prefixLift 61162
  have htrace : WordTrace (prefixWord ++ tailWord_61162) baseStart_61162 baseEnd_61162 := by
    simpa [prefixWord, tailWord_61162, baseEnd_61162] using wordTrace_append hprefix tailTrace_61162
  have hstable : (prefixWord ++ tailWord_61162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61162).length < 2 ^ (prefixWord ++ tailWord_61162).sum := by decide
  have hdescent : baseEnd_61162 < baseStart_61162 := by decide
  rcases family_descends (prefixWord ++ tailWord_61162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61197 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 5]
def baseStart_61197 : Nat := 118140960795 + 61197 * 2 ^ 59
def prefixEnd_61197 : Nat := 4983230072969 + 3 ^ 40 * 61197 * 2
def baseEnd_61197 : Nat := 3491497290366922239563

theorem tailTrace_61197 : CollatzResearch.WordTrace tailWord_61197 prefixEnd_61197 3491497290366922239563 := by
  unfold tailWord_61197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232037959301195460613845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1488025306200796973742563 2232037959301195460613845)
  ·
    refine ⟨52313389671121768608137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2232037959301195460613845 52313389671121768608137)
    ·
      refine ⟨39235042253341326456103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52313389671121768608137 39235042253341326456103)
      ·
        refine ⟨58852563380011989684155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39235042253341326456103 58852563380011989684155)
        ·
          refine ⟨88278845070017984526233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58852563380011989684155 88278845070017984526233)
          ·
            refine ⟨66209133802513488394675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88278845070017984526233 66209133802513488394675)
            ·
              refine ⟨99313700703770232592013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66209133802513488394675 99313700703770232592013)
              ·
                refine ⟨37242637763913837222005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99313700703770232592013 37242637763913837222005)
                ·
                  refine ⟨3491497290366922239563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37242637763913837222005 3491497290366922239563)
                  ·
                    rfl

theorem cell23_61197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_61197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61197 prefixEnd_61197 := by exact prefixLift 61197
  have htrace : WordTrace (prefixWord ++ tailWord_61197) baseStart_61197 baseEnd_61197 := by
    simpa [prefixWord, tailWord_61197, baseEnd_61197] using wordTrace_append hprefix tailTrace_61197
  have hstable : (prefixWord ++ tailWord_61197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61197).length < 2 ^ (prefixWord ++ tailWord_61197).sum := by decide
  have hdescent : baseEnd_61197 < baseStart_61197 := by decide
  rcases family_descends (prefixWord ++ tailWord_61197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61236 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 6]
def baseStart_61236 : Nat := 118140960795 + 61236 * 2 ^ 59
def prefixEnd_61236 : Nat := 4983230072969 + 3 ^ 40 * 61236 * 2
def baseEnd_61236 : Nat := 3493722373203071952043

theorem tailTrace_61236 : CollatzResearch.WordTrace tailWord_61236 prefixEnd_61236 3493722373203071952043 := by
  unfold tailWord_61236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116730203079952560641781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1488973604106603414189041 1116730203079952560641781)
  ·
    refine ⟨104693456538745552560167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1116730203079952560641781 104693456538745552560167)
    ·
      refine ⟨157040184808118328840251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104693456538745552560167 157040184808118328840251)
      ·
        refine ⟨235560277212177493260377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157040184808118328840251 235560277212177493260377)
        ·
          refine ⟨176670207909133119945283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235560277212177493260377 176670207909133119945283)
          ·
            refine ⟨265005311863699679917925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176670207909133119945283 265005311863699679917925)
            ·
              refine ⟨49688495974443689984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265005311863699679917925 49688495974443689984611)
              ·
                refine ⟨74532743961665534976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49688495974443689984611 74532743961665534976917)
                ·
                  refine ⟨3493722373203071952043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74532743961665534976917 3493722373203071952043)
                  ·
                    rfl

theorem cell23_61236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_61236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61236 prefixEnd_61236 := by exact prefixLift 61236
  have htrace : WordTrace (prefixWord ++ tailWord_61236) baseStart_61236 baseEnd_61236 := by
    simpa [prefixWord, tailWord_61236, baseEnd_61236] using wordTrace_append hprefix tailTrace_61236
  have hstable : (prefixWord ++ tailWord_61236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61236).length < 2 ^ (prefixWord ++ tailWord_61236).sum := by decide
  have hdescent : baseEnd_61236 < baseStart_61236 := by decide
  rcases family_descends (prefixWord ++ tailWord_61236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61256 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_61256 : Nat := 118140960795 + 61256 * 2 ^ 59
def prefixEnd_61256 : Nat := 4983230072969 + 3 ^ 40 * 61256 * 2
def baseEnd_61256 : Nat := 31453770971917569318295

theorem tailTrace_61256 : CollatzResearch.WordTrace tailWord_61256 prefixEnd_61256 31453770971917569318295 := by
  unfold tailWord_61256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117094933043724268505811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1489459910724965691341081 1117094933043724268505811)
  ·
    refine ⟨1675642399565586402758717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117094933043724268505811 1675642399565586402758717)
    ·
      refine ⟨628365899837094901034519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1675642399565586402758717 628365899837094901034519)
      ·
        refine ⟨942548849755642351551779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628365899837094901034519 942548849755642351551779)
        ·
          refine ⟨1413823274633463527327669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942548849755642351551779 1413823274633463527327669)
          ·
            refine ⟨132545931996887205686969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1413823274633463527327669 132545931996887205686969)
            ·
              refine ⟨99409448997665404265227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132545931996887205686969 99409448997665404265227)
              ·
                refine ⟨149114173496498106397841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99409448997665404265227 149114173496498106397841)
                ·
                  refine ⟨111835630122373579798381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149114173496498106397841 111835630122373579798381)
                  ·
                    refine ⟨41938361295890092424393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111835630122373579798381 41938361295890092424393)
                    ·
                      refine ⟨31453770971917569318295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 41938361295890092424393 31453770971917569318295)
                      ·
                        rfl

theorem cell23_61256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_61256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61256 prefixEnd_61256 := by exact prefixLift 61256
  have htrace : WordTrace (prefixWord ++ tailWord_61256) baseStart_61256 baseEnd_61256 := by
    simpa [prefixWord, tailWord_61256, baseEnd_61256] using wordTrace_append hprefix tailTrace_61256
  have hstable : (prefixWord ++ tailWord_61256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61256).length < 2 ^ (prefixWord ++ tailWord_61256).sum := by decide
  have hdescent : baseEnd_61256 < baseStart_61256 := by decide
  rcases family_descends (prefixWord ++ tailWord_61256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61266 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_61266 : Nat := 118140960795 + 61266 * 2 ^ 59
def prefixEnd_61266 : Nat := 4983230072969 + 3 ^ 40 * 61266 * 2
def baseEnd_61266 : Nat := 10486301926154176731083

theorem tailTrace_61266 : CollatzResearch.WordTrace tailWord_61266 prefixEnd_61266 10486301926154176731083 := by
  unfold tailWord_61266
  simp only [CollatzResearch.WordTrace]
  refine ⟨558638649012805061218913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1489703064034146829917101 558638649012805061218913)
  ·
    refine ⟨418978986759603795914185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 558638649012805061218913 418978986759603795914185)
    ·
      refine ⟨314234240069702846935639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418978986759603795914185 314234240069702846935639)
      ·
        refine ⟨471351360104554270403459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314234240069702846935639 471351360104554270403459)
        ·
          refine ⟨707027040156831405605189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471351360104554270403459 707027040156831405605189)
          ·
            refine ⟨132567570029405888550973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 707027040156831405605189 132567570029405888550973)
            ·
              refine ⟨49712838761027208206615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132567570029405888550973 49712838761027208206615)
              ·
                refine ⟨74569258141540812309923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49712838761027208206615 74569258141540812309923)
                ·
                  refine ⟨111853887212311218464885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74569258141540812309923 111853887212311218464885)
                  ·
                    refine ⟨10486301926154176731083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111853887212311218464885 10486301926154176731083)
                    ·
                      rfl

theorem cell23_61266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_61266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61266 prefixEnd_61266 := by exact prefixLift 61266
  have htrace : WordTrace (prefixWord ++ tailWord_61266) baseStart_61266 baseEnd_61266 := by
    simpa [prefixWord, tailWord_61266, baseEnd_61266] using wordTrace_append hprefix tailTrace_61266
  have hstable : (prefixWord ++ tailWord_61266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61266).length < 2 ^ (prefixWord ++ tailWord_61266).sum := by decide
  have hdescent : baseEnd_61266 < baseStart_61266 := by decide
  rcases family_descends (prefixWord ++ tailWord_61266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61279 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 2, 4]
def baseStart_61279 : Nat := 118140960795 + 61279 * 2 ^ 59
def prefixEnd_61279 : Nat := 4983230072969 + 3 ^ 40 * 61279 * 2
def baseEnd_61279 : Nat := 10488527008990326443563

theorem tailTrace_61279 : CollatzResearch.WordTrace tailWord_61279 prefixEnd_61279 10488527008990326443563 := by
  unfold tailWord_61279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235028745004123465098891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1490019163336082310065927 2235028745004123465098891)
  ·
    refine ⟨3352543117506185197648337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2235028745004123465098891 3352543117506185197648337)
    ·
      refine ⟨2514407338129638898236253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3352543117506185197648337 2514407338129638898236253)
      ·
        refine ⟨942902751798614586838595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2514407338129638898236253 942902751798614586838595)
        ·
          refine ⟨1414354127697921880257893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942902751798614586838595 1414354127697921880257893)
          ·
            refine ⟨265191398943360352548355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1414354127697921880257893 265191398943360352548355)
            ·
              refine ⟨397787098415040528822533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265191398943360352548355 397787098415040528822533)
              ·
                refine ⟨74585080952820099154225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397787098415040528822533 74585080952820099154225)
                ·
                  refine ⟨55938810714615074365669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74585080952820099154225 55938810714615074365669)
                  ·
                    refine ⟨10488527008990326443563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55938810714615074365669 10488527008990326443563)
                    ·
                      rfl

theorem cell23_61279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_61279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61279 prefixEnd_61279 := by exact prefixLift 61279
  have htrace : WordTrace (prefixWord ++ tailWord_61279) baseStart_61279 baseEnd_61279 := by
    simpa [prefixWord, tailWord_61279, baseEnd_61279] using wordTrace_append hprefix tailTrace_61279
  have hstable : (prefixWord ++ tailWord_61279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61279).length < 2 ^ (prefixWord ++ tailWord_61279).sum := by decide
  have hdescent : baseEnd_61279 < baseStart_61279 := by decide
  rcases family_descends (prefixWord ++ tailWord_61279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61280 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 1, 1, 3]
def baseStart_61280 : Nat := 118140960795 + 61280 * 2 ^ 59
def prefixEnd_61280 : Nat := 4983230072969 + 3 ^ 40 * 61280 * 2
def baseEnd_61280 : Nat := 31466094507625475418185

theorem tailTrace_61280 : CollatzResearch.WordTrace tailWord_61280 prefixEnd_61280 31466094507625475418185 := by
  unfold tailWord_61280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117532609000250317942647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1490043478667000423923529 1117532609000250317942647)
  ·
    refine ⟨1676298913500375476913971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117532609000250317942647 1676298913500375476913971)
    ·
      refine ⟨2514448370250563215370957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676298913500375476913971 2514448370250563215370957)
      ·
        refine ⟨942918138843961205764109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2514448370250563215370957 942918138843961205764109)
        ·
          refine ⟨353594302066485452161541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942918138843961205764109 353594302066485452161541)
          ·
            refine ⟨66298931637466022280289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 353594302066485452161541 66298931637466022280289)
            ·
              refine ⟨49724198728099516710217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66298931637466022280289 49724198728099516710217)
              ·
                refine ⟨37293149046074637532663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49724198728099516710217 37293149046074637532663)
                ·
                  refine ⟨55939723569111956298995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37293149046074637532663 55939723569111956298995)
                  ·
                    refine ⟨83909585353667934448493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55939723569111956298995 83909585353667934448493)
                    ·
                      refine ⟨31466094507625475418185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 83909585353667934448493 31466094507625475418185)
                      ·
                        rfl

theorem cell23_61280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_61280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61280 prefixEnd_61280 := by exact prefixLift 61280
  have htrace : WordTrace (prefixWord ++ tailWord_61280) baseStart_61280 baseEnd_61280 := by
    simpa [prefixWord, tailWord_61280, baseEnd_61280] using wordTrace_append hprefix tailTrace_61280
  have hstable : (prefixWord ++ tailWord_61280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61280).length < 2 ^ (prefixWord ++ tailWord_61280).sum := by decide
  have hdescent : baseEnd_61280 < baseStart_61280 := by decide
  rcases family_descends (prefixWord ++ tailWord_61280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61292 : List Nat := [2, 2, 1, 1, 4, 2, 3, 8]
def baseStart_61292 : Nat := 118140960795 + 61292 * 2 ^ 59
def prefixEnd_61292 : Nat := 4983230072969 + 3 ^ 40 * 61292 * 2
def baseEnd_61292 : Nat := 1165639121314052906227

theorem tailTrace_61292 : CollatzResearch.WordTrace tailWord_61292 prefixEnd_61292 1165639121314052906227 := by
  unfold tailWord_61292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117751446978513342661065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1490335262638017790214753 1117751446978513342661065)
  ·
    refine ⟨838313585233885006995799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1117751446978513342661065 838313585233885006995799)
    ·
      refine ⟨1257470377850827510493699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838313585233885006995799 1257470377850827510493699)
      ·
        refine ⟨1886205566776241265740549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257470377850827510493699 1886205566776241265740549)
        ·
          refine ⟨353663543770545237326353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1886205566776241265740549 353663543770545237326353)
          ·
            refine ⟨265247657827908927994765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353663543770545237326353 265247657827908927994765)
            ·
              refine ⟨99467871685465847998037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265247657827908927994765 99467871685465847998037)
              ·
                refine ⟨1165639121314052906227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 99467871685465847998037 1165639121314052906227)
                ·
                  rfl

theorem cell23_61292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 8].length) (baseStart_61292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61292 prefixEnd_61292 := by exact prefixLift 61292
  have htrace : WordTrace (prefixWord ++ tailWord_61292) baseStart_61292 baseEnd_61292 := by
    simpa [prefixWord, tailWord_61292, baseEnd_61292] using wordTrace_append hprefix tailTrace_61292
  have hstable : (prefixWord ++ tailWord_61292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61292).length < 2 ^ (prefixWord ++ tailWord_61292).sum := by decide
  have hdescent : baseEnd_61292 < baseStart_61292 := by decide
  rcases family_descends (prefixWord ++ tailWord_61292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61320 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_61320 : Nat := 118140960795 + 61320 * 2 ^ 59
def prefixEnd_61320 : Nat := 4983230072969 + 3 ^ 40 * 61320 * 2
def baseEnd_61320 : Nat := 31486633733805318918001

theorem tailTrace_61320 : CollatzResearch.WordTrace tailWord_61320 prefixEnd_61320 31486633733805318918001 := by
  unfold tailWord_61320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118262068927793733670707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1491016091903724978227609 1118262068927793733670707)
  ·
    refine ⟨1677393103391690600506061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118262068927793733670707 1677393103391690600506061)
    ·
      refine ⟨629022413771883975189773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1677393103391690600506061 629022413771883975189773)
      ·
        refine ⟨235883405164456490696165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629022413771883975189773 235883405164456490696165)
        ·
          refine ⟨44228138468335592005531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235883405164456490696165 44228138468335592005531)
          ·
            refine ⟨66342207702503388008297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44228138468335592005531 66342207702503388008297)
            ·
              refine ⟨49756655776877541006223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66342207702503388008297 49756655776877541006223)
              ·
                refine ⟨74634983665316311509335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49756655776877541006223 74634983665316311509335)
                ·
                  refine ⟨111952475497974467264003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74634983665316311509335 111952475497974467264003)
                  ·
                    refine ⟨167928713246961700896005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111952475497974467264003 167928713246961700896005)
                    ·
                      refine ⟨31486633733805318918001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 167928713246961700896005 31486633733805318918001)
                      ·
                        rfl

theorem cell23_61320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_61320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61320 prefixEnd_61320 := by exact prefixLift 61320
  have htrace : WordTrace (prefixWord ++ tailWord_61320) baseStart_61320 baseEnd_61320 := by
    simpa [prefixWord, tailWord_61320, baseEnd_61320] using wordTrace_append hprefix tailTrace_61320
  have hstable : (prefixWord ++ tailWord_61320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61320).length < 2 ^ (prefixWord ++ tailWord_61320).sum := by decide
  have hdescent : baseEnd_61320 < baseStart_61320 := by decide
  rcases family_descends (prefixWord ++ tailWord_61320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61362 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_61362 : Nat := 118140960795 + 61362 * 2 ^ 59
def prefixEnd_61362 : Nat := 4983230072969 + 3 ^ 40 * 61362 * 2
def baseEnd_61362 : Nat := 31508199921294154592807

theorem tailTrace_61362 : CollatzResearch.WordTrace tailWord_61362 prefixEnd_61362 31508199921294154592807 := by
  unfold tailWord_61362
  simp only [CollatzResearch.WordTrace]
  refine ⟨559514000925857160092585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1492037335802285760246893 559514000925857160092585)
  ·
    refine ⟨419635500694392870069439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 559514000925857160092585 419635500694392870069439)
    ·
      refine ⟨629453251041589305104159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419635500694392870069439 629453251041589305104159)
      ·
        refine ⟨944179876562383957656239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629453251041589305104159 944179876562383957656239)
        ·
          refine ⟨1416269814843575936484359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944179876562383957656239 1416269814843575936484359)
          ·
            refine ⟨2124404722265363904726539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416269814843575936484359 2124404722265363904726539)
            ·
              refine ⟨3186607083398045857089809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124404722265363904726539 3186607083398045857089809)
              ·
                refine ⟨2389955312548534392817357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186607083398045857089809 2389955312548534392817357)
                ·
                  refine ⟨896233242205700397306509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2389955312548534392817357 896233242205700397306509)
                  ·
                    refine ⟨336087465827137648989941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896233242205700397306509 336087465827137648989941)
                    ·
                      refine ⟨31508199921294154592807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 336087465827137648989941 31508199921294154592807)
                      ·
                        rfl

theorem cell23_61362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_61362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61362 prefixEnd_61362 := by exact prefixLift 61362
  have htrace : WordTrace (prefixWord ++ tailWord_61362) baseStart_61362 baseEnd_61362 := by
    simpa [prefixWord, tailWord_61362, baseEnd_61362] using wordTrace_append hprefix tailTrace_61362
  have hstable : (prefixWord ++ tailWord_61362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61362).length < 2 ^ (prefixWord ++ tailWord_61362).sum := by decide
  have hdescent : baseEnd_61362 < baseStart_61362 := by decide
  rcases family_descends (prefixWord ++ tailWord_61362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61376 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2]
def baseStart_61376 : Nat := 118140960795 + 61376 * 2 ^ 59
def prefixEnd_61376 : Nat := 4983230072969 + 3 ^ 40 * 61376 * 2
def baseEnd_61376 : Nat := 31515388650457099817743

theorem tailTrace_61376 : CollatzResearch.WordTrace tailWord_61376 prefixEnd_61376 31515388650457099817743 := by
  unfold tailWord_61376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119283312826354515689991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1492377750435139354253321 1119283312826354515689991)
  ·
    refine ⟨1678924969239531773534987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119283312826354515689991 1678924969239531773534987)
    ·
      refine ⟨2518387453859297660302481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678924969239531773534987 2518387453859297660302481)
      ·
        refine ⟨1888790590394473245226861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2518387453859297660302481 1888790590394473245226861)
        ·
          refine ⟨708296471397927466960073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1888790590394473245226861 708296471397927466960073)
          ·
            refine ⟨531222353548445600220055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708296471397927466960073 531222353548445600220055)
            ·
              refine ⟨796833530322668400330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531222353548445600220055 796833530322668400330083)
              ·
                refine ⟨1195250295484002600495125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796833530322668400330083 1195250295484002600495125)
                ·
                  refine ⟨56027357600812621898209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1195250295484002600495125 56027357600812621898209)
                  ·
                    refine ⟨42020518200609466423657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56027357600812621898209 42020518200609466423657)
                    ·
                      refine ⟨31515388650457099817743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42020518200609466423657 31515388650457099817743)
                      ·
                        rfl

theorem cell23_61376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_61376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61376 prefixEnd_61376 := by exact prefixLift 61376
  have htrace : WordTrace (prefixWord ++ tailWord_61376) baseStart_61376 baseEnd_61376 := by
    simpa [prefixWord, tailWord_61376, baseEnd_61376] using wordTrace_append hprefix tailTrace_61376
  have hstable : (prefixWord ++ tailWord_61376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61376).length < 2 ^ (prefixWord ++ tailWord_61376).sum := by decide
  have hdescent : baseEnd_61376 < baseStart_61376 := by decide
  rcases family_descends (prefixWord ++ tailWord_61376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61409 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_61409 : Nat := 118140960795 + 61409 * 2 ^ 59
def prefixEnd_61409 : Nat := 4983230072969 + 3 ^ 40 * 61409 * 2
def baseEnd_61409 : Nat := 31532333512055470705091

theorem tailTrace_61409 : CollatzResearch.WordTrace tailWord_61409 prefixEnd_61409 31532333512055470705091 := by
  unfold tailWord_61409
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239770234533155667331281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1493180156355437111554187 2239770234533155667331281)
  ·
    refine ⟨1679827675899866750498461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2239770234533155667331281 1679827675899866750498461)
    ·
      refine ⟨629935378462450031436923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1679827675899866750498461 629935378462450031436923)
      ·
        refine ⟨944903067693675047155385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629935378462450031436923 944903067693675047155385)
        ·
          refine ⟨708677300770256285366539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944903067693675047155385 708677300770256285366539)
          ·
            refine ⟨1063015951155384428049809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708677300770256285366539 1063015951155384428049809)
            ·
              refine ⟨797261963366538321037357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063015951155384428049809 797261963366538321037357)
              ·
                refine ⟨298973236262451870389009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 797261963366538321037357 298973236262451870389009)
                ·
                  refine ⟨224229927196838902791757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298973236262451870389009 224229927196838902791757)
                  ·
                    refine ⟨84086222698814588546909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224229927196838902791757 84086222698814588546909)
                    ·
                      refine ⟨31532333512055470705091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 84086222698814588546909 31532333512055470705091)
                      ·
                        rfl

theorem cell23_61409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_61409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61409 prefixEnd_61409 := by exact prefixLift 61409
  have htrace : WordTrace (prefixWord ++ tailWord_61409) baseStart_61409 baseEnd_61409 := by
    simpa [prefixWord, tailWord_61409, baseEnd_61409] using wordTrace_append hprefix tailTrace_61409
  have hstable : (prefixWord ++ tailWord_61409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61409).length < 2 ^ (prefixWord ++ tailWord_61409).sum := by decide
  have hdescent : baseEnd_61409 < baseStart_61409 := by decide
  rcases family_descends (prefixWord ++ tailWord_61409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61450 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_61450 : Nat := 118140960795 + 61450 * 2 ^ 59
def prefixEnd_61450 : Nat := 4983230072969 + 3 ^ 40 * 61450 * 2
def baseEnd_61450 : Nat := 3505931802098867810267

theorem tailTrace_61450 : CollatzResearch.WordTrace tailWord_61450 prefixEnd_61450 3505931802098867810267 := by
  unfold tailWord_61450
  simp only [CollatzResearch.WordTrace]
  refine ⟨560316406846154917393451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1494177084923079779715869 560316406846154917393451)
  ·
    refine ⟨840474610269232376090177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 560316406846154917393451 840474610269232376090177)
    ·
      refine ⟨630355957701924282067633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 840474610269232376090177 630355957701924282067633)
      ·
        refine ⟨472766968276443211550725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630355957701924282067633 472766968276443211550725)
        ·
          refine ⟨88643806551833102165761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472766968276443211550725 88643806551833102165761)
          ·
            refine ⟨66482854913874826624321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88643806551833102165761 66482854913874826624321)
            ·
              refine ⟨49862141185406119968241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66482854913874826624321 49862141185406119968241)
              ·
                refine ⟨37396605889054589976181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49862141185406119968241 37396605889054589976181)
                ·
                  refine ⟨3505931802098867810267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37396605889054589976181 3505931802098867810267)
                  ·
                    rfl

theorem cell23_61450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_61450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61450 prefixEnd_61450 := by exact prefixLift 61450
  have htrace : WordTrace (prefixWord ++ tailWord_61450) baseStart_61450 baseEnd_61450 := by
    simpa [prefixWord, tailWord_61450, baseEnd_61450] using wordTrace_append hprefix tailTrace_61450
  have hstable : (prefixWord ++ tailWord_61450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61450).length < 2 ^ (prefixWord ++ tailWord_61450).sum := by decide
  have hdescent : baseEnd_61450 < baseStart_61450 := by decide
  rcases family_descends (prefixWord ++ tailWord_61450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61460 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_61460 : Nat := 118140960795 + 61460 * 2 ^ 59
def prefixEnd_61460 : Nat := 4983230072969 + 3 ^ 40 * 61460 * 2
def baseEnd_61460 : Nat := 31558521025434771167357

theorem tailTrace_61460 : CollatzResearch.WordTrace tailWord_61460 prefixEnd_61460 31558521025434771167357 := by
  unfold tailWord_61460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120815178674195688718917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1494420238232260918291889 1120815178674195688718917)
  ·
    refine ⟨210152846001411691634797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1120815178674195688718917 210152846001411691634797)
    ·
      refine ⟨78807317250529384363049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210152846001411691634797 78807317250529384363049)
      ·
        refine ⟨59105487937897038272287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78807317250529384363049 59105487937897038272287)
        ·
          refine ⟨88658231906845557408431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59105487937897038272287 88658231906845557408431)
          ·
            refine ⟨132987347860268336112647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88658231906845557408431 132987347860268336112647)
            ·
              refine ⟨199481021790402504168971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132987347860268336112647 199481021790402504168971)
              ·
                refine ⟨299221532685603756253457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199481021790402504168971 299221532685603756253457)
                ·
                  refine ⟨224416149514202817190093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299221532685603756253457 224416149514202817190093)
                  ·
                    refine ⟨84156056067826056446285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224416149514202817190093 84156056067826056446285)
                    ·
                      refine ⟨31558521025434771167357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 84156056067826056446285 31558521025434771167357)
                      ·
                        rfl

theorem cell23_61460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_61460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61460 prefixEnd_61460 := by exact prefixLift 61460
  have htrace : WordTrace (prefixWord ++ tailWord_61460) baseStart_61460 baseEnd_61460 := by
    simpa [prefixWord, tailWord_61460, baseEnd_61460] using wordTrace_append hprefix tailTrace_61460
  have hstable : (prefixWord ++ tailWord_61460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61460).length < 2 ^ (prefixWord ++ tailWord_61460).sum := by decide
  have hdescent : baseEnd_61460 < baseStart_61460 := by decide
  rcases family_descends (prefixWord ++ tailWord_61460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61466 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_61466 : Nat := 118140960795 + 61466 * 2 ^ 59
def prefixEnd_61466 : Nat := 4983230072969 + 3 ^ 40 * 61466 * 2
def baseEnd_61466 : Nat := 31561601909361747692329

theorem tailTrace_61466 : CollatzResearch.WordTrace tailWord_61466 prefixEnd_61466 31561601909361747692329 := by
  unfold tailWord_61466
  simp only [CollatzResearch.WordTrace]
  refine ⟨560462298831663600539063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1494566130217769601437501 560462298831663600539063)
  ·
    refine ⟨840693448247495400808595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 560462298831663600539063 840693448247495400808595)
    ·
      refine ⟨1261040172371243101212893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840693448247495400808595 1261040172371243101212893)
      ·
        refine ⟨472890064639216162954835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1261040172371243101212893 472890064639216162954835)
        ·
          refine ⟨709335096958824244432253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472890064639216162954835 709335096958824244432253)
          ·
            refine ⟨266000661359559091662095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709335096958824244432253 266000661359559091662095)
            ·
              refine ⟨399000992039338637493143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266000661359559091662095 399000992039338637493143)
              ·
                refine ⟨598501488059007956239715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399000992039338637493143 598501488059007956239715)
                ·
                  refine ⟨897752232088511934359573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598501488059007956239715 897752232088511934359573)
                  ·
                    refine ⟨42082135879148996923105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 897752232088511934359573 42082135879148996923105)
                    ·
                      refine ⟨31561601909361747692329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42082135879148996923105 31561601909361747692329)
                      ·
                        rfl

theorem cell23_61466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_61466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61466 prefixEnd_61466 := by exact prefixLift 61466
  have htrace : WordTrace (prefixWord ++ tailWord_61466) baseStart_61466 baseEnd_61466 := by
    simpa [prefixWord, tailWord_61466, baseEnd_61466] using wordTrace_append hprefix tailTrace_61466
  have hstable : (prefixWord ++ tailWord_61466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61466).length < 2 ^ (prefixWord ++ tailWord_61466).sum := by decide
  have hdescent : baseEnd_61466 < baseStart_61466 := by decide
  rcases family_descends (prefixWord ++ tailWord_61466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61480 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_61480 : Nat := 118140960795 + 61480 * 2 ^ 59
def prefixEnd_61480 : Nat := 4983230072969 + 3 ^ 40 * 61480 * 2
def baseEnd_61480 : Nat := 10522930212841564305755

theorem tailTrace_61480 : CollatzResearch.WordTrace tailWord_61480 prefixEnd_61480 10522930212841564305755 := by
  unfold tailWord_61480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121179908637967396582947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1494906544850623195443929 1121179908637967396582947)
  ·
    refine ⟨1681769862956951094874421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121179908637967396582947 1681769862956951094874421)
    ·
      refine ⟨157665924652214165144477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1681769862956951094874421 157665924652214165144477)
      ·
        refine ⟨59124721744580311929179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157665924652214165144477 59124721744580311929179)
        ·
          refine ⟨88687082616870467893769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59124721744580311929179 88687082616870467893769)
          ·
            refine ⟨66515311962652850920327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88687082616870467893769 66515311962652850920327)
            ·
              refine ⟨99772967943979276380491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66515311962652850920327 99772967943979276380491)
              ·
                refine ⟨149659451915968914570737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99772967943979276380491 149659451915968914570737)
                ·
                  refine ⟨112244588936976685928053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149659451915968914570737 112244588936976685928053)
                  ·
                    refine ⟨10522930212841564305755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112244588936976685928053 10522930212841564305755)
                    ·
                      rfl

theorem cell23_61480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_61480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61480 prefixEnd_61480 := by exact prefixLift 61480
  have htrace : WordTrace (prefixWord ++ tailWord_61480) baseStart_61480 baseEnd_61480 := by
    simpa [prefixWord, tailWord_61480, baseEnd_61480] using wordTrace_append hprefix tailTrace_61480
  have hstable : (prefixWord ++ tailWord_61480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61480).length < 2 ^ (prefixWord ++ tailWord_61480).sum := by decide
  have hdescent : baseEnd_61480 < baseStart_61480 := by decide
  rcases family_descends (prefixWord ++ tailWord_61480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61493 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_61493 : Nat := 118140960795 + 61493 * 2 ^ 59
def prefixEnd_61493 : Nat := 4983230072969 + 3 ^ 40 * 61493 * 2
def baseEnd_61493 : Nat := 10525155295677714018235

theorem tailTrace_61493 : CollatzResearch.WordTrace tailWord_61493 prefixEnd_61493 10525155295677714018235 := by
  unfold tailWord_61493
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242833966228838013389133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1495222644152558675592755 2242833966228838013389133)
  ·
    refine ⟨841062737335814255020925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2242833966228838013389133 841062737335814255020925)
    ·
      refine ⟨315398526500930345632847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 841062737335814255020925 315398526500930345632847)
      ·
        refine ⟨473097789751395518449271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315398526500930345632847 473097789751395518449271)
        ·
          refine ⟨709646684627093277673907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473097789751395518449271 709646684627093277673907)
          ·
            refine ⟨1064470026940639916510861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709646684627093277673907 1064470026940639916510861)
            ·
              refine ⟨399176260102739968691573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1064470026940639916510861 399176260102739968691573)
              ·
                refine ⟨37422774384631872064835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399176260102739968691573 37422774384631872064835)
                ·
                  refine ⟨56134161576947808097253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37422774384631872064835 56134161576947808097253)
                  ·
                    refine ⟨10525155295677714018235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56134161576947808097253 10525155295677714018235)
                    ·
                      rfl

theorem cell23_61493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_61493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61493 prefixEnd_61493 := by exact prefixLift 61493
  have htrace : WordTrace (prefixWord ++ tailWord_61493) baseStart_61493 baseEnd_61493 := by
    simpa [prefixWord, tailWord_61493, baseEnd_61493] using wordTrace_append hprefix tailTrace_61493
  have hstable : (prefixWord ++ tailWord_61493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61493).length < 2 ^ (prefixWord ++ tailWord_61493).sum := by decide
  have hdescent : baseEnd_61493 < baseStart_61493 := by decide
  rcases family_descends (prefixWord ++ tailWord_61493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61510 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_61510 : Nat := 118140960795 + 61510 * 2 ^ 59
def prefixEnd_61510 : Nat := 4983230072969 + 3 ^ 40 * 61510 * 2
def baseEnd_61510 : Nat := 10528065019386525180709

theorem tailTrace_61510 : CollatzResearch.WordTrace tailWord_61510 prefixEnd_61510 10528065019386525180709 := by
  unfold tailWord_61510
  simp only [CollatzResearch.WordTrace]
  refine ⟨70107937723976559898687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1495636004778166611171989 70107937723976559898687)
  ·
    refine ⟨105161906585964839848031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70107937723976559898687 105161906585964839848031)
    ·
      refine ⟨157742859878947259772047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105161906585964839848031 157742859878947259772047)
      ·
        refine ⟨236614289818420889658071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157742859878947259772047 236614289818420889658071)
        ·
          refine ⟨354921434727631334487107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236614289818420889658071 354921434727631334487107)
          ·
            refine ⟨532382152091447001730661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354921434727631334487107 532382152091447001730661)
            ·
              refine ⟨99821653517146312824499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 532382152091447001730661 99821653517146312824499)
              ·
                refine ⟨149732480275719469236749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99821653517146312824499 149732480275719469236749)
                ·
                  refine ⟨56149680103394800963781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149732480275719469236749 56149680103394800963781)
                  ·
                    refine ⟨10528065019386525180709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56149680103394800963781 10528065019386525180709)
                    ·
                      rfl

theorem cell23_61510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_61510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61510 prefixEnd_61510 := by exact prefixLift 61510
  have htrace : WordTrace (prefixWord ++ tailWord_61510) baseStart_61510 baseEnd_61510 := by
    simpa [prefixWord, tailWord_61510, baseEnd_61510] using wordTrace_append hprefix tailTrace_61510
  have hstable : (prefixWord ++ tailWord_61510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61510).length < 2 ^ (prefixWord ++ tailWord_61510).sum := by decide
  have hdescent : baseEnd_61510 < baseStart_61510 := by decide
  rcases family_descends (prefixWord ++ tailWord_61510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61536 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_61536 : Nat := 118140960795 + 61536 * 2 ^ 59
def prefixEnd_61536 : Nat := 4983230072969 + 3 ^ 40 * 61536 * 2
def baseEnd_61536 : Nat := 10532515185058824605669

theorem tailTrace_61536 : CollatzResearch.WordTrace tailWord_61536 prefixEnd_61536 10532515185058824605669 := by
  unfold tailWord_61536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122201152536528178602231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1496268203382037571469641 1122201152536528178602231)
  ·
    refine ⟨1683301728804792267903347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122201152536528178602231 1683301728804792267903347)
    ·
      refine ⟨2524952593207188401855021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683301728804792267903347 2524952593207188401855021)
      ·
        refine ⟨946857222452695650695633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2524952593207188401855021 946857222452695650695633)
        ·
          refine ⟨710142916839521738021725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946857222452695650695633 710142916839521738021725)
          ·
            refine ⟨266303593814820651758147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710142916839521738021725 266303593814820651758147)
            ·
              refine ⟨399455390722230977637221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266303593814820651758147 399455390722230977637221)
              ·
                refine ⟨74897885760418308306979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399455390722230977637221 74897885760418308306979)
                ·
                  refine ⟨112346828640627462460469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74897885760418308306979 112346828640627462460469)
                  ·
                    refine ⟨10532515185058824605669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112346828640627462460469 10532515185058824605669)
                    ·
                      rfl

theorem cell23_61536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_61536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61536 prefixEnd_61536 := by exact prefixLift 61536
  have htrace : WordTrace (prefixWord ++ tailWord_61536) baseStart_61536 baseEnd_61536 := by
    simpa [prefixWord, tailWord_61536, baseEnd_61536] using wordTrace_append hprefix tailTrace_61536
  have hstable : (prefixWord ++ tailWord_61536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61536).length < 2 ^ (prefixWord ++ tailWord_61536).sum := by decide
  have hdescent : baseEnd_61536 < baseStart_61536 := by decide
  rcases family_descends (prefixWord ++ tailWord_61536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61543 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_61543 : Nat := 118140960795 + 61543 * 2 ^ 59
def prefixEnd_61543 : Nat := 4983230072969 + 3 ^ 40 * 61543 * 2
def baseEnd_61543 : Nat := 31601139919757946429475

theorem tailTrace_61543 : CollatzResearch.WordTrace tailWord_61543 prefixEnd_61543 31601139919757946429475 := by
  unfold tailWord_61543
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244657616047696552709283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496438410698464368472855 2244657616047696552709283)
  ·
    refine ⟨3366986424071544829063925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244657616047696552709283 3366986424071544829063925)
    ·
      refine ⟨315654977256707327724743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3366986424071544829063925 315654977256707327724743)
      ·
        refine ⟨473482465885060991587115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315654977256707327724743 473482465885060991587115)
        ·
          refine ⟨710223698827591487380673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473482465885060991587115 710223698827591487380673)
          ·
            refine ⟨532667774120693615535505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710223698827591487380673 532667774120693615535505)
            ·
              refine ⟨399500830590520211651629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532667774120693615535505 399500830590520211651629)
              ·
                refine ⟨149812811471445079369361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399500830590520211651629 149812811471445079369361)
                ·
                  refine ⟨112359608603583809527021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149812811471445079369361 112359608603583809527021)
                  ·
                    refine ⟨42134853226343928572633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112359608603583809527021 42134853226343928572633)
                    ·
                      refine ⟨31601139919757946429475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42134853226343928572633 31601139919757946429475)
                      ·
                        rfl

theorem cell23_61543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_61543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61543 prefixEnd_61543 := by exact prefixLift 61543
  have htrace : WordTrace (prefixWord ++ tailWord_61543) baseStart_61543 baseEnd_61543 := by
    simpa [prefixWord, tailWord_61543, baseEnd_61543] using wordTrace_append hprefix tailTrace_61543
  have hstable : (prefixWord ++ tailWord_61543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61543).length < 2 ^ (prefixWord ++ tailWord_61543).sum := by decide
  have hdescent : baseEnd_61543 < baseStart_61543 := by decide
  rcases family_descends (prefixWord ++ tailWord_61543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61586 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_61586 : Nat := 118140960795 + 61586 * 2 ^ 59
def prefixEnd_61586 : Nat := 4983230072969 + 3 ^ 40 * 61586 * 2
def baseEnd_61586 : Nat := 31623219587901278191777

theorem tailTrace_61586 : CollatzResearch.WordTrace tailWord_61586 prefixEnd_61586 31623219587901278191777 := by
  unfold tailWord_61586
  simp only [CollatzResearch.WordTrace]
  refine ⟨561556488722978724131153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1497483969927943264349741 561556488722978724131153)
  ·
    refine ⟨421167366542234043098365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 561556488722978724131153 421167366542234043098365)
    ·
      refine ⟨157937762453337766161887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421167366542234043098365 157937762453337766161887)
      ·
        refine ⟨236906643680006649242831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157937762453337766161887 236906643680006649242831)
        ·
          refine ⟨355359965520009973864247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236906643680006649242831 355359965520009973864247)
          ·
            refine ⟨533039948280014960796371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355359965520009973864247 533039948280014960796371)
            ·
              refine ⟨799559922420022441194557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533039948280014960796371 799559922420022441194557)
              ·
                refine ⟨299834970907508415447959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799559922420022441194557 299834970907508415447959)
                ·
                  refine ⟨449752456361262623171939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299834970907508415447959 449752456361262623171939)
                  ·
                    refine ⟨674628684541893934757909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449752456361262623171939 674628684541893934757909)
                    ·
                      refine ⟨31623219587901278191777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 674628684541893934757909 31623219587901278191777)
                      ·
                        rfl

theorem cell23_61586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_61586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61586 prefixEnd_61586 := by exact prefixLift 61586
  have htrace : WordTrace (prefixWord ++ tailWord_61586) baseStart_61586 baseEnd_61586 := by
    simpa [prefixWord, tailWord_61586, baseEnd_61586] using wordTrace_append hprefix tailTrace_61586
  have hstable : (prefixWord ++ tailWord_61586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61586).length < 2 ^ (prefixWord ++ tailWord_61586).sum := by decide
  have hdescent : baseEnd_61586 < baseStart_61586 := by decide
  rcases family_descends (prefixWord ++ tailWord_61586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61607 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_61607 : Nat := 118140960795 + 61607 * 2 ^ 59
def prefixEnd_61607 : Nat := 4983230072969 + 3 ^ 40 * 61607 * 2
def baseEnd_61607 : Nat := 31634002681645696029181

theorem tailTrace_61607 : CollatzResearch.WordTrace tailWord_61607 prefixEnd_61607 31634002681645696029181 := by
  unfold tailWord_61607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246991887815835483039075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1497994591877223655359383 2246991887815835483039075)
  ·
    refine ⟨3370487831723753224558613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2246991887815835483039075 3370487831723753224558613)
    ·
      refine ⟨157991617112050932401185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3370487831723753224558613 157991617112050932401185)
      ·
        refine ⟨118493712834038199300889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157991617112050932401185 118493712834038199300889)
        ·
          refine ⟨88870284625528649475667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118493712834038199300889 88870284625528649475667)
          ·
            refine ⟨133305426938292974213501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88870284625528649475667 133305426938292974213501)
            ·
              refine ⟨49989535101859865330063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133305426938292974213501 49989535101859865330063)
              ·
                refine ⟨74984302652789797995095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49989535101859865330063 74984302652789797995095)
                ·
                  refine ⟨112476453979184696992643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74984302652789797995095 112476453979184696992643)
                  ·
                    refine ⟨168714680968777045488965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112476453979184696992643 168714680968777045488965)
                    ·
                      refine ⟨31634002681645696029181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 168714680968777045488965 31634002681645696029181)
                      ·
                        rfl

theorem cell23_61607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_61607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61607 prefixEnd_61607 := by exact prefixLift 61607
  have htrace : WordTrace (prefixWord ++ tailWord_61607) baseStart_61607 baseEnd_61607 := by
    simpa [prefixWord, tailWord_61607, baseEnd_61607] using wordTrace_append hprefix tailTrace_61607
  have hstable : (prefixWord ++ tailWord_61607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61607).length < 2 ^ (prefixWord ++ tailWord_61607).sum := by decide
  have hdescent : baseEnd_61607 < baseStart_61607 := by decide
  rcases family_descends (prefixWord ++ tailWord_61607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61630 : List Nat := [4, 2, 1, 1, 5, 1, 1, 8]
def baseStart_61630 : Nat := 118140960795 + 61630 * 2 ^ 59
def prefixEnd_61630 : Nat := 4983230072969 + 3 ^ 40 * 61630 * 2
def baseEnd_61630 : Nat := 1172067138396263186725

theorem tailTrace_61630 : CollatzResearch.WordTrace tailWord_61630 prefixEnd_61630 1172067138396263186725 := by
  unfold tailWord_61630
  simp only [CollatzResearch.WordTrace]
  refine ⟨280978845841563801390793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1498553844488340274084229 280978845841563801390793)
  ·
    refine ⟨210734134381172851043095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280978845841563801390793 210734134381172851043095)
    ·
      refine ⟨316101201571759276564643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210734134381172851043095 316101201571759276564643)
      ·
        refine ⟨474151802357638914846965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316101201571759276564643 474151802357638914846965)
        ·
          refine ⟨44451731471028648266903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 474151802357638914846965 44451731471028648266903)
          ·
            refine ⟨66677597206542972400355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44451731471028648266903 66677597206542972400355)
            ·
              refine ⟨100016395809814458600533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66677597206542972400355 100016395809814458600533)
              ·
                refine ⟨1172067138396263186725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 100016395809814458600533 1172067138396263186725)
                ·
                  rfl

theorem cell23_61630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_61630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61630 prefixEnd_61630 := by exact prefixLift 61630
  have htrace : WordTrace (prefixWord ++ tailWord_61630) baseStart_61630 baseEnd_61630 := by
    simpa [prefixWord, tailWord_61630, baseEnd_61630] using wordTrace_append hprefix tailTrace_61630
  have hstable : (prefixWord ++ tailWord_61630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61630).length < 2 ^ (prefixWord ++ tailWord_61630).sum := by decide
  have hdescent : baseEnd_61630 < baseStart_61630 := by decide
  rcases family_descends (prefixWord ++ tailWord_61630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61650 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_61650 : Nat := 118140960795 + 61650 * 2 ^ 59
def prefixEnd_61650 : Nat := 4983230072969 + 3 ^ 40 * 61650 * 2
def baseEnd_61650 : Nat := 31656082349789027791483

theorem tailTrace_61650 : CollatzResearch.WordTrace tailWord_61650 prefixEnd_61650 31656082349789027791483 := by
  unfold tailWord_61650
  simp only [CollatzResearch.WordTrace]
  refine ⟨562140056665013456713601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1499040151106702551236269 562140056665013456713601)
  ·
    refine ⟨421605042498760092535201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562140056665013456713601 421605042498760092535201)
    ·
      refine ⟨316203781874070069401401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421605042498760092535201 316203781874070069401401)
      ·
        refine ⟨237152836405552552051051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316203781874070069401401 237152836405552552051051)
        ·
          refine ⟨355729254608328828076577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237152836405552552051051 355729254608328828076577)
          ·
            refine ⟨266796940956246621057433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355729254608328828076577 266796940956246621057433)
            ·
              refine ⟨200097705717184965793075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266796940956246621057433 200097705717184965793075)
              ·
                refine ⟨300146558575777448689613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200097705717184965793075 300146558575777448689613)
                ·
                  refine ⟨112554959465916543258605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300146558575777448689613 112554959465916543258605)
                  ·
                    refine ⟨42208109799718703721977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112554959465916543258605 42208109799718703721977)
                    ·
                      refine ⟨31656082349789027791483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42208109799718703721977 31656082349789027791483)
                      ·
                        rfl

theorem cell23_61650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_61650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61650 prefixEnd_61650 := by exact prefixLift 61650
  have htrace : WordTrace (prefixWord ++ tailWord_61650) baseStart_61650 baseEnd_61650 := by
    simpa [prefixWord, tailWord_61650, baseEnd_61650] using wordTrace_append hprefix tailTrace_61650
  have hstable : (prefixWord ++ tailWord_61650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61650).length < 2 ^ (prefixWord ++ tailWord_61650).sum := by decide
  have hdescent : baseEnd_61650 < baseStart_61650 := by decide
  rcases family_descends (prefixWord ++ tailWord_61650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61676 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_61676 : Nat := 118140960795 + 61676 * 2 ^ 59
def prefixEnd_61676 : Nat := 4983230072969 + 3 ^ 40 * 61676 * 2
def baseEnd_61676 : Nat := 31669432846805926066363

theorem tailTrace_61676 : CollatzResearch.WordTrace tailWord_61676 prefixEnd_61676 31669432846805926066363 := by
  unfold tailWord_61676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124754262282930133650441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1499672349710573511533921 1124754262282930133650441)
  ·
    refine ⟨843565696712197600237831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124754262282930133650441 843565696712197600237831)
    ·
      refine ⟨1265348545068296400356747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843565696712197600237831 1265348545068296400356747)
      ·
        refine ⟨1898022817602444600535121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265348545068296400356747 1898022817602444600535121)
        ·
          refine ⟨1423517113201833450401341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898022817602444600535121 1423517113201833450401341)
          ·
            refine ⟨533818917450687543900503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1423517113201833450401341 533818917450687543900503)
            ·
              refine ⟨800728376176031315850755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533818917450687543900503 800728376176031315850755)
              ·
                refine ⟨1201092564264046973776133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800728376176031315850755 1201092564264046973776133)
                ·
                  refine ⟨225204855799508807583025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201092564264046973776133 225204855799508807583025)
                  ·
                    refine ⟨168903641849631605687269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225204855799508807583025 168903641849631605687269)
                    ·
                      refine ⟨31669432846805926066363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 168903641849631605687269 31669432846805926066363)
                      ·
                        rfl

theorem cell23_61676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_61676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61676 prefixEnd_61676 := by exact prefixLift 61676
  have htrace : WordTrace (prefixWord ++ tailWord_61676) baseStart_61676 baseEnd_61676 := by
    simpa [prefixWord, tailWord_61676, baseEnd_61676] using wordTrace_append hprefix tailTrace_61676
  have hstable : (prefixWord ++ tailWord_61676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61676).length < 2 ^ (prefixWord ++ tailWord_61676).sum := by decide
  have hdescent : baseEnd_61676 < baseStart_61676 := by decide
  rcases family_descends (prefixWord ++ tailWord_61676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61763 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 3, 4]
def baseStart_61763 : Nat := 118140960795 + 61763 * 2 ^ 59
def prefixEnd_61763 : Nat := 4983230072969 + 3 ^ 40 * 61763 * 2
def baseEnd_61763 : Nat := 10571368554582361892821

theorem tailTrace_61763 : CollatzResearch.WordTrace tailWord_61763 prefixEnd_61763 10571368554582361892821 := by
  unfold tailWord_61763
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252681675250674125717943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501787783500449417145295 2252681675250674125717943)
  ·
    refine ⟨3379022512876011188576915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252681675250674125717943 3379022512876011188576915)
    ·
      refine ⟨5068533769314016782865373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379022512876011188576915 5068533769314016782865373)
      ·
        refine ⟨1900700163492756293574515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5068533769314016782865373 1900700163492756293574515)
        ·
          refine ⟨2851050245239134440361773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900700163492756293574515 2851050245239134440361773)
          ·
            refine ⟨1069143841964675415135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2851050245239134440361773 1069143841964675415135665)
            ·
              refine ⟨801857881473506561351749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069143841964675415135665 801857881473506561351749)
              ·
                refine ⟨150348352776282480253453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801857881473506561351749 150348352776282480253453)
                ·
                  refine ⟨56380632291105930095045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150348352776282480253453 56380632291105930095045)
                  ·
                    refine ⟨10571368554582361892821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56380632291105930095045 10571368554582361892821)
                    ·
                      rfl

theorem cell23_61763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 4].length) (baseStart_61763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61763 prefixEnd_61763 := by exact prefixLift 61763
  have htrace : WordTrace (prefixWord ++ tailWord_61763) baseStart_61763 baseEnd_61763 := by
    simpa [prefixWord, tailWord_61763, baseEnd_61763] using wordTrace_append hprefix tailTrace_61763
  have hstable : (prefixWord ++ tailWord_61763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61763).length < 2 ^ (prefixWord ++ tailWord_61763).sum := by decide
  have hdescent : baseEnd_61763 < baseStart_61763 := by decide
  rcases family_descends (prefixWord ++ tailWord_61763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61797 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_61797 : Nat := 118140960795 + 61797 * 2 ^ 59
def prefixEnd_61797 : Nat := 4983230072969 + 3 ^ 40 * 61797 * 2
def baseEnd_61797 : Nat := 10577188001999984217769

theorem tailTrace_61797 : CollatzResearch.WordTrace tailWord_61797 prefixEnd_61797 10577188001999984217769 := by
  unfold tailWord_61797
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253921757127497932455645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1502614504751665288303763 2253921757127497932455645)
  ·
    refine ⟨845220658922811724670867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2253921757127497932455645 845220658922811724670867)
    ·
      refine ⟨1267830988384217587006301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845220658922811724670867 1267830988384217587006301)
      ·
        refine ⟨475436620644081595127363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1267830988384217587006301 475436620644081595127363)
        ·
          refine ⟨713154930966122392691045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475436620644081595127363 713154930966122392691045)
          ·
            refine ⟨133716549556147948629571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 713154930966122392691045 133716549556147948629571)
            ·
              refine ⟨200574824334221922944357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133716549556147948629571 200574824334221922944357)
              ·
                refine ⟨37607779562666610552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200574824334221922944357 37607779562666610552067)
                ·
                  refine ⟨56411669343999915828101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37607779562666610552067 56411669343999915828101)
                  ·
                    refine ⟨10577188001999984217769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56411669343999915828101 10577188001999984217769)
                    ·
                      rfl

theorem cell23_61797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_61797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61797 prefixEnd_61797 := by exact prefixLift 61797
  have htrace : WordTrace (prefixWord ++ tailWord_61797) baseStart_61797 baseEnd_61797 := by
    simpa [prefixWord, tailWord_61797, baseEnd_61797] using wordTrace_append hprefix tailTrace_61797
  have hstable : (prefixWord ++ tailWord_61797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61797).length < 2 ^ (prefixWord ++ tailWord_61797).sum := by decide
  have hdescent : baseEnd_61797 < baseStart_61797 := by decide
  rcases family_descends (prefixWord ++ tailWord_61797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61814 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_61814 : Nat := 118140960795 + 61814 * 2 ^ 59
def prefixEnd_61814 : Nat := 4983230072969 + 3 ^ 40 * 61814 * 2
def baseEnd_61814 : Nat := 10580097725708795380243

theorem tailTrace_61814 : CollatzResearch.WordTrace tailWord_61814 prefixEnd_61814 10580097725708795380243 := by
  unfold tailWord_61814
  simp only [CollatzResearch.WordTrace]
  refine ⟨140908862379119364739031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1503027865377273223882997 140908862379119364739031)
  ·
    refine ⟨211363293568679047108547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140908862379119364739031 211363293568679047108547)
    ·
      refine ⟨317044940353018570662821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211363293568679047108547 317044940353018570662821)
      ·
        refine ⟨59445926316190981999279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317044940353018570662821 59445926316190981999279)
        ·
          refine ⟨89168889474286472998919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59445926316190981999279 89168889474286472998919)
          ·
            refine ⟨133753334211429709498379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89168889474286472998919 133753334211429709498379)
            ·
              refine ⟨200630001317144564247569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133753334211429709498379 200630001317144564247569)
              ·
                refine ⟨150472500987858423185677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200630001317144564247569 150472500987858423185677)
                ·
                  refine ⟨56427187870446908694629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150472500987858423185677 56427187870446908694629)
                  ·
                    refine ⟨10580097725708795380243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56427187870446908694629 10580097725708795380243)
                    ·
                      rfl

theorem cell23_61814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_61814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61814 prefixEnd_61814 := by exact prefixLift 61814
  have htrace : WordTrace (prefixWord ++ tailWord_61814) baseStart_61814 baseEnd_61814 := by
    simpa [prefixWord, tailWord_61814, baseEnd_61814] using wordTrace_append hprefix tailTrace_61814
  have hstable : (prefixWord ++ tailWord_61814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61814).length < 2 ^ (prefixWord ++ tailWord_61814).sum := by decide
  have hdescent : baseEnd_61814 < baseStart_61814 := by decide
  rcases family_descends (prefixWord ++ tailWord_61814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61844 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 6]
def baseStart_61844 : Nat := 118140960795 + 61844 * 2 ^ 59
def prefixEnd_61844 : Nat := 4983230072969 + 3 ^ 40 * 61844 * 2
def baseEnd_61844 : Nat := 3528410844084585418399

theorem tailTrace_61844 : CollatzResearch.WordTrace tailWord_61844 prefixEnd_61844 3528410844084585418399 := by
  unfold tailWord_61844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127817993978612479708293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1503757325304816639611057 1127817993978612479708293)
  ·
    refine ⟨211465873870989839945305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1127817993978612479708293 211465873870989839945305)
    ·
      refine ⟨158599405403242379958979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211465873870989839945305 158599405403242379958979)
      ·
        refine ⟨237899108104863569938469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158599405403242379958979 237899108104863569938469)
        ·
          refine ⟨44606082769661919363463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237899108104863569938469 44606082769661919363463)
          ·
            refine ⟨66909124154492879045195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44606082769661919363463 66909124154492879045195)
            ·
              refine ⟨100363686231739318567793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66909124154492879045195 100363686231739318567793)
              ·
                refine ⟨75272764673804488925845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100363686231739318567793 75272764673804488925845)
                ·
                  refine ⟨3528410844084585418399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75272764673804488925845 3528410844084585418399)
                  ·
                    rfl

theorem cell23_61844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_61844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61844 prefixEnd_61844 := by exact prefixLift 61844
  have htrace : WordTrace (prefixWord ++ tailWord_61844) baseStart_61844 baseEnd_61844 := by
    simpa [prefixWord, tailWord_61844, baseEnd_61844] using wordTrace_append hprefix tailTrace_61844
  have hstable : (prefixWord ++ tailWord_61844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61844).length < 2 ^ (prefixWord ++ tailWord_61844).sum := by decide
  have hdescent : baseEnd_61844 < baseStart_61844 := by decide
  rcases family_descends (prefixWord ++ tailWord_61844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61854 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_61854 : Nat := 118140960795 + 61854 * 2 ^ 59
def prefixEnd_61854 : Nat := 4983230072969 + 3 ^ 40 * 61854 * 2
def baseEnd_61854 : Nat := 31760832403306229640545

theorem tailTrace_61854 : CollatzResearch.WordTrace tailWord_61854 prefixEnd_61854 31760832403306229640545 := by
  unfold tailWord_61854
  simp only [CollatzResearch.WordTrace]
  refine ⟨282000089740124583410077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1504000478613997778187077 282000089740124583410077)
  ·
    refine ⟨105750033652546718778779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282000089740124583410077 105750033652546718778779)
    ·
      refine ⟨158625050478820078168169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105750033652546718778779 158625050478820078168169)
      ·
        refine ⟨118968787859115058626127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158625050478820078168169 118968787859115058626127)
        ·
          refine ⟨178453181788672587939191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118968787859115058626127 178453181788672587939191)
          ·
            refine ⟨267679772683008881908787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178453181788672587939191 267679772683008881908787)
            ·
              refine ⟨401519659024513322863181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267679772683008881908787 401519659024513322863181)
              ·
                refine ⟨150569872134192496073693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401519659024513322863181 150569872134192496073693)
                ·
                  refine ⟨56463702050322186027635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150569872134192496073693 56463702050322186027635)
                  ·
                    refine ⟨84695553075483279041453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56463702050322186027635 84695553075483279041453)
                    ·
                      refine ⟨31760832403306229640545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 84695553075483279041453 31760832403306229640545)
                      ·
                        rfl

theorem cell23_61854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_61854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61854 prefixEnd_61854 := by exact prefixLift 61854
  have htrace : WordTrace (prefixWord ++ tailWord_61854) baseStart_61854 baseEnd_61854 := by
    simpa [prefixWord, tailWord_61854, baseEnd_61854] using wordTrace_append hprefix tailTrace_61854
  have hstable : (prefixWord ++ tailWord_61854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61854).length < 2 ^ (prefixWord ++ tailWord_61854).sum := by decide
  have hdescent : baseEnd_61854 < baseStart_61854 := by decide
  rcases family_descends (prefixWord ++ tailWord_61854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61900 : List Nat := [2, 2, 1, 4, 3, 2, 9]
def baseStart_61900 : Nat := 118140960795 + 61900 * 2 ^ 59
def prefixEnd_61900 : Nat := 4983230072969 + 3 ^ 40 * 61900 * 2
def baseEnd_61900 : Nat := 392400648313741353893

theorem tailTrace_61900 : CollatzResearch.WordTrace tailWord_61900 prefixEnd_61900 392400648313741353893 := by
  unfold tailWord_61900
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128839237877173261727577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1505118983836231015636769 1128839237877173261727577)
  ·
    refine ⟨846629428407879946295683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1128839237877173261727577 846629428407879946295683)
    ·
      refine ⟨1269944142611819919443525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846629428407879946295683 1269944142611819919443525)
      ·
        refine ⟨238114526739716234895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1269944142611819919443525 238114526739716234895661)
        ·
          refine ⟨89292947527393588085873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238114526739716234895661 89292947527393588085873)
          ·
            refine ⟨66969710645545191064405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89292947527393588085873 66969710645545191064405)
            ·
              refine ⟨392400648313741353893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 66969710645545191064405 392400648313741353893)
              ·
                rfl

theorem cell23_61900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 9].length) (baseStart_61900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61900 prefixEnd_61900 := by exact prefixLift 61900
  have htrace : WordTrace (prefixWord ++ tailWord_61900) baseStart_61900 baseEnd_61900 := by
    simpa [prefixWord, tailWord_61900, baseEnd_61900] using wordTrace_append hprefix tailTrace_61900
  have hstable : (prefixWord ++ tailWord_61900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61900).length < 2 ^ (prefixWord ++ tailWord_61900).sum := by decide
  have hdescent : baseEnd_61900 < baseStart_61900 := by decide
  rcases family_descends (prefixWord ++ tailWord_61900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61913 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 7]
def baseStart_61913 : Nat := 118140960795 + 61913 * 2 ^ 59
def prefixEnd_61913 : Nat := 4983230072969 + 3 ^ 40 * 61913 * 2
def baseEnd_61913 : Nat := 10597042587307166267591

theorem tailTrace_61913 : CollatzResearch.WordTrace tailWord_61913 prefixEnd_61913 10597042587307166267591 := by
  unfold tailWord_61913
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258152624707249743678393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505435083138166495785595 2258152624707249743678393)
  ·
    refine ⟨1693614468530437307758795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2258152624707249743678393 1693614468530437307758795)
    ·
      refine ⟨2540421702795655961638193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693614468530437307758795 2540421702795655961638193)
      ·
        refine ⟨1905316277096741971228645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540421702795655961638193 1905316277096741971228645)
        ·
          refine ⟨357246801955639119605371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1905316277096741971228645 357246801955639119605371)
          ·
            refine ⟨535870202933458679408057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357246801955639119605371 535870202933458679408057)
            ·
              refine ⟨401902652200094009556043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535870202933458679408057 401902652200094009556043)
              ·
                refine ⟨602853978300141014334065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401902652200094009556043 602853978300141014334065)
                ·
                  refine ⟨452140483725105760750549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602853978300141014334065 452140483725105760750549)
                  ·
                    refine ⟨10597042587307166267591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 452140483725105760750549 10597042587307166267591)
                    ·
                      rfl

theorem cell23_61913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_61913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61913 prefixEnd_61913 := by exact prefixLift 61913
  have htrace : WordTrace (prefixWord ++ tailWord_61913) baseStart_61913 baseEnd_61913 := by
    simpa [prefixWord, tailWord_61913, baseEnd_61913] using wordTrace_append hprefix tailTrace_61913
  have hstable : (prefixWord ++ tailWord_61913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61913).length < 2 ^ (prefixWord ++ tailWord_61913).sum := by decide
  have hdescent : baseEnd_61913 < baseStart_61913 := by decide
  rcases family_descends (prefixWord ++ tailWord_61913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61937 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_61937 : Nat := 118140960795 + 61937 * 2 ^ 59
def prefixEnd_61937 : Nat := 4983230072969 + 3 ^ 40 * 61937 * 2
def baseEnd_61937 : Nat := 31803451297629404902663

theorem tailTrace_61937 : CollatzResearch.WordTrace tailWord_61937 prefixEnd_61937 31803451297629404902663 := by
  unfold tailWord_61937
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259027976620301842552065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1506018651080201228368043 2259027976620301842552065)
  ·
    refine ⟨1694270982465226381914049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2259027976620301842552065 1694270982465226381914049)
    ·
      refine ⟨1270703236848919786435537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694270982465226381914049 1270703236848919786435537)
      ·
        refine ⟨953027427636689839826653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270703236848919786435537 953027427636689839826653)
        ·
          refine ⟨357385285363758689934995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953027427636689839826653 357385285363758689934995)
          ·
            refine ⟨536077928045638034902493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357385285363758689934995 536077928045638034902493)
            ·
              refine ⟨201029223017114263088435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536077928045638034902493 201029223017114263088435)
              ·
                refine ⟨301543834525671394632653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201029223017114263088435 301543834525671394632653)
                ·
                  refine ⟨113078937947126772987245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301543834525671394632653 113078937947126772987245)
                  ·
                    refine ⟨42404601730172539870217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113078937947126772987245 42404601730172539870217)
                    ·
                      refine ⟨31803451297629404902663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42404601730172539870217 31803451297629404902663)
                      ·
                        rfl

theorem cell23_61937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_61937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61937 prefixEnd_61937 := by exact prefixLift 61937
  have htrace : WordTrace (prefixWord ++ tailWord_61937) baseStart_61937 baseEnd_61937 := by
    simpa [prefixWord, tailWord_61937, baseEnd_61937] using wordTrace_append hprefix tailTrace_61937
  have hstable : (prefixWord ++ tailWord_61937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61937).length < 2 ^ (prefixWord ++ tailWord_61937).sum := by decide
  have hdescent : baseEnd_61937 < baseStart_61937 := by decide
  rcases family_descends (prefixWord ++ tailWord_61937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61980 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_61980 : Nat := 118140960795 + 61980 * 2 ^ 59
def prefixEnd_61980 : Nat := 4983230072969 + 3 ^ 40 * 61980 * 2
def baseEnd_61980 : Nat := 31825530965772736664965

theorem tailTrace_61980 : CollatzResearch.WordTrace tailWord_61980 prefixEnd_61980 31825530965772736664965 := by
  unfold tailWord_61980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130298157732260093183697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1507064210309680124244929 1130298157732260093183697)
  ·
    refine ⟨847723618299195069887773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1130298157732260093183697 847723618299195069887773)
    ·
      refine ⟨317896356862198151207915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 847723618299195069887773 317896356862198151207915)
      ·
        refine ⟨476844535293297226811873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317896356862198151207915 476844535293297226811873)
        ·
          refine ⟨357633401469972920108905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476844535293297226811873 357633401469972920108905)
          ·
            refine ⟨268225051102479690081679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357633401469972920108905 268225051102479690081679)
            ·
              refine ⟨402337576653719535122519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268225051102479690081679 402337576653719535122519)
              ·
                refine ⟨603506364980579302683779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402337576653719535122519 603506364980579302683779)
                ·
                  refine ⟨905259547470868954025669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603506364980579302683779 905259547470868954025669)
                  ·
                    refine ⟨169736165150787928879813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 905259547470868954025669 169736165150787928879813)
                    ·
                      refine ⟨31825530965772736664965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 169736165150787928879813 31825530965772736664965)
                      ·
                        rfl

theorem cell23_61980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_61980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_61980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_61980 prefixEnd_61980 := by exact prefixLift 61980
  have htrace : WordTrace (prefixWord ++ tailWord_61980) baseStart_61980 baseEnd_61980 := by
    simpa [prefixWord, tailWord_61980, baseEnd_61980] using wordTrace_append hprefix tailTrace_61980
  have hstable : (prefixWord ++ tailWord_61980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61980).length < 2 ^ (prefixWord ++ tailWord_61980).sum := by decide
  have hdescent : baseEnd_61980 < baseStart_61980 := by decide
  rcases family_descends (prefixWord ++ tailWord_61980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62007 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 5]
def baseStart_62007 : Nat := 118140960795 + 62007 * 2 ^ 59
def prefixEnd_62007 : Nat := 4983230072969 + 3 ^ 40 * 62007 * 2
def baseEnd_62007 : Nat := 3537710549271570114149

theorem tailTrace_62007 : CollatzResearch.WordTrace tailWord_62007 prefixEnd_62007 3537710549271570114149 := by
  unfold tailWord_62007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261581086366703797600275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1507720724244469198400183 2261581086366703797600275)
  ·
    refine ⟨3392371629550055696400413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261581086366703797600275 3392371629550055696400413)
    ·
      refine ⟨1272139361081270886150155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3392371629550055696400413 1272139361081270886150155)
      ·
        refine ⟨1908209041621906329225233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272139361081270886150155 1908209041621906329225233)
        ·
          refine ⟨1431156781216429746918925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908209041621906329225233 1431156781216429746918925)
          ·
            refine ⟨536683792956161155094597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1431156781216429746918925 536683792956161155094597)
            ·
              refine ⟨100628211179280216580237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536683792956161155094597 100628211179280216580237)
              ·
                refine ⟨37735579192230081217589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100628211179280216580237 37735579192230081217589)
                ·
                  refine ⟨3537710549271570114149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37735579192230081217589 3537710549271570114149)
                  ·
                    rfl

theorem cell23_62007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 5].length) (baseStart_62007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62007 prefixEnd_62007 := by exact prefixLift 62007
  have htrace : WordTrace (prefixWord ++ tailWord_62007) baseStart_62007 baseEnd_62007 := by
    simpa [prefixWord, tailWord_62007, baseEnd_62007] using wordTrace_append hprefix tailTrace_62007
  have hstable : (prefixWord ++ tailWord_62007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62007).length < 2 ^ (prefixWord ++ tailWord_62007).sum := by decide
  have hdescent : baseEnd_62007 < baseStart_62007 := by decide
  rcases family_descends (prefixWord ++ tailWord_62007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62017 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_62017 : Nat := 118140960795 + 62017 * 2 ^ 59
def prefixEnd_62017 : Nat := 4983230072969 + 3 ^ 40 * 62017 * 2
def baseEnd_62017 : Nat := 31844529749989091902295

theorem tailTrace_62017 : CollatzResearch.WordTrace tailWord_62017 prefixEnd_62017 31844529749989091902295 := by
  unfold tailWord_62017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261945816330475505464305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1507963877553650336976203 2261945816330475505464305)
  ·
    refine ⟨1696459362247856629098229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261945816330475505464305 1696459362247856629098229)
    ·
      refine ⟨159043065210736558977959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1696459362247856629098229 159043065210736558977959)
      ·
        refine ⟨238564597816104838466939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159043065210736558977959 238564597816104838466939)
        ·
          refine ⟨357846896724157257700409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238564597816104838466939 357846896724157257700409)
          ·
            refine ⟨268385172543117943275307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357846896724157257700409 268385172543117943275307)
            ·
              refine ⟨402577758814676914912961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268385172543117943275307 402577758814676914912961)
              ·
                refine ⟨301933319111007686184721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402577758814676914912961 301933319111007686184721)
                ·
                  refine ⟨226449989333255764638541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301933319111007686184721 226449989333255764638541)
                  ·
                    refine ⟨84918745999970911739453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226449989333255764638541 84918745999970911739453)
                    ·
                      refine ⟨31844529749989091902295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 84918745999970911739453 31844529749989091902295)
                      ·
                        rfl

theorem cell23_62017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_62017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62017 prefixEnd_62017 := by exact prefixLift 62017
  have htrace : WordTrace (prefixWord ++ tailWord_62017) baseStart_62017 baseEnd_62017 := by
    simpa [prefixWord, tailWord_62017, baseEnd_62017] using wordTrace_append hprefix tailTrace_62017
  have hstable : (prefixWord ++ tailWord_62017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62017).length < 2 ^ (prefixWord ++ tailWord_62017).sum := by decide
  have hdescent : baseEnd_62017 < baseStart_62017 := by decide
  rcases family_descends (prefixWord ++ tailWord_62017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62030 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_62030 : Nat := 118140960795 + 62030 * 2 ^ 59
def prefixEnd_62030 : Nat := 4983230072969 + 3 ^ 40 * 62030 * 2
def baseEnd_62030 : Nat := 31851204998497541039735

theorem tailTrace_62030 : CollatzResearch.WordTrace tailWord_62030 prefixEnd_62030 31851204998497541039735 := by
  unfold tailWord_62030
  simp only [CollatzResearch.WordTrace]
  refine ⟨282802495660422340710943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1508279976855585817125029 282802495660422340710943)
  ·
    refine ⟨424203743490633511066415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282802495660422340710943 424203743490633511066415)
    ·
      refine ⟨636305615235950266599623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424203743490633511066415 636305615235950266599623)
      ·
        refine ⟨954458422853925399899435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636305615235950266599623 954458422853925399899435)
        ·
          refine ⟨1431687634280888099849153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954458422853925399899435 1431687634280888099849153)
          ·
            refine ⟨1073765725710666074886865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431687634280888099849153 1073765725710666074886865)
            ·
              refine ⟨805324294282999556165149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073765725710666074886865 805324294282999556165149)
              ·
                refine ⟨301996610356124833561931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805324294282999556165149 301996610356124833561931)
                ·
                  refine ⟨452994915534187250342897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301996610356124833561931 452994915534187250342897)
                  ·
                    refine ⟨339746186650640437757173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 452994915534187250342897 339746186650640437757173)
                    ·
                      refine ⟨31851204998497541039735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 339746186650640437757173 31851204998497541039735)
                      ·
                        rfl

theorem cell23_62030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_62030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62030 prefixEnd_62030 := by exact prefixLift 62030
  have htrace : WordTrace (prefixWord ++ tailWord_62030) baseStart_62030 baseEnd_62030 := by
    simpa [prefixWord, tailWord_62030, baseEnd_62030] using wordTrace_append hprefix tailTrace_62030
  have hstable : (prefixWord ++ tailWord_62030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62030).length < 2 ^ (prefixWord ++ tailWord_62030).sum := by decide
  have hdescent : baseEnd_62030 < baseStart_62030 := by decide
  rcases family_descends (prefixWord ++ tailWord_62030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62040 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_62040 : Nat := 118140960795 + 62040 * 2 ^ 59
def prefixEnd_62040 : Nat := 4983230072969 + 3 ^ 40 * 62040 * 2
def baseEnd_62040 : Nat := 31856339805042501914689

theorem tailTrace_62040 : CollatzResearch.WordTrace tailWord_62040 prefixEnd_62040 31856339805042501914689 := by
  unfold tailWord_62040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131392347623575216775787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1508523130164766955701049 1131392347623575216775787)
  ·
    refine ⟨1697088521435362825163681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1131392347623575216775787 1697088521435362825163681)
    ·
      refine ⟨1272816391076522118872761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697088521435362825163681 1272816391076522118872761)
      ·
        refine ⟨954612293307391589154571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1272816391076522118872761 954612293307391589154571)
        ·
          refine ⟨1431918439961087383731857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954612293307391589154571 1431918439961087383731857)
          ·
            refine ⟨1073938829970815537798893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431918439961087383731857 1073938829970815537798893)
            ·
              refine ⟨402727061239055826674585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073938829970815537798893 402727061239055826674585)
              ·
                refine ⟨302045295929291870005939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402727061239055826674585 302045295929291870005939)
                ·
                  refine ⟨453067943893937805008909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302045295929291870005939 453067943893937805008909)
                  ·
                    refine ⟨169900478960226676878341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 453067943893937805008909 169900478960226676878341)
                    ·
                      refine ⟨31856339805042501914689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 169900478960226676878341 31856339805042501914689)
                      ·
                        rfl

theorem cell23_62040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_62040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62040 prefixEnd_62040 := by exact prefixLift 62040
  have htrace : WordTrace (prefixWord ++ tailWord_62040) baseStart_62040 baseEnd_62040 := by
    simpa [prefixWord, tailWord_62040, baseEnd_62040] using wordTrace_append hprefix tailTrace_62040
  have hstable : (prefixWord ++ tailWord_62040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62040).length < 2 ^ (prefixWord ++ tailWord_62040).sum := by decide
  have hdescent : baseEnd_62040 < baseStart_62040 := by decide
  rcases family_descends (prefixWord ++ tailWord_62040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62080 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 8]
def baseStart_62080 : Nat := 118140960795 + 62080 * 2 ^ 59
def prefixEnd_62080 : Nat := 4983230072969 + 3 ^ 40 * 62080 * 2
def baseEnd_62080 : Nat := 3541875447913593934945

theorem tailTrace_62080 : CollatzResearch.WordTrace tailWord_62080 prefixEnd_62080 3541875447913593934945 := by
  unfold tailWord_62080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132121807551118632503847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1509495743401491510005129 1132121807551118632503847)
  ·
    refine ⟨1698182711326677948755771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132121807551118632503847 1698182711326677948755771)
    ·
      refine ⟨2547274066990016923133657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698182711326677948755771 2547274066990016923133657)
      ·
        refine ⟨1910455550242512692350243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547274066990016923133657 1910455550242512692350243)
        ·
          refine ⟨2865683325363769038525365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910455550242512692350243 2865683325363769038525365)
          ·
            refine ⟨268657811752853347361753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2865683325363769038525365 268657811752853347361753)
            ·
              refine ⟨201493358814640010521315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268657811752853347361753 201493358814640010521315)
              ·
                refine ⟨302240038221960015781973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201493358814640010521315 302240038221960015781973)
                ·
                  refine ⟨3541875447913593934945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 302240038221960015781973 3541875447913593934945)
                  ·
                    rfl

theorem cell23_62080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_62080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62080 prefixEnd_62080 := by exact prefixLift 62080
  have htrace : WordTrace (prefixWord ++ tailWord_62080) baseStart_62080 baseEnd_62080 := by
    simpa [prefixWord, tailWord_62080, baseEnd_62080] using wordTrace_append hprefix tailTrace_62080
  have hstable : (prefixWord ++ tailWord_62080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62080).length < 2 ^ (prefixWord ++ tailWord_62080).sum := by decide
  have hdescent : baseEnd_62080 < baseStart_62080 := by decide
  rcases family_descends (prefixWord ++ tailWord_62080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62084 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_62084 : Nat := 118140960795 + 62084 * 2 ^ 59
def prefixEnd_62084 : Nat := 4983230072969 + 3 ^ 40 * 62084 * 2
def baseEnd_62084 : Nat := 10626310984613443254829

theorem tailTrace_62084 : CollatzResearch.WordTrace tailWord_62084 prefixEnd_62084 10626310984613443254829 := by
  unfold tailWord_62084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132194753543872974076653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1509593004725163965435537 1132194753543872974076653)
  ·
    refine ⟨424573032578952365278745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1132194753543872974076653 424573032578952365278745)
    ·
      refine ⟨318429774434214273959059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424573032578952365278745 318429774434214273959059)
      ·
        refine ⟨477644661651321410938589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318429774434214273959059 477644661651321410938589)
        ·
          refine ⟨179116748119245529101971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477644661651321410938589 179116748119245529101971)
          ·
            refine ⟨268675122178868293652957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179116748119245529101971 268675122178868293652957)
            ·
              refine ⟨100753170817075610119859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268675122178868293652957 100753170817075610119859)
              ·
                refine ⟨151129756225613415179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100753170817075610119859 151129756225613415179789)
                ·
                  refine ⟨56673658584605030692421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151129756225613415179789 56673658584605030692421)
                  ·
                    refine ⟨10626310984613443254829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56673658584605030692421 10626310984613443254829)
                    ·
                      rfl

theorem cell23_62084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_62084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62084 prefixEnd_62084 := by exact prefixLift 62084
  have htrace : WordTrace (prefixWord ++ tailWord_62084) baseStart_62084 baseEnd_62084 := by
    simpa [prefixWord, tailWord_62084, baseEnd_62084] using wordTrace_append hprefix tailTrace_62084
  have hstable : (prefixWord ++ tailWord_62084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62084).length < 2 ^ (prefixWord ++ tailWord_62084).sum := by decide
  have hdescent : baseEnd_62084 < baseStart_62084 := by decide
  rcases family_descends (prefixWord ++ tailWord_62084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62107 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 3]
def baseStart_62107 : Nat := 118140960795 + 62107 * 2 ^ 59
def prefixEnd_62107 : Nat := 4983230072969 + 3 ^ 40 * 62107 * 2
def baseEnd_62107 : Nat := 31890743008893739776881

theorem tailTrace_62107 : CollatzResearch.WordTrace tailWord_62107 prefixEnd_62107 31890743008893739776881 := by
  unfold tailWord_62107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265228386004420876240575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1510152257336280584160383 2265228386004420876240575)
  ·
    refine ⟨3397842579006631314360863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265228386004420876240575 3397842579006631314360863)
    ·
      refine ⟨5096763868509946971541295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397842579006631314360863 5096763868509946971541295)
      ·
        refine ⟨7645145802764920457311943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096763868509946971541295 7645145802764920457311943)
        ·
          refine ⟨11467718704147380685967915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645145802764920457311943 11467718704147380685967915)
          ·
            refine ⟨17201578056221071028951873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467718704147380685967915 17201578056221071028951873)
            ·
              refine ⟨12901183542165803271713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17201578056221071028951873 12901183542165803271713905)
              ·
                refine ⟨9675887656624352453785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901183542165803271713905 9675887656624352453785429)
                ·
                  refine ⟨56694654238033315158899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9675887656624352453785429 56694654238033315158899)
                  ·
                    refine ⟨85041981357049972738349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56694654238033315158899 85041981357049972738349)
                    ·
                      refine ⟨31890743008893739776881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85041981357049972738349 31890743008893739776881)
                      ·
                        rfl

theorem cell23_62107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9, 1, 3].length) (baseStart_62107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62107 prefixEnd_62107 := by exact prefixLift 62107
  have htrace : WordTrace (prefixWord ++ tailWord_62107) baseStart_62107 baseEnd_62107 := by
    simpa [prefixWord, tailWord_62107, baseEnd_62107] using wordTrace_append hprefix tailTrace_62107
  have hstable : (prefixWord ++ tailWord_62107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62107).length < 2 ^ (prefixWord ++ tailWord_62107).sum := by decide
  have hdescent : baseEnd_62107 < baseStart_62107 := by decide
  rcases family_descends (prefixWord ++ tailWord_62107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62135 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 1, 4]
def baseStart_62135 : Nat := 118140960795 + 62135 * 2 ^ 59
def prefixEnd_62135 : Nat := 4983230072969 + 3 ^ 40 * 62135 * 2
def baseEnd_62135 : Nat := 10635040155739876742251

theorem tailTrace_62135 : CollatzResearch.WordTrace tailWord_62135 prefixEnd_62135 10635040155739876742251 := by
  unfold tailWord_62135
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266249629902981658259859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1510833086601987772173239 2266249629902981658259859)
  ·
    refine ⟨3399374444854472487389789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2266249629902981658259859 3399374444854472487389789)
    ·
      refine ⟨1274765416820427182771171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3399374444854472487389789 1274765416820427182771171)
      ·
        refine ⟨1912148125230640774156757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274765416820427182771171 1912148125230640774156757)
        ·
          refine ⟨44815971685093143144299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1912148125230640774156757 44815971685093143144299)
          ·
            refine ⟨67223957527639714716449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44815971685093143144299 67223957527639714716449)
            ·
              refine ⟨50417968145729786037337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67223957527639714716449 50417968145729786037337)
              ·
                refine ⟨37813476109297339528003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50417968145729786037337 37813476109297339528003)
                ·
                  refine ⟨56720214163946009292005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37813476109297339528003 56720214163946009292005)
                  ·
                    refine ⟨10635040155739876742251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56720214163946009292005 10635040155739876742251)
                    ·
                      rfl

theorem cell23_62135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_62135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62135 prefixEnd_62135 := by exact prefixLift 62135
  have htrace : WordTrace (prefixWord ++ tailWord_62135) baseStart_62135 baseEnd_62135 := by
    simpa [prefixWord, tailWord_62135, baseEnd_62135] using wordTrace_append hprefix tailTrace_62135
  have hstable : (prefixWord ++ tailWord_62135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62135).length < 2 ^ (prefixWord ++ tailWord_62135).sum := by decide
  have hdescent : baseEnd_62135 < baseStart_62135 := by decide
  rcases family_descends (prefixWord ++ tailWord_62135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_62160 : Nat := 118140960795 + 62160 * 2 ^ 59
def prefixEnd_62160 : Nat := 4983230072969 + 3 ^ 40 * 62160 * 2
def baseEnd_62160 : Nat := 31917957483582032414137

theorem tailTrace_62160 : CollatzResearch.WordTrace tailWord_62160 prefixEnd_62160 31917957483582032414137 := by
  unfold tailWord_62160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133580727406205463959967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1511440969874940618613289 1133580727406205463959967)
  ·
    refine ⟨1700371091109308195939951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133580727406205463959967 1700371091109308195939951)
    ·
      refine ⟨2550556636663962293909927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700371091109308195939951 2550556636663962293909927)
      ·
        refine ⟨3825834954995943440864891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550556636663962293909927 3825834954995943440864891)
        ·
          refine ⟨5738752432493915161297337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825834954995943440864891 5738752432493915161297337)
          ·
            refine ⟨4304064324370436370973003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5738752432493915161297337 4304064324370436370973003)
            ·
              refine ⟨6456096486555654556459505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304064324370436370973003 6456096486555654556459505)
              ·
                refine ⟨4842072364916740917344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6456096486555654556459505 4842072364916740917344629)
                ·
                  refine ⟨453944284210944461001059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842072364916740917344629 453944284210944461001059)
                  ·
                    refine ⟨680916426316416691501589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 453944284210944461001059 680916426316416691501589)
                    ·
                      refine ⟨31917957483582032414137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 680916426316416691501589 31917957483582032414137)
                      ·
                        rfl

theorem cell23_62160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_62160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62160 prefixEnd_62160 := by exact prefixLift 62160
  have htrace : WordTrace (prefixWord ++ tailWord_62160) baseStart_62160 baseEnd_62160 := by
    simpa [prefixWord, tailWord_62160, baseEnd_62160] using wordTrace_append hprefix tailTrace_62160
  have hstable : (prefixWord ++ tailWord_62160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62160).length < 2 ^ (prefixWord ++ tailWord_62160).sum := by decide
  have hdescent : baseEnd_62160 < baseStart_62160 := by decide
  rcases family_descends (prefixWord ++ tailWord_62160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62181 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_62181 : Nat := 118140960795 + 62181 * 2 ^ 59
def prefixEnd_62181 : Nat := 4983230072969 + 3 ^ 40 * 62181 * 2
def baseEnd_62181 : Nat := 31928740577326450251541

theorem tailTrace_62181 : CollatzResearch.WordTrace tailWord_62181 prefixEnd_62181 31928740577326450251541 := by
  unfold tailWord_62181
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267927387736331514434397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1511951591824221009622931 2267927387736331514434397)
  ·
    refine ⟨850472770401124317912899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2267927387736331514434397 850472770401124317912899)
    ·
      refine ⟨1275709155601686476869349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850472770401124317912899 1275709155601686476869349)
      ·
        refine ⟨239195466675316214413003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1275709155601686476869349 239195466675316214413003)
        ·
          refine ⟨358793200012974321619505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239195466675316214413003 358793200012974321619505)
          ·
            refine ⟨269094900009730741214629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358793200012974321619505 269094900009730741214629)
            ·
              refine ⟨50455293751824513977743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269094900009730741214629 50455293751824513977743)
              ·
                refine ⟨75682940627736770966615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50455293751824513977743 75682940627736770966615)
                ·
                  refine ⟨113524410941605156449923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75682940627736770966615 113524410941605156449923)
                  ·
                    refine ⟨170286616412407734674885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113524410941605156449923 170286616412407734674885)
                    ·
                      refine ⟨31928740577326450251541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 170286616412407734674885 31928740577326450251541)
                      ·
                        rfl

theorem cell23_62181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_62181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62181 prefixEnd_62181 := by exact prefixLift 62181
  have htrace : WordTrace (prefixWord ++ tailWord_62181) baseStart_62181 baseEnd_62181 := by
    simpa [prefixWord, tailWord_62181, baseEnd_62181] using wordTrace_append hprefix tailTrace_62181
  have hstable : (prefixWord ++ tailWord_62181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62181).length < 2 ^ (prefixWord ++ tailWord_62181).sum := by decide
  have hdescent : baseEnd_62181 < baseStart_62181 := by decide
  rcases family_descends (prefixWord ++ tailWord_62181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62191 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 2, 4]
def baseStart_62191 : Nat := 118140960795 + 62191 * 2 ^ 59
def prefixEnd_62191 : Nat := 4983230072969 + 3 ^ 40 * 62191 * 2
def baseEnd_62191 : Nat := 10644625127957137042165

theorem tailTrace_62191 : CollatzResearch.WordTrace tailWord_62191 prefixEnd_62191 10644625127957137042165 := by
  unfold tailWord_62191
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268292117700103222298427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1512194745133402148198951 2268292117700103222298427)
  ·
    refine ⟨3402438176550154833447641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2268292117700103222298427 3402438176550154833447641)
    ·
      refine ⟨2551828632412616125085731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402438176550154833447641 2551828632412616125085731)
      ·
        refine ⟨3827742948618924187628597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551828632412616125085731 3827742948618924187628597)
        ·
          refine ⟨358850901433024142590181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3827742948618924187628597 358850901433024142590181)
          ·
            refine ⟨67284544018692026735659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358850901433024142590181 67284544018692026735659)
            ·
              refine ⟨100926816028038040103489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67284544018692026735659 100926816028038040103489)
              ·
                refine ⟨75695112021028530077617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100926816028038040103489 75695112021028530077617)
                ·
                  refine ⟨56771334015771397558213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75695112021028530077617 56771334015771397558213)
                  ·
                    refine ⟨10644625127957137042165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56771334015771397558213 10644625127957137042165)
                    ·
                      rfl

theorem cell23_62191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_62191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62191 prefixEnd_62191 := by exact prefixLift 62191
  have htrace : WordTrace (prefixWord ++ tailWord_62191) baseStart_62191 baseEnd_62191 := by
    simpa [prefixWord, tailWord_62191, baseEnd_62191] using wordTrace_append hprefix tailTrace_62191
  have hstable : (prefixWord ++ tailWord_62191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62191).length < 2 ^ (prefixWord ++ tailWord_62191).sum := by decide
  have hdescent : baseEnd_62191 < baseStart_62191 := by decide
  rcases family_descends (prefixWord ++ tailWord_62191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62198 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_62198 : Nat := 118140960795 + 62198 * 2 ^ 59
def prefixEnd_62198 : Nat := 4983230072969 + 3 ^ 40 * 62198 * 2
def baseEnd_62198 : Nat := 31937469748452883738963

theorem tailTrace_62198 : CollatzResearch.WordTrace tailWord_62198 prefixEnd_62198 31937469748452883738963 := by
  unfold tailWord_62198
  simp only [CollatzResearch.WordTrace]
  refine ⟨141784214292171463612703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1512364952449828945202165 141784214292171463612703)
  ·
    refine ⟨212676321438257195419055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141784214292171463612703 212676321438257195419055)
    ·
      refine ⟨319014482157385793128583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212676321438257195419055 319014482157385793128583)
      ·
        refine ⟨478521723236078689692875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319014482157385793128583 478521723236078689692875)
        ·
          refine ⟨717782584854118034539313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478521723236078689692875 717782584854118034539313)
          ·
            refine ⟨538336938640588525904485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717782584854118034539313 538336938640588525904485)
            ·
              refine ⟨100938175995110348607091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538336938640588525904485 100938175995110348607091)
              ·
                refine ⟨151407263992665522910637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100938175995110348607091 151407263992665522910637)
                ·
                  refine ⟨56777723997249571091489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151407263992665522910637 56777723997249571091489)
                  ·
                    refine ⟨42583292997937178318617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56777723997249571091489 42583292997937178318617)
                    ·
                      refine ⟨31937469748452883738963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42583292997937178318617 31937469748452883738963)
                      ·
                        rfl

theorem cell23_62198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_62198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62198 prefixEnd_62198 := by exact prefixLift 62198
  have htrace : WordTrace (prefixWord ++ tailWord_62198) baseStart_62198 baseEnd_62198 := by
    simpa [prefixWord, tailWord_62198, baseEnd_62198] using wordTrace_append hprefix tailTrace_62198
  have hstable : (prefixWord ++ tailWord_62198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62198).length < 2 ^ (prefixWord ++ tailWord_62198).sum := by decide
  have hdescent : baseEnd_62198 < baseStart_62198 := by decide
  rcases family_descends (prefixWord ++ tailWord_62198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62241 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_62241 : Nat := 118140960795 + 62241 * 2 ^ 59
def prefixEnd_62241 : Nat := 4983230072969 + 3 ^ 40 * 62241 * 2
def baseEnd_62241 : Nat := 31959549416596215501265

theorem tailTrace_62241 : CollatzResearch.WordTrace tailWord_62241 prefixEnd_62241 31959549416596215501265 := by
  unfold tailWord_62241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270115767518961761618577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1513410511679307841079051 2270115767518961761618577)
  ·
    refine ⟨1702586825639221321213933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2270115767518961761618577 1702586825639221321213933)
    ·
      refine ⟨638470059614707995455225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1702586825639221321213933 638470059614707995455225)
      ·
        refine ⟨478852544711030996591419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638470059614707995455225 478852544711030996591419)
        ·
          refine ⟨718278817066546494887129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478852544711030996591419 718278817066546494887129)
          ·
            refine ⟨538709112799909871165347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718278817066546494887129 538709112799909871165347)
            ·
              refine ⟨808063669199864806748021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538709112799909871165347 808063669199864806748021)
              ·
                refine ⟨75755968987487325632627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 808063669199864806748021 75755968987487325632627)
                ·
                  refine ⟨113633953481230988448941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75755968987487325632627 113633953481230988448941)
                  ·
                    refine ⟨42612732555461620668353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113633953481230988448941 42612732555461620668353)
                    ·
                      refine ⟨31959549416596215501265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42612732555461620668353 31959549416596215501265)
                      ·
                        rfl

theorem cell23_62241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_62241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62241 prefixEnd_62241 := by exact prefixLift 62241
  have htrace : WordTrace (prefixWord ++ tailWord_62241) baseStart_62241 baseEnd_62241 := by
    simpa [prefixWord, tailWord_62241, baseEnd_62241] using wordTrace_append hprefix tailTrace_62241
  have hstable : (prefixWord ++ tailWord_62241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62241).length < 2 ^ (prefixWord ++ tailWord_62241).sum := by decide
  have hdescent : baseEnd_62241 < baseStart_62241 := by decide
  rcases family_descends (prefixWord ++ tailWord_62241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62257 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_62257 : Nat := 118140960795 + 62257 * 2 ^ 59
def prefixEnd_62257 : Nat := 4983230072969 + 3 ^ 40 * 62257 * 2
def baseEnd_62257 : Nat := 31967765107068152901191

theorem tailTrace_62257 : CollatzResearch.WordTrace tailWord_62257 prefixEnd_62257 31967765107068152901191 := by
  unfold tailWord_62257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270699335460996494201025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1513799556973997662800683 2270699335460996494201025)
  ·
    refine ⟨1703024501595747370650769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2270699335460996494201025 1703024501595747370650769)
    ·
      refine ⟨1277268376196810527988077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703024501595747370650769 1277268376196810527988077)
      ·
        refine ⟨478975641073803947995529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1277268376196810527988077 478975641073803947995529)
        ·
          refine ⟨359231730805352960996647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478975641073803947995529 359231730805352960996647)
          ·
            refine ⟨538847596208029441494971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359231730805352960996647 538847596208029441494971)
            ·
              refine ⟨808271394312044162242457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538847596208029441494971 808271394312044162242457)
              ·
                refine ⟨606203545734033121681843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808271394312044162242457 606203545734033121681843)
                ·
                  refine ⟨909305318601049682522765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606203545734033121681843 909305318601049682522765)
                  ·
                    refine ⟨340989494475393630946037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909305318601049682522765 340989494475393630946037)
                    ·
                      refine ⟨31967765107068152901191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 340989494475393630946037 31967765107068152901191)
                      ·
                        rfl

theorem cell23_62257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_62257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62257 prefixEnd_62257 := by exact prefixLift 62257
  have htrace : WordTrace (prefixWord ++ tailWord_62257) baseStart_62257 baseEnd_62257 := by
    simpa [prefixWord, tailWord_62257, baseEnd_62257] using wordTrace_append hprefix tailTrace_62257
  have hstable : (prefixWord ++ tailWord_62257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62257).length < 2 ^ (prefixWord ++ tailWord_62257).sum := by decide
  have hdescent : baseEnd_62257 < baseStart_62257 := by decide
  rcases family_descends (prefixWord ++ tailWord_62257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62304 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_62304 : Nat := 118140960795 + 62304 * 2 ^ 59
def prefixEnd_62304 : Nat := 4983230072969 + 3 ^ 40 * 62304 * 2
def baseEnd_62304 : Nat := 31991898697829469013475

theorem tailTrace_62304 : CollatzResearch.WordTrace tailWord_62304 prefixEnd_62304 31991898697829469013475 := by
  unfold tailWord_62304
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136206783145361760580983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1514942377527149014107977 1136206783145361760580983)
  ·
    refine ⟨1704310174718042640871475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1136206783145361760580983 1704310174718042640871475)
    ·
      refine ⟨2556465262077063961307213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704310174718042640871475 2556465262077063961307213)
      ·
        refine ⟨958674473278898985490205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2556465262077063961307213 958674473278898985490205)
        ·
          refine ⟨359502927479587119558827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958674473278898985490205 359502927479587119558827)
          ·
            refine ⟨539254391219380679338241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359502927479587119558827 539254391219380679338241)
            ·
              refine ⟨404440793414535509503681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539254391219380679338241 404440793414535509503681)
              ·
                refine ⟨303330595060901632127761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404440793414535509503681 303330595060901632127761)
                ·
                  refine ⟨227497946295676224095821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303330595060901632127761 227497946295676224095821)
                  ·
                    refine ⟨85311729860878584035933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227497946295676224095821 85311729860878584035933)
                    ·
                      refine ⟨31991898697829469013475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85311729860878584035933 31991898697829469013475)
                      ·
                        rfl

theorem cell23_62304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_62304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62304 prefixEnd_62304 := by exact prefixLift 62304
  have htrace : WordTrace (prefixWord ++ tailWord_62304) baseStart_62304 baseEnd_62304 := by
    simpa [prefixWord, tailWord_62304, baseEnd_62304] using wordTrace_append hprefix tailTrace_62304
  have hstable : (prefixWord ++ tailWord_62304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62304).length < 2 ^ (prefixWord ++ tailWord_62304).sum := by decide
  have hdescent : baseEnd_62304 < baseStart_62304 := by decide
  rcases family_descends (prefixWord ++ tailWord_62304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62311 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 5]
def baseStart_62311 : Nat := 118140960795 + 62311 * 2 ^ 59
def prefixEnd_62311 : Nat := 4983230072969 + 3 ^ 40 * 62311 * 2
def baseEnd_62311 : Nat := 3555054784712326847327

theorem tailTrace_62311 : CollatzResearch.WordTrace tailWord_62311 prefixEnd_62311 3555054784712326847327 := by
  unfold tailWord_62311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272668877265363716666787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1515112584843575811111191 2272668877265363716666787)
  ·
    refine ⟨3409003315898045575000181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2272668877265363716666787 3409003315898045575000181)
    ·
      refine ⟨319594060865441772656267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3409003315898045575000181 319594060865441772656267)
      ·
        refine ⟨479391091298162658984401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319594060865441772656267 479391091298162658984401)
        ·
          refine ⟨359543318473621994238301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479391091298162658984401 359543318473621994238301)
          ·
            refine ⟨134828744427608247839363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359543318473621994238301 134828744427608247839363)
            ·
              refine ⟨202243116641412371759045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134828744427608247839363 202243116641412371759045)
              ·
                refine ⟨37920584370264819704821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202243116641412371759045 37920584370264819704821)
                ·
                  refine ⟨3555054784712326847327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37920584370264819704821 3555054784712326847327)
                  ·
                    rfl

theorem cell23_62311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 5].length) (baseStart_62311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62311 prefixEnd_62311 := by exact prefixLift 62311
  have htrace : WordTrace (prefixWord ++ tailWord_62311) baseStart_62311 baseEnd_62311 := by
    simpa [prefixWord, tailWord_62311, baseEnd_62311] using wordTrace_append hprefix tailTrace_62311
  have hstable : (prefixWord ++ tailWord_62311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62311).length < 2 ^ (prefixWord ++ tailWord_62311).sum := by decide
  have hdescent : baseEnd_62311 < baseStart_62311 := by decide
  rcases family_descends (prefixWord ++ tailWord_62311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62341 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_62341 : Nat := 118140960795 + 62341 * 2 ^ 59
def prefixEnd_62341 : Nat := 4983230072969 + 3 ^ 40 * 62341 * 2
def baseEnd_62341 : Nat := 10670299160681941416935

theorem tailTrace_62341 : CollatzResearch.WordTrace tailWord_62341 prefixEnd_62341 10670299160681941416935 := by
  unfold tailWord_62341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2273763067156678840258877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1515842044771119226839251 2273763067156678840258877)
  ·
    refine ⟨852661150183754565097079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2273763067156678840258877 852661150183754565097079)
    ·
      refine ⟨1278991725275631847645619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852661150183754565097079 1278991725275631847645619)
      ·
        refine ⟨1918487587913447771468429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278991725275631847645619 1918487587913447771468429)
        ·
          refine ⟨719432845467542914300661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1918487587913447771468429 719432845467542914300661)
          ·
            refine ⟨67446829262582148215687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 719432845467542914300661 67446829262582148215687)
            ·
              refine ⟨101170243893873222323531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67446829262582148215687 101170243893873222323531)
              ·
                refine ⟨151755365840809833485297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101170243893873222323531 151755365840809833485297)
                ·
                  refine ⟨113816524380607375113973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151755365840809833485297 113816524380607375113973)
                  ·
                    refine ⟨10670299160681941416935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113816524380607375113973 10670299160681941416935)
                    ·
                      rfl

theorem cell23_62341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_62341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62341 prefixEnd_62341 := by exact prefixLift 62341
  have htrace : WordTrace (prefixWord ++ tailWord_62341) baseStart_62341 baseEnd_62341 := by
    simpa [prefixWord, tailWord_62341, baseEnd_62341] using wordTrace_append hprefix tailTrace_62341
  have hstable : (prefixWord ++ tailWord_62341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62341).length < 2 ^ (prefixWord ++ tailWord_62341).sum := by decide
  have hdescent : baseEnd_62341 < baseStart_62341 := by decide
  rcases family_descends (prefixWord ++ tailWord_62341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62394 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_62394 : Nat := 118140960795 + 62394 * 2 ^ 59
def prefixEnd_62394 : Nat := 4983230072969 + 3 ^ 40 * 62394 * 2
def baseEnd_62394 : Nat := 32038111956734116888061

theorem tailTrace_62394 : CollatzResearch.WordTrace tailWord_62394 prefixEnd_62394 32038111956734116888061 := by
  unfold tailWord_62394
  simp only [CollatzResearch.WordTrace]
  refine ⟨568924033991167222984559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1517130757309779261292157 568924033991167222984559)
  ·
    refine ⟨853386050986750834476839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 568924033991167222984559 853386050986750834476839)
    ·
      refine ⟨1280079076480126251715259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853386050986750834476839 1280079076480126251715259)
      ·
        refine ⟨1920118614720189377572889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280079076480126251715259 1920118614720189377572889)
        ·
          refine ⟨1440088961040142033179667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1920118614720189377572889 1440088961040142033179667)
          ·
            refine ⟨2160133441560213049769501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440088961040142033179667 2160133441560213049769501)
            ·
              refine ⟨810050040585079893663563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2160133441560213049769501 810050040585079893663563)
              ·
                refine ⟨1215075060877619840495345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810050040585079893663563 1215075060877619840495345)
                ·
                  refine ⟨911306295658214880371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1215075060877619840495345 911306295658214880371509)
                  ·
                    refine ⟨85434965217957645034829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 911306295658214880371509 85434965217957645034829)
                    ·
                      refine ⟨32038111956734116888061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85434965217957645034829 32038111956734116888061)
                      ·
                        rfl

theorem cell23_62394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_62394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62394 prefixEnd_62394 := by exact prefixLift 62394
  have htrace : WordTrace (prefixWord ++ tailWord_62394) baseStart_62394 baseEnd_62394 := by
    simpa [prefixWord, tailWord_62394, baseEnd_62394] using wordTrace_append hprefix tailTrace_62394
  have hstable : (prefixWord ++ tailWord_62394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62394).length < 2 ^ (prefixWord ++ tailWord_62394).sum := by decide
  have hdescent : baseEnd_62394 < baseStart_62394 := by decide
  rcases family_descends (prefixWord ++ tailWord_62394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62474 : List Nat := [3, 1, 2, 2, 3, 12]
def baseStart_62474 : Nat := 118140960795 + 62474 * 2 ^ 59
def prefixEnd_62474 : Nat := 4983230072969 + 3 ^ 40 * 62474 * 2
def baseEnd_62474 : Nat := 132013129255530057151

theorem tailTrace_62474 : CollatzResearch.WordTrace tailWord_62474 prefixEnd_62474 132013129255530057151 := by
  unfold tailWord_62474
  simp only [CollatzResearch.WordTrace]
  refine ⟨569653493918710638712619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1519075983783228369900317 569653493918710638712619)
  ·
    refine ⟨854480240878065958068929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569653493918710638712619 854480240878065958068929)
    ·
      refine ⟨640860180658549468551697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 854480240878065958068929 640860180658549468551697)
      ·
        refine ⟨480645135493912101413773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640860180658549468551697 480645135493912101413773)
        ·
          refine ⟨180241925810217038030165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480645135493912101413773 180241925810217038030165)
          ·
            refine ⟨132013129255530057151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 180241925810217038030165 132013129255530057151)
            ·
              rfl

theorem cell23_62474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 12].length) (baseStart_62474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62474 prefixEnd_62474 := by exact prefixLift 62474
  have htrace : WordTrace (prefixWord ++ tailWord_62474) baseStart_62474 baseEnd_62474 := by
    simpa [prefixWord, tailWord_62474, baseEnd_62474] using wordTrace_append hprefix tailTrace_62474
  have hstable : (prefixWord ++ tailWord_62474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62474).length < 2 ^ (prefixWord ++ tailWord_62474).sum := by decide
  have hdescent : baseEnd_62474 < baseStart_62474 := by decide
  rcases family_descends (prefixWord ++ tailWord_62474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62478 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_62478 : Nat := 118140960795 + 62478 * 2 ^ 59
def prefixEnd_62478 : Nat := 4983230072969 + 3 ^ 40 * 62478 * 2
def baseEnd_62478 : Nat := 10693748110570596079225

theorem tailTrace_62478 : CollatzResearch.WordTrace tailWord_62478 prefixEnd_62478 10693748110570596079225 := by
  unfold tailWord_62478
  simp only [CollatzResearch.WordTrace]
  refine ⟨284844983457543904749511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1519173245106900825330725 284844983457543904749511)
  ·
    refine ⟨427267475186315857124267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284844983457543904749511 427267475186315857124267)
    ·
      refine ⟨640901212779473785686401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427267475186315857124267 640901212779473785686401)
      ·
        refine ⟨480675909584605339264801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640901212779473785686401 480675909584605339264801)
        ·
          refine ⟨360506932188454004448601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480675909584605339264801 360506932188454004448601)
          ·
            refine ⟨270380199141340503336451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360506932188454004448601 270380199141340503336451)
            ·
              refine ⟨405570298712010755004677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270380199141340503336451 405570298712010755004677)
              ·
                refine ⟨76044431008502016563377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405570298712010755004677 76044431008502016563377)
                ·
                  refine ⟨57033323256376512422533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76044431008502016563377 57033323256376512422533)
                  ·
                    refine ⟨10693748110570596079225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57033323256376512422533 10693748110570596079225)
                    ·
                      rfl

theorem cell23_62478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_62478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62478 prefixEnd_62478 := by exact prefixLift 62478
  have htrace : WordTrace (prefixWord ++ tailWord_62478) baseStart_62478 baseEnd_62478 := by
    simpa [prefixWord, tailWord_62478, baseEnd_62478] using wordTrace_append hprefix tailTrace_62478
  have hstable : (prefixWord ++ tailWord_62478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62478).length < 2 ^ (prefixWord ++ tailWord_62478).sum := by decide
  have hdescent : baseEnd_62478 < baseStart_62478 := by decide
  rcases family_descends (prefixWord ++ tailWord_62478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62498 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_62498 : Nat := 118140960795 + 62498 * 2 ^ 59
def prefixEnd_62498 : Nat := 4983230072969 + 3 ^ 40 * 62498 * 2
def baseEnd_62498 : Nat := 32091513944801709987583

theorem tailTrace_62498 : CollatzResearch.WordTrace tailWord_62498 prefixEnd_62498 32091513944801709987583 := by
  unfold tailWord_62498
  simp only [CollatzResearch.WordTrace]
  refine ⟨569872331896973663431037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1519659551725263102482765 569872331896973663431037)
  ·
    refine ⟨213702124461365123786639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 569872331896973663431037 213702124461365123786639)
    ·
      refine ⟨320553186692047685679959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213702124461365123786639 320553186692047685679959)
      ·
        refine ⟨480829780038071528519939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320553186692047685679959 480829780038071528519939)
        ·
          refine ⟨721244670057107292779909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480829780038071528519939 721244670057107292779909)
          ·
            refine ⟨135233375635707617396233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 721244670057107292779909 135233375635707617396233)
            ·
              refine ⟨101425031726780713047175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135233375635707617396233 101425031726780713047175)
              ·
                refine ⟨152137547590171069570763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101425031726780713047175 152137547590171069570763)
                ·
                  refine ⟨228206321385256604356145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152137547590171069570763 228206321385256604356145)
                  ·
                    refine ⟨171154741038942453267109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228206321385256604356145 171154741038942453267109)
                    ·
                      refine ⟨32091513944801709987583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 171154741038942453267109 32091513944801709987583)
                      ·
                        rfl

theorem cell23_62498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_62498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62498 prefixEnd_62498 := by exact prefixLift 62498
  have htrace : WordTrace (prefixWord ++ tailWord_62498) baseStart_62498 baseEnd_62498 := by
    simpa [prefixWord, tailWord_62498, baseEnd_62498] using wordTrace_append hprefix tailTrace_62498
  have hstable : (prefixWord ++ tailWord_62498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62498).length < 2 ^ (prefixWord ++ tailWord_62498).sum := by decide
  have hdescent : baseEnd_62498 < baseStart_62498 := by decide
  rcases family_descends (prefixWord ++ tailWord_62498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62535 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_62535 : Nat := 118140960795 + 62535 * 2 ^ 59
def prefixEnd_62535 : Nat := 4983230072969 + 3 ^ 40 * 62535 * 2
def baseEnd_62535 : Nat := 32110512729018065224913

theorem tailTrace_62535 : CollatzResearch.WordTrace tailWord_62535 prefixEnd_62535 32110512729018065224913 := by
  unfold tailWord_62535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280838828453849972821059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1520559218969233315214039 2280838828453849972821059)
  ·
    refine ⟨3421258242680774959231589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280838828453849972821059 3421258242680774959231589)
    ·
      refine ⟨641485920502645304855923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3421258242680774959231589 641485920502645304855923)
      ·
        refine ⟨962228880753967957283885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641485920502645304855923 962228880753967957283885)
        ·
          refine ⟨360835830282737983981457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962228880753967957283885 360835830282737983981457)
          ·
            refine ⟨270626872712053487986093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360835830282737983981457 270626872712053487986093)
            ·
              refine ⟨101485077267020057994785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270626872712053487986093 101485077267020057994785)
              ·
                refine ⟨76113807950265043496089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101485077267020057994785 76113807950265043496089)
                ·
                  refine ⟨57085355962698782622067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76113807950265043496089 57085355962698782622067)
                  ·
                    refine ⟨85628033944048173933101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57085355962698782622067 85628033944048173933101)
                    ·
                      refine ⟨32110512729018065224913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85628033944048173933101 32110512729018065224913)
                      ·
                        rfl

theorem cell23_62535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_62535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62535 prefixEnd_62535 := by exact prefixLift 62535
  have htrace : WordTrace (prefixWord ++ tailWord_62535) baseStart_62535 baseEnd_62535 := by
    simpa [prefixWord, tailWord_62535, baseEnd_62535] using wordTrace_append hprefix tailTrace_62535
  have hstable : (prefixWord ++ tailWord_62535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62535).length < 2 ^ (prefixWord ++ tailWord_62535).sum := by decide
  have hdescent : baseEnd_62535 < baseStart_62535 := by decide
  rcases family_descends (prefixWord ++ tailWord_62535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62561 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_62561 : Nat := 118140960795 + 62561 * 2 ^ 59
def prefixEnd_62561 : Nat := 4983230072969 + 3 ^ 40 * 62561 * 2
def baseEnd_62561 : Nat := 32123863226034963499793

theorem tailTrace_62561 : CollatzResearch.WordTrace tailWord_62561 prefixEnd_62561 32123863226034963499793 := by
  unfold tailWord_62561
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281787126359656413267537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521191417573104275511691 2281787126359656413267537)
  ·
    refine ⟨1711340344769742309950653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2281787126359656413267537 1711340344769742309950653)
    ·
      refine ⟨641752629288653366231495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1711340344769742309950653 641752629288653366231495)
      ·
        refine ⟨962628943932980049347243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641752629288653366231495 962628943932980049347243)
        ·
          refine ⟨1443943415899470074020865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962628943932980049347243 1443943415899470074020865)
          ·
            refine ⟨1082957561924602555515649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443943415899470074020865 1082957561924602555515649)
            ·
              refine ⟨812218171443451916636737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082957561924602555515649 812218171443451916636737)
              ·
                refine ⟨609163628582588937477553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812218171443451916636737 609163628582588937477553)
                ·
                  refine ⟨456872721436941703108165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609163628582588937477553 456872721436941703108165)
                  ·
                    refine ⟨85663635269426569332781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 456872721436941703108165 85663635269426569332781)
                    ·
                      refine ⟨32123863226034963499793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85663635269426569332781 32123863226034963499793)
                      ·
                        rfl

theorem cell23_62561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_62561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62561 prefixEnd_62561 := by exact prefixLift 62561
  have htrace : WordTrace (prefixWord ++ tailWord_62561) baseStart_62561 baseEnd_62561 := by
    simpa [prefixWord, tailWord_62561, baseEnd_62561] using wordTrace_append hprefix tailTrace_62561
  have hstable : (prefixWord ++ tailWord_62561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62561).length < 2 ^ (prefixWord ++ tailWord_62561).sum := by decide
  have hdescent : baseEnd_62561 < baseStart_62561 := by decide
  rcases family_descends (prefixWord ++ tailWord_62561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62562 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_62562 : Nat := 118140960795 + 62562 * 2 ^ 59
def prefixEnd_62562 : Nat := 4983230072969 + 3 ^ 40 * 62562 * 2
def baseEnd_62562 : Nat := 32124376706689459587289

theorem tailTrace_62562 : CollatzResearch.WordTrace tailWord_62562 prefixEnd_62562 32124376706689459587289 := by
  unfold tailWord_62562
  simp only [CollatzResearch.WordTrace]
  refine ⟨570455899839008396013485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1521215732904022389369293 570455899839008396013485)
  ·
    refine ⟨213920962439628148505057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 570455899839008396013485 213920962439628148505057)
    ·
      refine ⟨160440721829721111378793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213920962439628148505057 160440721829721111378793)
      ·
        refine ⟨120330541372290833534095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160440721829721111378793 120330541372290833534095)
        ·
          refine ⟨180495812058436250301143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120330541372290833534095 180495812058436250301143)
          ·
            refine ⟨270743718087654375451715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180495812058436250301143 270743718087654375451715)
            ·
              refine ⟨406115577131481563177573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270743718087654375451715 406115577131481563177573)
              ·
                refine ⟨76146670712152793095795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406115577131481563177573 76146670712152793095795)
                ·
                  refine ⟨114220006068229189643693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76146670712152793095795 114220006068229189643693)
                  ·
                    refine ⟨42832502275585946116385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114220006068229189643693 42832502275585946116385)
                    ·
                      refine ⟨32124376706689459587289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 42832502275585946116385 32124376706689459587289)
                      ·
                        rfl

theorem cell23_62562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_62562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62562 prefixEnd_62562 := by exact prefixLift 62562
  have htrace : WordTrace (prefixWord ++ tailWord_62562) baseStart_62562 baseEnd_62562 := by
    simpa [prefixWord, tailWord_62562, baseEnd_62562] using wordTrace_append hprefix tailTrace_62562
  have hstable : (prefixWord ++ tailWord_62562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62562).length < 2 ^ (prefixWord ++ tailWord_62562).sum := by decide
  have hdescent : baseEnd_62562 < baseStart_62562 := by decide
  rcases family_descends (prefixWord ++ tailWord_62562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62621 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_62621 : Nat := 118140960795 + 62621 * 2 ^ 59
def prefixEnd_62621 : Nat := 4983230072969 + 3 ^ 40 * 62621 * 2
def baseEnd_62621 : Nat := 32154672065304728749517

theorem tailTrace_62621 : CollatzResearch.WordTrace tailWord_62621 prefixEnd_62621 32154672065304728749517 := by
  unfold tailWord_62621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283975506142286660451717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1522650337428191106967811 2283975506142286660451717)
  ·
    refine ⟨428245407401678748834697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2283975506142286660451717 428245407401678748834697)
    ·
      refine ⟨321184055551259061626023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428245407401678748834697 321184055551259061626023)
      ·
        refine ⟨481776083326888592439035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321184055551259061626023 481776083326888592439035)
        ·
          refine ⟨722664124990332888658553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481776083326888592439035 722664124990332888658553)
          ·
            refine ⟨541998093742749666493915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722664124990332888658553 541998093742749666493915)
            ·
              refine ⟨812997140614124499740873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541998093742749666493915 812997140614124499740873)
              ·
                refine ⟨609747855460593374805655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812997140614124499740873 609747855460593374805655)
                ·
                  refine ⟨914621783190890062208483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609747855460593374805655 914621783190890062208483)
                  ·
                    refine ⟨1371932674786335093312725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914621783190890062208483 1371932674786335093312725)
                    ·
                      refine ⟨32154672065304728749517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1371932674786335093312725 32154672065304728749517)
                      ·
                        rfl

theorem cell23_62621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_62621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62621 prefixEnd_62621 := by exact prefixLift 62621
  have htrace : WordTrace (prefixWord ++ tailWord_62621) baseStart_62621 baseEnd_62621 := by
    simpa [prefixWord, tailWord_62621, baseEnd_62621] using wordTrace_append hprefix tailTrace_62621
  have hstable : (prefixWord ++ tailWord_62621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62621).length < 2 ^ (prefixWord ++ tailWord_62621).sum := by decide
  have hdescent : baseEnd_62621 < baseStart_62621 := by decide
  rcases family_descends (prefixWord ++ tailWord_62621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62628 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_62628 : Nat := 118140960795 + 62628 * 2 ^ 59
def prefixEnd_62628 : Nat := 4983230072969 + 3 ^ 40 * 62628 * 2
def baseEnd_62628 : Nat := 10719422143295400453995

theorem tailTrace_62628 : CollatzResearch.WordTrace tailWord_62628 prefixEnd_62628 10719422143295400453995 := by
  unfold tailWord_62628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142115408558463427978269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1522820544744617903971025 1142115408558463427978269)
  ·
    refine ⟨428293278209423785491851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1142115408558463427978269 428293278209423785491851)
    ·
      refine ⟨642439917314135678237777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428293278209423785491851 642439917314135678237777)
      ·
        refine ⟨481829937985601758678333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642439917314135678237777 481829937985601758678333)
        ·
          refine ⟨180686226744600659504375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481829937985601758678333 180686226744600659504375)
          ·
            refine ⟨271029340116900989256563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180686226744600659504375 271029340116900989256563)
            ·
              refine ⟨406544010175351483884845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271029340116900989256563 406544010175351483884845)
              ·
                refine ⟨152454003815756806456817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406544010175351483884845 152454003815756806456817)
                ·
                  refine ⟨114340502861817604842613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152454003815756806456817 114340502861817604842613)
                  ·
                    refine ⟨10719422143295400453995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114340502861817604842613 10719422143295400453995)
                    ·
                      rfl

theorem cell23_62628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_62628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62628 prefixEnd_62628 := by exact prefixLift 62628
  have htrace : WordTrace (prefixWord ++ tailWord_62628) baseStart_62628 baseEnd_62628 := by
    simpa [prefixWord, tailWord_62628, baseEnd_62628] using wordTrace_append hprefix tailTrace_62628
  have hstable : (prefixWord ++ tailWord_62628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62628).length < 2 ^ (prefixWord ++ tailWord_62628).sum := by decide
  have hdescent : baseEnd_62628 < baseStart_62628 := by decide
  rcases family_descends (prefixWord ++ tailWord_62628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62661 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_62661 : Nat := 118140960795 + 62661 * 2 ^ 59
def prefixEnd_62661 : Nat := 4983230072969 + 3 ^ 40 * 62661 * 2
def baseEnd_62661 : Nat := 32175211291484572249333

theorem tailTrace_62661 : CollatzResearch.WordTrace tailWord_62661 prefixEnd_62661 32175211291484572249333 := by
  unfold tailWord_62661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285434425997373491907837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1523622950664915661271891 2285434425997373491907837)
  ·
    refine ⟨857037909749015059465439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2285434425997373491907837 857037909749015059465439)
    ·
      refine ⟨1285556864623522589198159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857037909749015059465439 1285556864623522589198159)
      ·
        refine ⟨1928335296935283883797239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285556864623522589198159 1928335296935283883797239)
        ·
          refine ⟨2892502945402925825695859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928335296935283883797239 2892502945402925825695859)
          ·
            refine ⟨4338754418104388738543789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892502945402925825695859 4338754418104388738543789)
            ·
              refine ⟨1627032906789145776953921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338754418104388738543789 1627032906789145776953921)
              ·
                refine ⟨1220274680091859332715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1627032906789145776953921 1220274680091859332715441)
                ·
                  refine ⟨915206010068894499536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220274680091859332715441 915206010068894499536581)
                  ·
                    refine ⟨171601126887917718663109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915206010068894499536581 171601126887917718663109)
                    ·
                      refine ⟨32175211291484572249333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 171601126887917718663109 32175211291484572249333)
                      ·
                        rfl

theorem cell23_62661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_62661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62661 prefixEnd_62661 := by exact prefixLift 62661
  have htrace : WordTrace (prefixWord ++ tailWord_62661) baseStart_62661 baseEnd_62661 := by
    simpa [prefixWord, tailWord_62661, baseEnd_62661] using wordTrace_append hprefix tailTrace_62661
  have hstable : (prefixWord ++ tailWord_62661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62661).length < 2 ^ (prefixWord ++ tailWord_62661).sum := by decide
  have hdescent : baseEnd_62661 < baseStart_62661 := by decide
  rcases family_descends (prefixWord ++ tailWord_62661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62711 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_62711 : Nat := 118140960795 + 62711 * 2 ^ 59
def prefixEnd_62711 : Nat := 4983230072969 + 3 ^ 40 * 62711 * 2
def baseEnd_62711 : Nat := 32200885324209376624103

theorem tailTrace_62711 : CollatzResearch.WordTrace tailWord_62711 prefixEnd_62711 32200885324209376624103 := by
  unfold tailWord_62711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287258075816232031227987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1524838717210821354151991 2287258075816232031227987)
  ·
    refine ⟨3430887113724348046841981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287258075816232031227987 3430887113724348046841981)
    ·
      refine ⟨1286582667646630517565743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3430887113724348046841981 1286582667646630517565743)
      ·
        refine ⟨1929874001469945776348615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286582667646630517565743 1929874001469945776348615)
        ·
          refine ⟨2894811002204918664522923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929874001469945776348615 2894811002204918664522923)
          ·
            refine ⟨4342216503307377996784385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894811002204918664522923 4342216503307377996784385)
            ·
              refine ⟨3256662377480533497588289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342216503307377996784385 3256662377480533497588289)
              ·
                refine ⟨2442496783110400123191217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3256662377480533497588289 2442496783110400123191217)
                ·
                  refine ⟨1831872587332800092393413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2442496783110400123191217 1831872587332800092393413)
                  ·
                    refine ⟨343476110124900017323765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831872587332800092393413 343476110124900017323765)
                    ·
                      refine ⟨32200885324209376624103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 343476110124900017323765 32200885324209376624103)
                      ·
                        rfl

theorem cell23_62711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_62711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62711 prefixEnd_62711 := by exact prefixLift 62711
  have htrace : WordTrace (prefixWord ++ tailWord_62711) baseStart_62711 baseEnd_62711 := by
    simpa [prefixWord, tailWord_62711, baseEnd_62711] using wordTrace_append hprefix tailTrace_62711
  have hstable : (prefixWord ++ tailWord_62711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62711).length < 2 ^ (prefixWord ++ tailWord_62711).sum := by decide
  have hdescent : baseEnd_62711 < baseStart_62711 := by decide
  rcases family_descends (prefixWord ++ tailWord_62711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62748 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_62748 : Nat := 118140960795 + 62748 * 2 ^ 59
def prefixEnd_62748 : Nat := 4983230072969 + 3 ^ 40 * 62748 * 2
def baseEnd_62748 : Nat := 10739961369475243953811

theorem tailTrace_62748 : CollatzResearch.WordTrace tailWord_62748 prefixEnd_62748 10739961369475243953811 := by
  unfold tailWord_62748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1144303788341093675162449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1525738384454791566883265 1144303788341093675162449)
  ·
    refine ⟨858227841255820256371837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1144303788341093675162449 858227841255820256371837)
    ·
      refine ⟨321835440470932596139439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 858227841255820256371837 321835440470932596139439)
      ·
        refine ⟨482753160706398894209159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321835440470932596139439 482753160706398894209159)
        ·
          refine ⟨724129741059598341313739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482753160706398894209159 724129741059598341313739)
          ·
            refine ⟨1086194611589397511970609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724129741059598341313739 1086194611589397511970609)
            ·
              refine ⟨814645958692048133977957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086194611589397511970609 814645958692048133977957)
              ·
                refine ⟨152746117254759025120867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814645958692048133977957 152746117254759025120867)
                ·
                  refine ⟨229119175882138537681301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152746117254759025120867 229119175882138537681301)
                  ·
                    refine ⟨10739961369475243953811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229119175882138537681301 10739961369475243953811)
                    ·
                      rfl

theorem cell23_62748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_62748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62748 prefixEnd_62748 := by exact prefixLift 62748
  have htrace : WordTrace (prefixWord ++ tailWord_62748) baseStart_62748 baseEnd_62748 := by
    simpa [prefixWord, tailWord_62748, baseEnd_62748] using wordTrace_append hprefix tailTrace_62748
  have hstable : (prefixWord ++ tailWord_62748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62748).length < 2 ^ (prefixWord ++ tailWord_62748).sum := by decide
  have hdescent : baseEnd_62748 < baseStart_62748 := by decide
  rcases family_descends (prefixWord ++ tailWord_62748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62755 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 4]
def baseStart_62755 : Nat := 118140960795 + 62755 * 2 ^ 59
def prefixEnd_62755 : Nat := 4983230072969 + 3 ^ 40 * 62755 * 2
def baseEnd_62755 : Nat := 32223478473007204473901

theorem tailTrace_62755 : CollatzResearch.WordTrace tailWord_62755 prefixEnd_62755 32223478473007204473901 := by
  unfold tailWord_62755
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288862887656827545829719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1525908591771218363886479 2288862887656827545829719)
  ·
    refine ⟨3433294331485241318744579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288862887656827545829719 3433294331485241318744579)
    ·
      refine ⟨5149941497227861978116869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433294331485241318744579 5149941497227861978116869)
      ·
        refine ⟨965614030730224120896913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5149941497227861978116869 965614030730224120896913)
        ·
          refine ⟨724210523047668090672685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965614030730224120896913 724210523047668090672685)
          ·
            refine ⟨271578946142875534002257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724210523047668090672685 271578946142875534002257)
            ·
              refine ⟨203684209607156650501693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271578946142875534002257 203684209607156650501693)
              ·
                refine ⟨76381578602683743938135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203684209607156650501693 76381578602683743938135)
                ·
                  refine ⟨114572367904025615907203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76381578602683743938135 114572367904025615907203)
                  ·
                    refine ⟨171858551856038423860805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114572367904025615907203 171858551856038423860805)
                    ·
                      refine ⟨32223478473007204473901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 171858551856038423860805 32223478473007204473901)
                      ·
                        rfl

theorem cell23_62755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_62755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62755 prefixEnd_62755 := by exact prefixLift 62755
  have htrace : WordTrace (prefixWord ++ tailWord_62755) baseStart_62755 baseEnd_62755 := by
    simpa [prefixWord, tailWord_62755, baseEnd_62755] using wordTrace_append hprefix tailTrace_62755
  have hstable : (prefixWord ++ tailWord_62755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62755).length < 2 ^ (prefixWord ++ tailWord_62755).sum := by decide
  have hdescent : baseEnd_62755 < baseStart_62755 := by decide
  rcases family_descends (prefixWord ++ tailWord_62755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62778 : List Nat := [3, 1, 1, 1, 4, 1, 4, 8]
def baseStart_62778 : Nat := 118140960795 + 62778 * 2 ^ 59
def prefixEnd_62778 : Nat := 4983230072969 + 3 ^ 40 * 62778 * 2
def baseEnd_62778 : Nat := 1193899575113356092085

theorem tailTrace_62778 : CollatzResearch.WordTrace tailWord_62778 prefixEnd_62778 1193899575113356092085 := by
  unfold tailWord_62778
  simp only [CollatzResearch.WordTrace]
  refine ⟨572425441643375618479247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1526467844382334982611325 572425441643375618479247)
  ·
    refine ⟨858638162465063427718871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572425441643375618479247 858638162465063427718871)
    ·
      refine ⟨1287957243697595141578307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858638162465063427718871 1287957243697595141578307)
      ·
        refine ⟨1931935865546392712367461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287957243697595141578307 1931935865546392712367461)
        ·
          refine ⟨362237974789948633568899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1931935865546392712367461 362237974789948633568899)
          ·
            refine ⟨543356962184922950353349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362237974789948633568899 543356962184922950353349)
            ·
              refine ⟨101879430409673053191253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 543356962184922950353349 101879430409673053191253)
              ·
                refine ⟨1193899575113356092085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101879430409673053191253 1193899575113356092085)
                ·
                  rfl

theorem cell23_62778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_62778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62778 prefixEnd_62778 := by exact prefixLift 62778
  have htrace : WordTrace (prefixWord ++ tailWord_62778) baseStart_62778 baseEnd_62778 := by
    simpa [prefixWord, tailWord_62778, baseEnd_62778] using wordTrace_append hprefix tailTrace_62778
  have hstable : (prefixWord ++ tailWord_62778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62778).length < 2 ^ (prefixWord ++ tailWord_62778).sum := by decide
  have hdescent : baseEnd_62778 < baseStart_62778 := by decide
  rcases family_descends (prefixWord ++ tailWord_62778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62782 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_62782 : Nat := 118140960795 + 62782 * 2 ^ 59
def prefixEnd_62782 : Nat := 4983230072969 + 3 ^ 40 * 62782 * 2
def baseEnd_62782 : Nat := 10745780816892866278759

theorem tailTrace_62782 : CollatzResearch.WordTrace tailWord_62782 prefixEnd_62782 10745780816892866278759 := by
  unfold tailWord_62782
  simp only [CollatzResearch.WordTrace]
  refine ⟨286230957319876394632825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1526565105706007438041733 286230957319876394632825)
  ·
    refine ⟨214673217989907295974619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286230957319876394632825 214673217989907295974619)
    ·
      refine ⟨322009826984860943961929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214673217989907295974619 322009826984860943961929)
      ·
        refine ⟨241507370238645707971447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322009826984860943961929 241507370238645707971447)
        ·
          refine ⟨362261055357968561957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241507370238645707971447 362261055357968561957171)
          ·
            refine ⟨543391583036952842935757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362261055357968561957171 543391583036952842935757)
            ·
              refine ⟨203771843638857316100909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543391583036952842935757 203771843638857316100909)
              ·
                refine ⟨76414441364571493537841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203771843638857316100909 76414441364571493537841)
                ·
                  refine ⟨57310831023428620153381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76414441364571493537841 57310831023428620153381)
                  ·
                    refine ⟨10745780816892866278759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57310831023428620153381 10745780816892866278759)
                    ·
                      rfl

theorem cell23_62782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_62782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62782 prefixEnd_62782 := by exact prefixLift 62782
  have htrace : WordTrace (prefixWord ++ tailWord_62782) baseStart_62782 baseEnd_62782 := by
    simpa [prefixWord, tailWord_62782, baseEnd_62782] using wordTrace_append hprefix tailTrace_62782
  have hstable : (prefixWord ++ tailWord_62782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62782).length < 2 ^ (prefixWord ++ tailWord_62782).sum := by decide
  have hdescent : baseEnd_62782 < baseStart_62782 := by decide
  rcases family_descends (prefixWord ++ tailWord_62782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62785 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_62785 : Nat := 118140960795 + 62785 * 2 ^ 59
def prefixEnd_62785 : Nat := 4983230072969 + 3 ^ 40 * 62785 * 2
def baseEnd_62785 : Nat := 32238882892642087098763

theorem tailTrace_62785 : CollatzResearch.WordTrace tailWord_62785 prefixEnd_62785 32238882892642087098763 := by
  unfold tailWord_62785
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289957077548142669421809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1526638051698761779614539 2289957077548142669421809)
  ·
    refine ⟨1717467808161107002066357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2289957077548142669421809 1717467808161107002066357)
    ·
      refine ⟨161012607015103781443721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1717467808161107002066357 161012607015103781443721)
      ·
        refine ⟨120759455261327836082791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161012607015103781443721 120759455261327836082791)
        ·
          refine ⟨181139182891991754124187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120759455261327836082791 181139182891991754124187)
          ·
            refine ⟨271708774337987631186281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181139182891991754124187 271708774337987631186281)
            ·
              refine ⟨203781580753490723389711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271708774337987631186281 203781580753490723389711)
              ·
                refine ⟨305672371130236085084567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203781580753490723389711 305672371130236085084567)
                ·
                  refine ⟨458508556695354127626851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305672371130236085084567 458508556695354127626851)
                  ·
                    refine ⟨687762835043031191440277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458508556695354127626851 687762835043031191440277)
                    ·
                      refine ⟨32238882892642087098763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 687762835043031191440277 32238882892642087098763)
                      ·
                        rfl

theorem cell23_62785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_62785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62785 prefixEnd_62785 := by exact prefixLift 62785
  have htrace : WordTrace (prefixWord ++ tailWord_62785) baseStart_62785 baseEnd_62785 := by
    simpa [prefixWord, tailWord_62785, baseEnd_62785] using wordTrace_append hprefix tailTrace_62785
  have hstable : (prefixWord ++ tailWord_62785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62785).length < 2 ^ (prefixWord ++ tailWord_62785).sum := by decide
  have hdescent : baseEnd_62785 < baseStart_62785 := by decide
  rcases family_descends (prefixWord ++ tailWord_62785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62805 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_62805 : Nat := 118140960795 + 62805 * 2 ^ 59
def prefixEnd_62805 : Nat := 4983230072969 + 3 ^ 40 * 62805 * 2
def baseEnd_62805 : Nat := 32249152505732008848671

theorem tailTrace_62805 : CollatzResearch.WordTrace tailWord_62805 prefixEnd_62805 32249152505732008848671 := by
  unfold tailWord_62805
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290686537475686085149869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1527124358317124056766579 2290686537475686085149869)
  ·
    refine ⟨859007451553382281931201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2290686537475686085149869 859007451553382281931201)
    ·
      refine ⟨644255588665036711448401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 859007451553382281931201 644255588665036711448401)
      ·
        refine ⟨483191691498777533586301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644255588665036711448401 483191691498777533586301)
        ·
          refine ⟨181196884312041575094863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483191691498777533586301 181196884312041575094863)
          ·
            refine ⟨271795326468062362642295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181196884312041575094863 271795326468062362642295)
            ·
              refine ⟨407692989702093543963443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271795326468062362642295 407692989702093543963443)
              ·
                refine ⟨611539484553140315945165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407692989702093543963443 611539484553140315945165)
                ·
                  refine ⟨229327306707427618479437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611539484553140315945165 229327306707427618479437)
                  ·
                    refine ⟨85997740015285356929789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229327306707427618479437 85997740015285356929789)
                    ·
                      refine ⟨32249152505732008848671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 85997740015285356929789 32249152505732008848671)
                      ·
                        rfl

theorem cell23_62805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_62805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62805 prefixEnd_62805 := by exact prefixLift 62805
  have htrace : WordTrace (prefixWord ++ tailWord_62805) baseStart_62805 baseEnd_62805 := by
    simpa [prefixWord, tailWord_62805, baseEnd_62805] using wordTrace_append hprefix tailTrace_62805
  have hstable : (prefixWord ++ tailWord_62805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62805).length < 2 ^ (prefixWord ++ tailWord_62805).sum := by decide
  have hdescent : baseEnd_62805 < baseStart_62805 := by decide
  rcases family_descends (prefixWord ++ tailWord_62805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_62848 : Nat := 118140960795 + 62848 * 2 ^ 59
def prefixEnd_62848 : Nat := 4983230072969 + 3 ^ 40 * 62848 * 2
def baseEnd_62848 : Nat := 32271232173875340610973

theorem tailTrace_62848 : CollatzResearch.WordTrace tailWord_62848 prefixEnd_62848 32271232173875340610973 := by
  unfold tailWord_62848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146127438159952214482599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528169917546602952643465 1146127438159952214482599)
  ·
    refine ⟨1719191157239928321723899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146127438159952214482599 1719191157239928321723899)
    ·
      refine ⟨2578786735859892482585849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1719191157239928321723899 2578786735859892482585849)
      ·
        refine ⟨1934090051894919361939387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578786735859892482585849 1934090051894919361939387)
        ·
          refine ⟨2901135077842379042909081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934090051894919361939387 2901135077842379042909081)
          ·
            refine ⟨2175851308381784282181811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901135077842379042909081 2175851308381784282181811)
            ·
              refine ⟨3263776962572676423272717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175851308381784282181811 3263776962572676423272717)
              ·
                refine ⟨1223916360964753658727269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263776962572676423272717 1223916360964753658727269)
                ·
                  refine ⟨229484317680891311011363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1223916360964753658727269 229484317680891311011363)
                  ·
                    refine ⟨344226476521336966517045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229484317680891311011363 344226476521336966517045)
                    ·
                      refine ⟨32271232173875340610973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 344226476521336966517045 32271232173875340610973)
                      ·
                        rfl

theorem cell23_62848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_62848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62848 prefixEnd_62848 := by exact prefixLift 62848
  have htrace : WordTrace (prefixWord ++ tailWord_62848) baseStart_62848 baseEnd_62848 := by
    simpa [prefixWord, tailWord_62848, baseEnd_62848] using wordTrace_append hprefix tailTrace_62848
  have hstable : (prefixWord ++ tailWord_62848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62848).length < 2 ^ (prefixWord ++ tailWord_62848).sum := by decide
  have hdescent : baseEnd_62848 < baseStart_62848 := by decide
  rcases family_descends (prefixWord ++ tailWord_62848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62879 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 4, 2, 2]
def baseStart_62879 : Nat := 118140960795 + 62879 * 2 ^ 59
def prefixEnd_62879 : Nat := 4983230072969 + 3 ^ 40 * 62879 * 2
def baseEnd_62879 : Nat := 32287150074164719323331

theorem tailTrace_62879 : CollatzResearch.WordTrace tailWord_62879 prefixEnd_62879 32287150074164719323331 := by
  unfold tailWord_62879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293385539207596723343691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1528923692805064482229127 2293385539207596723343691)
  ·
    refine ⟨3440078308811395085015537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2293385539207596723343691 3440078308811395085015537)
    ·
      refine ⟨2580058731608546313761653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3440078308811395085015537 2580058731608546313761653)
      ·
        refine ⟨241880506088301216915155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2580058731608546313761653 241880506088301216915155)
        ·
          refine ⟨362820759132451825372733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241880506088301216915155 362820759132451825372733)
          ·
            refine ⟨136057784674669434514775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362820759132451825372733 136057784674669434514775)
            ·
              refine ⟨204086677012004151772163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136057784674669434514775 204086677012004151772163)
              ·
                refine ⟨306130015518006227658245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204086677012004151772163 306130015518006227658245)
                ·
                  refine ⟨57399377909626167685921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 306130015518006227658245 57399377909626167685921)
                  ·
                    refine ⟨43049533432219625764441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57399377909626167685921 43049533432219625764441)
                    ·
                      refine ⟨32287150074164719323331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43049533432219625764441 32287150074164719323331)
                      ·
                        rfl

theorem cell23_62879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_62879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62879 prefixEnd_62879 := by exact prefixLift 62879
  have htrace : WordTrace (prefixWord ++ tailWord_62879) baseStart_62879 baseEnd_62879 := by
    simpa [prefixWord, tailWord_62879, baseEnd_62879] using wordTrace_append hprefix tailTrace_62879
  have hstable : (prefixWord ++ tailWord_62879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62879).length < 2 ^ (prefixWord ++ tailWord_62879).sum := by decide
  have hdescent : baseEnd_62879 < baseStart_62879 := by decide
  rcases family_descends (prefixWord ++ tailWord_62879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62928 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_62928 : Nat := 118140960795 + 62928 * 2 ^ 59
def prefixEnd_62928 : Nat := 4983230072969 + 3 ^ 40 * 62928 * 2
def baseEnd_62928 : Nat := 10770770208745009203535

theorem tailTrace_62928 : CollatzResearch.WordTrace tailWord_62928 prefixEnd_62928 10770770208745009203535 := by
  unfold tailWord_62928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147586358015039045938719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1530115144020052061251625 1147586358015039045938719)
  ·
    refine ⟨1721379537022558568908079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147586358015039045938719 1721379537022558568908079)
    ·
      refine ⟨2582069305533837853362119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721379537022558568908079 2582069305533837853362119)
      ·
        refine ⟨3873103958300756780043179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582069305533837853362119 3873103958300756780043179)
        ·
          refine ⟨5809655937451135170064769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873103958300756780043179 5809655937451135170064769)
          ·
            refine ⟨4357241953088351377548577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5809655937451135170064769 4357241953088351377548577)
            ·
              refine ⟨3267931464816263533161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357241953088351377548577 3267931464816263533161433)
              ·
                refine ⟨2450948598612197649871075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267931464816263533161433 2450948598612197649871075)
                ·
                  refine ⟨3676422897918296474806613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450948598612197649871075 3676422897918296474806613)
                  ·
                    refine ⟨10770770208745009203535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 3676422897918296474806613 10770770208745009203535)
                    ·
                      rfl

theorem cell23_62928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_62928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62928 prefixEnd_62928 := by exact prefixLift 62928
  have htrace : WordTrace (prefixWord ++ tailWord_62928) baseStart_62928 baseEnd_62928 := by
    simpa [prefixWord, tailWord_62928, baseEnd_62928] using wordTrace_append hprefix tailTrace_62928
  have hstable : (prefixWord ++ tailWord_62928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62928).length < 2 ^ (prefixWord ++ tailWord_62928).sum := by decide
  have hdescent : baseEnd_62928 < baseStart_62928 := by decide
  rcases family_descends (prefixWord ++ tailWord_62928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62952 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_62952 : Nat := 118140960795 + 62952 * 2 ^ 59
def prefixEnd_62952 : Nat := 4983230072969 + 3 ^ 40 * 62952 * 2
def baseEnd_62952 : Nat := 32324634161942933710495

theorem tailTrace_62952 : CollatzResearch.WordTrace tailWord_62952 prefixEnd_62952 32324634161942933710495 := by
  unfold tailWord_62952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148024033971565095375555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1530698711962086793834073 1148024033971565095375555)
  ·
    refine ⟨1722036050957347643063333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148024033971565095375555 1722036050957347643063333)
    ·
      refine ⟨322881759554502683074375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1722036050957347643063333 322881759554502683074375)
      ·
        refine ⟨484322639331754024611563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322881759554502683074375 484322639331754024611563)
        ·
          refine ⟨726483958997631036917345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484322639331754024611563 726483958997631036917345)
          ·
            refine ⟨544862969248223277688009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726483958997631036917345 544862969248223277688009)
            ·
              refine ⟨408647226936167458266007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544862969248223277688009 408647226936167458266007)
              ·
                refine ⟨612970840404251187399011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408647226936167458266007 612970840404251187399011)
                ·
                  refine ⟨919456260606376781098517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612970840404251187399011 919456260606376781098517)
                  ·
                    refine ⟨43099512215923911613993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 919456260606376781098517 43099512215923911613993)
                    ·
                      refine ⟨32324634161942933710495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43099512215923911613993 32324634161942933710495)
                      ·
                        rfl

theorem cell23_62952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_62952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62952 prefixEnd_62952 := by exact prefixLift 62952
  have htrace : WordTrace (prefixWord ++ tailWord_62952) baseStart_62952 baseEnd_62952 := by
    simpa [prefixWord, tailWord_62952, baseEnd_62952] using wordTrace_append hprefix tailTrace_62952
  have hstable : (prefixWord ++ tailWord_62952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62952).length < 2 ^ (prefixWord ++ tailWord_62952).sum := by decide
  have hdescent : baseEnd_62952 < baseStart_62952 := by decide
  rcases family_descends (prefixWord ++ tailWord_62952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62955 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3]
def baseStart_62955 : Nat := 118140960795 + 62955 * 2 ^ 59
def prefixEnd_62955 : Nat := 4983230072969 + 3 ^ 40 * 62955 * 2
def baseEnd_62955 : Nat := 32326174603906421972981

theorem tailTrace_62955 : CollatzResearch.WordTrace tailWord_62955 prefixEnd_62955 32326174603906421972981 := by
  unfold tailWord_62955
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296157486932261703110319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1530771657954841135406879 2296157486932261703110319)
  ·
    refine ⟨3444236230398392554665479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296157486932261703110319 3444236230398392554665479)
    ·
      refine ⟨5166354345597588831998219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3444236230398392554665479 5166354345597588831998219)
      ·
        refine ⟨7749531518396383247997329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166354345597588831998219 7749531518396383247997329)
        ·
          refine ⟨5812148638797287435997997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7749531518396383247997329 5812148638797287435997997)
          ·
            refine ⟨2179555739548982788499249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5812148638797287435997997 2179555739548982788499249)
            ·
              refine ⟨1634666804661737091374437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179555739548982788499249 1634666804661737091374437)
              ·
                refine ⟨306500025874075704632707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634666804661737091374437 306500025874075704632707)
                ·
                  refine ⟨459750038811113556949061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306500025874075704632707 459750038811113556949061)
                  ·
                    refine ⟨86203132277083791927949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459750038811113556949061 86203132277083791927949)
                    ·
                      refine ⟨32326174603906421972981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86203132277083791927949 32326174603906421972981)
                      ·
                        rfl

theorem cell23_62955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].length) (baseStart_62955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62955 prefixEnd_62955 := by exact prefixLift 62955
  have htrace : WordTrace (prefixWord ++ tailWord_62955) baseStart_62955 baseEnd_62955 := by
    simpa [prefixWord, tailWord_62955, baseEnd_62955] using wordTrace_append hprefix tailTrace_62955
  have hstable : (prefixWord ++ tailWord_62955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62955).length < 2 ^ (prefixWord ++ tailWord_62955).sum := by decide
  have hdescent : baseEnd_62955 < baseStart_62955 := by decide
  rcases family_descends (prefixWord ++ tailWord_62955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62972 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_62972 : Nat := 118140960795 + 62972 * 2 ^ 59
def prefixEnd_62972 : Nat := 4983230072969 + 3 ^ 40 * 62972 * 2
def baseEnd_62972 : Nat := 32334903775032855460403

theorem tailTrace_62972 : CollatzResearch.WordTrace tailWord_62972 prefixEnd_62972 32334903775032855460403 := by
  unfold tailWord_62972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148388763935336803239585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1531185018580449070986113 1148388763935336803239585)
  ·
    refine ⟨861291572951502602429689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148388763935336803239585 861291572951502602429689)
    ·
      refine ⟨645968679713626951822267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 861291572951502602429689 645968679713626951822267)
      ·
        refine ⟨968953019570440427733401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645968679713626951822267 968953019570440427733401)
        ·
          refine ⟨726714764677830320800051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968953019570440427733401 726714764677830320800051)
          ·
            refine ⟨1090072147016745481200077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726714764677830320800051 1090072147016745481200077)
            ·
              refine ⟨408777055131279555450029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090072147016745481200077 408777055131279555450029)
              ·
                refine ⟨153291395674229833293761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408777055131279555450029 153291395674229833293761)
                ·
                  refine ⟨114968546755672374970321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153291395674229833293761 114968546755672374970321)
                  ·
                    refine ⟨86226410066754281227741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114968546755672374970321 86226410066754281227741)
                    ·
                      refine ⟨32334903775032855460403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86226410066754281227741 32334903775032855460403)
                      ·
                        rfl

theorem cell23_62972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_62972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_62972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_62972 prefixEnd_62972 := by exact prefixLift 62972
  have htrace : WordTrace (prefixWord ++ tailWord_62972) baseStart_62972 baseEnd_62972 := by
    simpa [prefixWord, tailWord_62972, baseEnd_62972] using wordTrace_append hprefix tailTrace_62972
  have hstable : (prefixWord ++ tailWord_62972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62972).length < 2 ^ (prefixWord ++ tailWord_62972).sum := by decide
  have hdescent : baseEnd_62972 < baseStart_62972 := by decide
  rcases family_descends (prefixWord ++ tailWord_62972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63029 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_63029 : Nat := 118140960795 + 63029 * 2 ^ 59
def prefixEnd_63029 : Nat := 4983230072969 + 3 ^ 40 * 63029 * 2
def baseEnd_63029 : Nat := 32364172172339132447641

theorem tailTrace_63029 : CollatzResearch.WordTrace tailWord_63029 prefixEnd_63029 32364172172339132447641 := by
  unfold tailWord_63029
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298856488664172341304141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1532570992442781560869427 2298856488664172341304141)
  ·
    refine ⟨862071183249064627989053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2298856488664172341304141 862071183249064627989053)
    ·
      refine ⟨323276693718399235495895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862071183249064627989053 323276693718399235495895)
      ·
        refine ⟨484915040577598853243843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323276693718399235495895 484915040577598853243843)
        ·
          refine ⟨727372560866398279865765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484915040577598853243843 727372560866398279865765)
          ·
            refine ⟨136382355162449677474831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 727372560866398279865765 136382355162449677474831)
            ·
              refine ⟨204573532743674516212247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136382355162449677474831 204573532743674516212247)
              ·
                refine ⟨306860299115511774318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204573532743674516212247 306860299115511774318371)
                ·
                  refine ⟨460290448673267661477557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306860299115511774318371 460290448673267661477557)
                  ·
                    refine ⟨43152229563118843263521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 460290448673267661477557 43152229563118843263521)
                    ·
                      refine ⟨32364172172339132447641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43152229563118843263521 32364172172339132447641)
                      ·
                        rfl

theorem cell23_63029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_63029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63029 prefixEnd_63029 := by exact prefixLift 63029
  have htrace : WordTrace (prefixWord ++ tailWord_63029) baseStart_63029 baseEnd_63029 := by
    simpa [prefixWord, tailWord_63029, baseEnd_63029] using wordTrace_append hprefix tailTrace_63029
  have hstable : (prefixWord ++ tailWord_63029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63029).length < 2 ^ (prefixWord ++ tailWord_63029).sum := by decide
  have hdescent : baseEnd_63029 < baseStart_63029 := by decide
  rcases family_descends (prefixWord ++ tailWord_63029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63039 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 1, 5]
def baseStart_63039 : Nat := 118140960795 + 63039 * 2 ^ 59
def prefixEnd_63039 : Nat := 4983230072969 + 3 ^ 40 * 63039 * 2
def baseEnd_63039 : Nat := 10789768992961364440865

theorem tailTrace_63039 : CollatzResearch.WordTrace tailWord_63039 prefixEnd_63039 10789768992961364440865 := by
  unfold tailWord_63039
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299221218627944049168171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1532814145751962699445447 2299221218627944049168171)
  ·
    refine ⟨3448831827941916073752257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299221218627944049168171 3448831827941916073752257)
    ·
      refine ⟨2586623870956437055314193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448831827941916073752257 2586623870956437055314193)
      ·
        refine ⟨1939967903217327791485645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586623870956437055314193 1939967903217327791485645)
        ·
          refine ⟨727487963706497921807117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1939967903217327791485645 727487963706497921807117)
          ·
            refine ⟨272807986389936720677669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727487963706497921807117 272807986389936720677669)
            ·
              refine ⟨51151497448113135127063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272807986389936720677669 51151497448113135127063)
              ·
                refine ⟨76727246172169702690595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51151497448113135127063 76727246172169702690595)
                ·
                  refine ⟨115090869258254554035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76727246172169702690595 115090869258254554035893)
                  ·
                    refine ⟨10789768992961364440865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115090869258254554035893 10789768992961364440865)
                    ·
                      rfl

theorem cell23_63039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_63039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63039 prefixEnd_63039 := by exact prefixLift 63039
  have htrace : WordTrace (prefixWord ++ tailWord_63039) baseStart_63039 baseEnd_63039 := by
    simpa [prefixWord, tailWord_63039, baseEnd_63039] using wordTrace_append hprefix tailTrace_63039
  have hstable : (prefixWord ++ tailWord_63039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63039).length < 2 ^ (prefixWord ++ tailWord_63039).sum := by decide
  have hdescent : baseEnd_63039 < baseStart_63039 := by decide
  rcases family_descends (prefixWord ++ tailWord_63039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63053 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_63053 : Nat := 118140960795 + 63053 * 2 ^ 59
def prefixEnd_63053 : Nat := 4983230072969 + 3 ^ 40 * 63053 * 2
def baseEnd_63053 : Nat := 32376495708047038547531

theorem tailTrace_63053 : CollatzResearch.WordTrace tailWord_63053 prefixEnd_63053 32376495708047038547531 := by
  unfold tailWord_63053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299731840577224440177813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1533154560384816293451875 2299731840577224440177813)
  ·
    refine ⟨107799930027057395633335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2299731840577224440177813 107799930027057395633335)
    ·
      refine ⟨161699895040586093450003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107799930027057395633335 161699895040586093450003)
      ·
        refine ⟨242549842560879140175005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161699895040586093450003 242549842560879140175005)
        ·
          refine ⟨90956190960329677565627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242549842560879140175005 90956190960329677565627)
          ·
            refine ⟨136434286440494516348441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90956190960329677565627 136434286440494516348441)
            ·
              refine ⟨102325714830370887261331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136434286440494516348441 102325714830370887261331)
              ·
                refine ⟨153488572245556330891997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102325714830370887261331 153488572245556330891997)
                ·
                  refine ⟨57558214592083624084499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153488572245556330891997 57558214592083624084499)
                  ·
                    refine ⟨86337321888125436126749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57558214592083624084499 86337321888125436126749)
                    ·
                      refine ⟨32376495708047038547531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86337321888125436126749 32376495708047038547531)
                      ·
                        rfl

theorem cell23_63053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_63053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63053 prefixEnd_63053 := by exact prefixLift 63053
  have htrace : WordTrace (prefixWord ++ tailWord_63053) baseStart_63053 baseEnd_63053 := by
    simpa [prefixWord, tailWord_63053, baseEnd_63053] using wordTrace_append hprefix tailTrace_63053
  have hstable : (prefixWord ++ tailWord_63053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63053).length < 2 ^ (prefixWord ++ tailWord_63053).sum := by decide
  have hdescent : baseEnd_63053 < baseStart_63053 := by decide
  rcases family_descends (prefixWord ++ tailWord_63053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63055 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_63055 : Nat := 118140960795 + 63055 * 2 ^ 59
def prefixEnd_63055 : Nat := 4983230072969 + 3 ^ 40 * 63055 * 2
def baseEnd_63055 : Nat := 32377522669356030722521

theorem tailTrace_63055 : CollatzResearch.WordTrace tailWord_63055 prefixEnd_63055 32377522669356030722521 := by
  unfold tailWord_63055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299804786569978781750619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1533203191046652521167079 2299804786569978781750619)
  ·
    refine ⟨3449707179854968172625929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299804786569978781750619 3449707179854968172625929)
    ·
      refine ⟨2587280384891226129469447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3449707179854968172625929 2587280384891226129469447)
      ·
        refine ⟨3880920577336839194204171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587280384891226129469447 3880920577336839194204171)
        ·
          refine ⟨5821380866005258791306257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880920577336839194204171 5821380866005258791306257)
          ·
            refine ⟨4366035649503944093479693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821380866005258791306257 4366035649503944093479693)
            ·
              refine ⟨1637263368563979035054885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4366035649503944093479693 1637263368563979035054885)
              ·
                refine ⟨306986881605746069072791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1637263368563979035054885 306986881605746069072791)
                ·
                  refine ⟨460480322408619103609187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306986881605746069072791 460480322408619103609187)
                  ·
                    refine ⟨690720483612928655413781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460480322408619103609187 690720483612928655413781)
                    ·
                      refine ⟨32377522669356030722521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 690720483612928655413781 32377522669356030722521)
                      ·
                        rfl

theorem cell23_63055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_63055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63055 prefixEnd_63055 := by exact prefixLift 63055
  have htrace : WordTrace (prefixWord ++ tailWord_63055) baseStart_63055 baseEnd_63055 := by
    simpa [prefixWord, tailWord_63055, baseEnd_63055] using wordTrace_append hprefix tailTrace_63055
  have hstable : (prefixWord ++ tailWord_63055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63055).length < 2 ^ (prefixWord ++ tailWord_63055).sum := by decide
  have hdescent : baseEnd_63055 < baseStart_63055 := by decide
  rcases family_descends (prefixWord ++ tailWord_63055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63076 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_63076 : Nat := 118140960795 + 63076 * 2 ^ 59
def prefixEnd_63076 : Nat := 4983230072969 + 3 ^ 40 * 63076 * 2
def baseEnd_63076 : Nat := 32388305763100448559925

theorem tailTrace_63076 : CollatzResearch.WordTrace tailWord_63076 prefixEnd_63076 32388305763100448559925 := by
  unfold tailWord_63076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150285359746949684132541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1533713812995932912176721 1150285359746949684132541)
  ·
    refine ⟨431357009905106131549703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1150285359746949684132541 431357009905106131549703)
    ·
      refine ⟨647035514857659197324555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431357009905106131549703 647035514857659197324555)
      ·
        refine ⟨970553272286488795986833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647035514857659197324555 970553272286488795986833)
        ·
          refine ⟨727914954214866596990125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970553272286488795986833 727914954214866596990125)
          ·
            refine ⟨272968107830574973871297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727914954214866596990125 272968107830574973871297)
            ·
              refine ⟨204726080872931230403473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272968107830574973871297 204726080872931230403473)
              ·
                refine ⟨153544560654698422802605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204726080872931230403473 153544560654698422802605)
                ·
                  refine ⟨57579210245511908550977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153544560654698422802605 57579210245511908550977)
                  ·
                    refine ⟨43184407684133931413233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57579210245511908550977 43184407684133931413233)
                    ·
                      refine ⟨32388305763100448559925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43184407684133931413233 32388305763100448559925)
                      ·
                        rfl

theorem cell23_63076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_63076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63076 prefixEnd_63076 := by exact prefixLift 63076
  have htrace : WordTrace (prefixWord ++ tailWord_63076) baseStart_63076 baseEnd_63076 := by
    simpa [prefixWord, tailWord_63076, baseEnd_63076] using wordTrace_append hprefix tailTrace_63076
  have hstable : (prefixWord ++ tailWord_63076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63076).length < 2 ^ (prefixWord ++ tailWord_63076).sum := by decide
  have hdescent : baseEnd_63076 < baseStart_63076 := by decide
  rcases family_descends (prefixWord ++ tailWord_63076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63079 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_63079 : Nat := 118140960795 + 63079 * 2 ^ 59
def prefixEnd_63079 : Nat := 4983230072969 + 3 ^ 40 * 63079 * 2
def baseEnd_63079 : Nat := 32389846205063936822411

theorem tailTrace_63079 : CollatzResearch.WordTrace tailWord_63079 prefixEnd_63079 32389846205063936822411 := by
  unfold tailWord_63079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300680138483030880624291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1533786758988687253749527 2300680138483030880624291)
  ·
    refine ⟨3451020207724546320936437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300680138483030880624291 3451020207724546320936437)
    ·
      refine ⟨323533144474176217587791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3451020207724546320936437 323533144474176217587791)
      ·
        refine ⟨485299716711264326381687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323533144474176217587791 485299716711264326381687)
        ·
          refine ⟨727949575066896489572531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485299716711264326381687 727949575066896489572531)
          ·
            refine ⟨1091924362600344734358797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727949575066896489572531 1091924362600344734358797)
            ·
              refine ⟨409471635975129275384549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091924362600344734358797 409471635975129275384549)
              ·
                refine ⟨76775931745336739134603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409471635975129275384549 76775931745336739134603)
                ·
                  refine ⟨115163897618005108701905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76775931745336739134603 115163897618005108701905)
                  ·
                    refine ⟨86372923213503831526429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115163897618005108701905 86372923213503831526429)
                    ·
                      refine ⟨32389846205063936822411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86372923213503831526429 32389846205063936822411)
                      ·
                        rfl

theorem cell23_63079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_63079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63079 prefixEnd_63079 := by exact prefixLift 63079
  have htrace : WordTrace (prefixWord ++ tailWord_63079) baseStart_63079 baseEnd_63079 := by
    simpa [prefixWord, tailWord_63079, baseEnd_63079] using wordTrace_append hprefix tailTrace_63079
  have hstable : (prefixWord ++ tailWord_63079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63079).length < 2 ^ (prefixWord ++ tailWord_63079).sum := by decide
  have hdescent : baseEnd_63079 < baseStart_63079 := by decide
  rcases family_descends (prefixWord ++ tailWord_63079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63082 : List Nat := [3, 1, 3, 2, 1, 3, 1, 9]
def baseStart_63082 : Nat := 118140960795 + 63082 * 2 ^ 59
def prefixEnd_63082 : Nat := 4983230072969 + 3 ^ 40 * 63082 * 2
def baseEnd_63082 : Nat := 1199680986926941669811

theorem tailTrace_63082 : CollatzResearch.WordTrace tailWord_63082 prefixEnd_63082 1199680986926941669811 := by
  unfold tailWord_63082
  simp only [CollatzResearch.WordTrace]
  refine ⟨575197389368040598245875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1533859704981441595322333 575197389368040598245875)
  ·
    refine ⟨862796084052060897368813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575197389368040598245875 862796084052060897368813)
    ·
      refine ⟨323548531519522836513305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862796084052060897368813 323548531519522836513305)
      ·
        refine ⟨242661398639642127384979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323548531519522836513305 242661398639642127384979)
        ·
          refine ⟨363992097959463191077469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242661398639642127384979 363992097959463191077469)
          ·
            refine ⟨136497036734798696654051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363992097959463191077469 136497036734798696654051)
            ·
              refine ⟨204745555102198044981077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136497036734798696654051 204745555102198044981077)
              ·
                refine ⟨1199680986926941669811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 204745555102198044981077 1199680986926941669811)
                ·
                  rfl

theorem cell23_63082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_63082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63082 prefixEnd_63082 := by exact prefixLift 63082
  have htrace : WordTrace (prefixWord ++ tailWord_63082) baseStart_63082 baseEnd_63082 := by
    simpa [prefixWord, tailWord_63082, baseEnd_63082] using wordTrace_append hprefix tailTrace_63082
  have hstable : (prefixWord ++ tailWord_63082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63082).length < 2 ^ (prefixWord ++ tailWord_63082).sum := by decide
  have hdescent : baseEnd_63082 < baseStart_63082 := by decide
  rcases family_descends (prefixWord ++ tailWord_63082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63095 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 9]
def baseStart_63095 : Nat := 118140960795 + 63095 * 2 ^ 59
def prefixEnd_63095 : Nat := 4983230072969 + 3 ^ 40 * 63095 * 2
def baseEnd_63095 : Nat := 10799353965178624740779

theorem tailTrace_63095 : CollatzResearch.WordTrace tailWord_63095 prefixEnd_63095 10799353965178624740779 := by
  unfold tailWord_63095
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301263706425065613206739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1534175804283377075471159 2301263706425065613206739)
  ·
    refine ⟨3451895559637598419810109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2301263706425065613206739 3451895559637598419810109)
    ·
      refine ⟨1294460834864099407428791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3451895559637598419810109 1294460834864099407428791)
      ·
        refine ⟨1941691252296149111143187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294460834864099407428791 1941691252296149111143187)
        ·
          refine ⟨2912536878444223666714781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941691252296149111143187 2912536878444223666714781)
          ·
            refine ⟨1092201329416583875018043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2912536878444223666714781 1092201329416583875018043)
            ·
              refine ⟨1638301994124875812527065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092201329416583875018043 1638301994124875812527065)
              ·
                refine ⟨1228726495593656859395299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638301994124875812527065 1228726495593656859395299)
                ·
                  refine ⟨1843089743390485289092949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228726495593656859395299 1843089743390485289092949)
                  ·
                    refine ⟨10799353965178624740779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1843089743390485289092949 10799353965178624740779)
                    ·
                      rfl

theorem cell23_63095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_63095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63095 prefixEnd_63095 := by exact prefixLift 63095
  have htrace : WordTrace (prefixWord ++ tailWord_63095) baseStart_63095 baseEnd_63095 := by
    simpa [prefixWord, tailWord_63095, baseEnd_63095] using wordTrace_append hprefix tailTrace_63095
  have hstable : (prefixWord ++ tailWord_63095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63095).length < 2 ^ (prefixWord ++ tailWord_63095).sum := by decide
  have hdescent : baseEnd_63095 < baseStart_63095 := by decide
  rcases family_descends (prefixWord ++ tailWord_63095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63109 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_63109 : Nat := 118140960795 + 63109 * 2 ^ 59
def prefixEnd_63109 : Nat := 4983230072969 + 3 ^ 40 * 63109 * 2
def baseEnd_63109 : Nat := 32405250624698819447273

theorem tailTrace_63109 : CollatzResearch.WordTrace tailWord_63109 prefixEnd_63109 32405250624698819447273 := by
  unfold tailWord_63109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301774328374346004216381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1534516218916230669477587 2301774328374346004216381)
  ·
    refine ⟨863165373140379751581143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2301774328374346004216381 863165373140379751581143)
    ·
      refine ⟨1294748059710569627371715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863165373140379751581143 1294748059710569627371715)
      ·
        refine ⟨1942122089565854441057573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294748059710569627371715 1942122089565854441057573)
        ·
          refine ⟨364147891793597707698295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1942122089565854441057573 364147891793597707698295)
          ·
            refine ⟨546221837690396561547443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364147891793597707698295 546221837690396561547443)
            ·
              refine ⟨819332756535594842321165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546221837690396561547443 819332756535594842321165)
              ·
                refine ⟨307249783700848065870437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819332756535594842321165 307249783700848065870437)
                ·
                  refine ⟨57609334443909012350707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 307249783700848065870437 57609334443909012350707)
                  ·
                    refine ⟨86414001665863518526061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57609334443909012350707 86414001665863518526061)
                    ·
                      refine ⟨32405250624698819447273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86414001665863518526061 32405250624698819447273)
                      ·
                        rfl

theorem cell23_63109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_63109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63109 prefixEnd_63109 := by exact prefixLift 63109
  have htrace : WordTrace (prefixWord ++ tailWord_63109) baseStart_63109 baseEnd_63109 := by
    simpa [prefixWord, tailWord_63109, baseEnd_63109] using wordTrace_append hprefix tailTrace_63109
  have hstable : (prefixWord ++ tailWord_63109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63109).length < 2 ^ (prefixWord ++ tailWord_63109).sum := by decide
  have hdescent : baseEnd_63109 < baseStart_63109 := by decide
  rcases family_descends (prefixWord ++ tailWord_63109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63136 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2]
def baseStart_63136 : Nat := 118140960795 + 63136 * 2 ^ 59
def prefixEnd_63136 : Nat := 4983230072969 + 3 ^ 40 * 63136 * 2
def baseEnd_63136 : Nat := 32419114602370213809649

theorem tailTrace_63136 : CollatzResearch.WordTrace tailWord_63136 prefixEnd_63136 32419114602370213809649 := by
  unfold tailWord_63136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151379549638264807724631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1535172732851019743632841 1151379549638264807724631)
  ·
    refine ⟨1727069324457397211586947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151379549638264807724631 1727069324457397211586947)
    ·
      refine ⟨2590603986686095817380421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727069324457397211586947 2590603986686095817380421)
      ·
        refine ⟨485738247503642965758829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2590603986686095817380421 485738247503642965758829)
        ·
          refine ⟨182151842813866112159561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 485738247503642965758829 182151842813866112159561)
          ·
            refine ⟨136613882110399584119671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182151842813866112159561 136613882110399584119671)
            ·
              refine ⟨204920823165599376179507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136613882110399584119671 204920823165599376179507)
              ·
                refine ⟨307381234748399064269261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204920823165599376179507 307381234748399064269261)
                ·
                  refine ⟨115267963030649649100973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307381234748399064269261 115267963030649649100973)
                  ·
                    refine ⟨43225486136493618412865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115267963030649649100973 43225486136493618412865)
                    ·
                      refine ⟨32419114602370213809649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43225486136493618412865 32419114602370213809649)
                      ·
                        rfl

theorem cell23_63136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_63136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63136 prefixEnd_63136 := by exact prefixLift 63136
  have htrace : WordTrace (prefixWord ++ tailWord_63136) baseStart_63136 baseEnd_63136 := by
    simpa [prefixWord, tailWord_63136, baseEnd_63136] using wordTrace_append hprefix tailTrace_63136
  have hstable : (prefixWord ++ tailWord_63136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63136).length < 2 ^ (prefixWord ++ tailWord_63136).sum := by decide
  have hdescent : baseEnd_63136 < baseStart_63136 := by decide
  rcases family_descends (prefixWord ++ tailWord_63136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63152 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_63152 : Nat := 118140960795 + 63152 * 2 ^ 59
def prefixEnd_63152 : Nat := 4983230072969 + 3 ^ 40 * 63152 * 2
def baseEnd_63152 : Nat := 32427330292842151209575

theorem tailTrace_63152 : CollatzResearch.WordTrace tailWord_63152 prefixEnd_63152 32427330292842151209575 := by
  unfold tailWord_63152
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151671333609282174015855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1535561778145709565354473 1151671333609282174015855)
  ·
    refine ⟨1727507000413923261023783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151671333609282174015855 1727507000413923261023783)
    ·
      refine ⟨2591260500620884891535675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727507000413923261023783 2591260500620884891535675)
      ·
        refine ⟨3886890750931327337303513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2591260500620884891535675 3886890750931327337303513)
        ·
          refine ⟨2915168063198495502977635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886890750931327337303513 2915168063198495502977635)
          ·
            refine ⟨4372752094797743254466453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915168063198495502977635 4372752094797743254466453)
            ·
              refine ⟨204972754443644215053115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4372752094797743254466453 204972754443644215053115)
              ·
                refine ⟨307459131665466322579673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204972754443644215053115 307459131665466322579673)
                ·
                  refine ⟨230594348749099741934755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307459131665466322579673 230594348749099741934755)
                  ·
                    refine ⟨345891523123649612902133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230594348749099741934755 345891523123649612902133)
                    ·
                      refine ⟨32427330292842151209575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 345891523123649612902133 32427330292842151209575)
                      ·
                        rfl

theorem cell23_63152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_63152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63152 prefixEnd_63152 := by exact prefixLift 63152
  have htrace : WordTrace (prefixWord ++ tailWord_63152) baseStart_63152 baseEnd_63152 := by
    simpa [prefixWord, tailWord_63152, baseEnd_63152] using wordTrace_append hprefix tailTrace_63152
  have hstable : (prefixWord ++ tailWord_63152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63152).length < 2 ^ (prefixWord ++ tailWord_63152).sum := by decide
  have hdescent : baseEnd_63152 < baseStart_63152 := by decide
  rcases family_descends (prefixWord ++ tailWord_63152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63212 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_63212 : Nat := 118140960795 + 63212 * 2 ^ 59
def prefixEnd_63212 : Nat := 4983230072969 + 3 ^ 40 * 63212 * 2
def baseEnd_63212 : Nat := 32458139132111916459299

theorem tailTrace_63212 : CollatzResearch.WordTrace tailWord_63212 prefixEnd_63212 32458139132111916459299 := by
  unfold tailWord_63212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1152765523500597297607945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1537020698000796396810593 1152765523500597297607945)
  ·
    refine ⟨864574142625447973205959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1152765523500597297607945 864574142625447973205959)
    ·
      refine ⟨1296861213938171959808939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864574142625447973205959 1296861213938171959808939)
      ·
        refine ⟨1945291820907257939713409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296861213938171959808939 1945291820907257939713409)
        ·
          refine ⟨1458968865680443454785057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945291820907257939713409 1458968865680443454785057)
          ·
            refine ⟨1094226649260332591088793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1458968865680443454785057 1094226649260332591088793)
            ·
              refine ⟨820669986945249443316595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094226649260332591088793 820669986945249443316595)
              ·
                refine ⟨1231004980417874164974893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820669986945249443316595 1231004980417874164974893)
                ·
                  refine ⟨461626867656702811865585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1231004980417874164974893 461626867656702811865585)
                  ·
                    refine ⟨346220150742527108899189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 461626867656702811865585 346220150742527108899189)
                    ·
                      refine ⟨32458139132111916459299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 346220150742527108899189 32458139132111916459299)
                      ·
                        rfl

theorem cell23_63212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_63212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63212 prefixEnd_63212 := by exact prefixLift 63212
  have htrace : WordTrace (prefixWord ++ tailWord_63212) baseStart_63212 baseEnd_63212 := by
    simpa [prefixWord, tailWord_63212, baseEnd_63212] using wordTrace_append hprefix tailTrace_63212
  have hstable : (prefixWord ++ tailWord_63212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63212).length < 2 ^ (prefixWord ++ tailWord_63212).sum := by decide
  have hdescent : baseEnd_63212 < baseStart_63212 := by decide
  rcases family_descends (prefixWord ++ tailWord_63212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63276 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_63276 : Nat := 118140960795 + 63276 * 2 ^ 59
def prefixEnd_63276 : Nat := 4983230072969 + 3 ^ 40 * 63276 * 2
def baseEnd_63276 : Nat := 32491001893999666059005

theorem tailTrace_63276 : CollatzResearch.WordTrace tailWord_63276 prefixEnd_63276 32491001893999666059005 := by
  unfold tailWord_63276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153932659384666762772841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1538576879179555683697121 1153932659384666762772841)
  ·
    refine ⟨865449494538500072079631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1153932659384666762772841 865449494538500072079631)
    ·
      refine ⟨1298174241807750108119447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865449494538500072079631 1298174241807750108119447)
      ·
        refine ⟨1947261362711625162179171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298174241807750108119447 1947261362711625162179171)
        ·
          refine ⟨2920892044067437743268757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947261362711625162179171 2920892044067437743268757)
          ·
            refine ⟨136916814565661144215723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2920892044067437743268757 136916814565661144215723)
            ·
              refine ⟨205375221848491716323585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136916814565661144215723 205375221848491716323585)
              ·
                refine ⟨154031416386368787242689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205375221848491716323585 154031416386368787242689)
                ·
                  refine ⟨115523562289776590432017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154031416386368787242689 115523562289776590432017)
                  ·
                    refine ⟨86642671717332442824013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115523562289776590432017 86642671717332442824013)
                    ·
                      refine ⟨32491001893999666059005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86642671717332442824013 32491001893999666059005)
                      ·
                        rfl

theorem cell23_63276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_63276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63276 prefixEnd_63276 := by exact prefixLift 63276
  have htrace : WordTrace (prefixWord ++ tailWord_63276) baseStart_63276 baseEnd_63276 := by
    simpa [prefixWord, tailWord_63276, baseEnd_63276] using wordTrace_append hprefix tailTrace_63276
  have hstable : (prefixWord ++ tailWord_63276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63276).length < 2 ^ (prefixWord ++ tailWord_63276).sum := by decide
  have hdescent : baseEnd_63276 < baseStart_63276 := by decide
  rcases family_descends (prefixWord ++ tailWord_63276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63283 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 3, 4]
def baseStart_63283 : Nat := 118140960795 + 63283 * 2 ^ 59
def prefixEnd_63283 : Nat := 4983230072969 + 3 ^ 40 * 63283 * 2
def baseEnd_63283 : Nat := 10831532086193712890491

theorem tailTrace_63283 : CollatzResearch.WordTrace tailWord_63283 prefixEnd_63283 10831532086193712890491 := by
  unfold tailWord_63283
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308120629743973721050503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1538747086495982480700335 2308120629743973721050503)
  ·
    refine ⟨3462180944615960581575755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308120629743973721050503 3462180944615960581575755)
    ·
      refine ⟨5193271416923940872363633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462180944615960581575755 5193271416923940872363633)
      ·
        refine ⟨3894953562692955654272725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5193271416923940872363633 3894953562692955654272725)
        ·
          refine ⟨91287974125616148147017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3894953562692955654272725 91287974125616148147017)
          ·
            refine ⟨68465980594212111110263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91287974125616148147017 68465980594212111110263)
            ·
              refine ⟨102698970891318166665395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68465980594212111110263 102698970891318166665395)
              ·
                refine ⟨154048456336977249998093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102698970891318166665395 154048456336977249998093)
                ·
                  refine ⟨57768171126366468749285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154048456336977249998093 57768171126366468749285)
                  ·
                    refine ⟨10831532086193712890491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57768171126366468749285 10831532086193712890491)
                    ·
                      rfl

theorem cell23_63283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 4].length) (baseStart_63283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63283 prefixEnd_63283 := by exact prefixLift 63283
  have htrace : WordTrace (prefixWord ++ tailWord_63283) baseStart_63283 baseEnd_63283 := by
    simpa [prefixWord, tailWord_63283, baseEnd_63283] using wordTrace_append hprefix tailTrace_63283
  have hstable : (prefixWord ++ tailWord_63283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63283).length < 2 ^ (prefixWord ++ tailWord_63283).sum := by decide
  have hdescent : baseEnd_63283 < baseStart_63283 := by decide
  rcases family_descends (prefixWord ++ tailWord_63283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63306 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_63306 : Nat := 118140960795 + 63306 * 2 ^ 59
def prefixEnd_63306 : Nat := 4983230072969 + 3 ^ 40 * 63306 * 2
def baseEnd_63306 : Nat := 32506406313634548683867

theorem tailTrace_63306 : CollatzResearch.WordTrace tailWord_63306 prefixEnd_63306 32506406313634548683867 := by
  unfold tailWord_63306
  simp only [CollatzResearch.WordTrace]
  refine ⟨577239877165162162284443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1539306339107099099425181 577239877165162162284443)
  ·
    refine ⟨865859815747743243426665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577239877165162162284443 865859815747743243426665)
    ·
      refine ⟨649394861810807432569999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865859815747743243426665 649394861810807432569999)
      ·
        refine ⟨974092292716211148854999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649394861810807432569999 974092292716211148854999)
        ·
          refine ⟨1461138439074316723282499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974092292716211148854999 1461138439074316723282499)
          ·
            refine ⟨2191707658611475084923749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461138439074316723282499 2191707658611475084923749)
            ·
              refine ⟨410945185989651578423203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2191707658611475084923749 410945185989651578423203)
              ·
                refine ⟨616417778984477367634805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410945185989651578423203 616417778984477367634805)
                ·
                  refine ⟨57789166779794753215763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616417778984477367634805 57789166779794753215763)
                  ·
                    refine ⟨86683750169692129823645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57789166779794753215763 86683750169692129823645)
                    ·
                      refine ⟨32506406313634548683867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86683750169692129823645 32506406313634548683867)
                      ·
                        rfl

theorem cell23_63306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_63306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63306 prefixEnd_63306 := by exact prefixLift 63306
  have htrace : WordTrace (prefixWord ++ tailWord_63306) baseStart_63306 baseEnd_63306 := by
    simpa [prefixWord, tailWord_63306, baseEnd_63306] using wordTrace_append hprefix tailTrace_63306
  have hstable : (prefixWord ++ tailWord_63306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63306).length < 2 ^ (prefixWord ++ tailWord_63306).sum := by decide
  have hdescent : baseEnd_63306 < baseStart_63306 := by decide
  rcases family_descends (prefixWord ++ tailWord_63306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63340 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 1, 1, 3]
def baseStart_63340 : Nat := 118140960795 + 63340 * 2 ^ 59
def prefixEnd_63340 : Nat := 4983230072969 + 3 ^ 40 * 63340 * 2
def baseEnd_63340 : Nat := 32523864655887415658711

theorem tailTrace_63340 : CollatzResearch.WordTrace tailWord_63340 prefixEnd_63340 32523864655887415658711 := by
  unfold tailWord_63340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155099795268736227937737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1540133060358314970583649 1155099795268736227937737)
  ·
    refine ⟨866324846451552170953303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155099795268736227937737 866324846451552170953303)
    ·
      refine ⟨1299487269677328256429955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866324846451552170953303 1299487269677328256429955)
      ·
        refine ⟨1949230904515992384644933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299487269677328256429955 1949230904515992384644933)
        ·
          refine ⟨365480794596748572120925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1949230904515992384644933 365480794596748572120925)
          ·
            refine ⟨137055297973780714545347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365480794596748572120925 137055297973780714545347)
            ·
              refine ⟨205582946960671071818021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137055297973780714545347 205582946960671071818021)
              ·
                refine ⟨38546802555125825965879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205582946960671071818021 38546802555125825965879)
                ·
                  refine ⟨57820203832688738948819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38546802555125825965879 57820203832688738948819)
                  ·
                    refine ⟨86730305749033108423229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57820203832688738948819 86730305749033108423229)
                    ·
                      refine ⟨32523864655887415658711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86730305749033108423229 32523864655887415658711)
                      ·
                        rfl

theorem cell23_63340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 1, 3].length) (baseStart_63340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63340 prefixEnd_63340 := by exact prefixLift 63340
  have htrace : WordTrace (prefixWord ++ tailWord_63340) baseStart_63340 baseEnd_63340 := by
    simpa [prefixWord, tailWord_63340, baseEnd_63340] using wordTrace_append hprefix tailTrace_63340
  have hstable : (prefixWord ++ tailWord_63340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63340).length < 2 ^ (prefixWord ++ tailWord_63340).sum := by decide
  have hdescent : baseEnd_63340 < baseStart_63340 := by decide
  rcases family_descends (prefixWord ++ tailWord_63340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63346 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_63346 : Nat := 118140960795 + 63346 * 2 ^ 59
def prefixEnd_63346 : Nat := 4983230072969 + 3 ^ 40 * 63346 * 2
def baseEnd_63346 : Nat := 32526945539814392183683

theorem tailTrace_63346 : CollatzResearch.WordTrace tailWord_63346 prefixEnd_63346 32526945539814392183683 := by
  unfold tailWord_63346
  simp only [CollatzResearch.WordTrace]
  refine ⟨577604607128933870148473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1540278952343823653729261 577604607128933870148473)
  ·
    refine ⟨433203455346700402611355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 577604607128933870148473 433203455346700402611355)
    ·
      refine ⟨649805183020050603917033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433203455346700402611355 649805183020050603917033)
      ·
        refine ⟨487353887265037952937775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649805183020050603917033 487353887265037952937775)
        ·
          refine ⟨731030830897556929406663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487353887265037952937775 731030830897556929406663)
          ·
            refine ⟨1096546246346335394109995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731030830897556929406663 1096546246346335394109995)
            ·
              refine ⟨1644819369519503091164993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096546246346335394109995 1644819369519503091164993)
              ·
                refine ⟨1233614527139627318373745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644819369519503091164993 1233614527139627318373745)
                ·
                  refine ⟨925210895354720488780309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233614527139627318373745 925210895354720488780309)
                  ·
                    refine ⟨43369260719752522911577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 925210895354720488780309 43369260719752522911577)
                    ·
                      refine ⟨32526945539814392183683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43369260719752522911577 32526945539814392183683)
                      ·
                        rfl

theorem cell23_63346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_63346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63346 prefixEnd_63346 := by exact prefixLift 63346
  have htrace : WordTrace (prefixWord ++ tailWord_63346) baseStart_63346 baseEnd_63346 := by
    simpa [prefixWord, tailWord_63346, baseEnd_63346] using wordTrace_append hprefix tailTrace_63346
  have hstable : (prefixWord ++ tailWord_63346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63346).length < 2 ^ (prefixWord ++ tailWord_63346).sum := by decide
  have hdescent : baseEnd_63346 < baseStart_63346 := by decide
  rcases family_descends (prefixWord ++ tailWord_63346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63363 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 5, 2, 2]
def baseStart_63363 : Nat := 118140960795 + 63363 * 2 ^ 59
def prefixEnd_63363 : Nat := 4983230072969 + 3 ^ 40 * 63363 * 2
def baseEnd_63363 : Nat := 32535674710940825671105

theorem tailTrace_63363 : CollatzResearch.WordTrace tailWord_63363 prefixEnd_63363 32535674710940825671105 := by
  unfold tailWord_63363
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311038469454147383962743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1540692312969431589308495 2311038469454147383962743)
  ·
    refine ⟨3466557704181221075944115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311038469454147383962743 3466557704181221075944115)
    ·
      refine ⟨5199836556271831613916173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3466557704181221075944115 5199836556271831613916173)
      ·
        refine ⟨1949938708601936855218565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5199836556271831613916173 1949938708601936855218565)
        ·
          refine ⟨365613507862863160353481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1949938708601936855218565 365613507862863160353481)
          ·
            refine ⟨274210130897147370265111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365613507862863160353481 274210130897147370265111)
            ·
              refine ⟨411315196345721055397667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274210130897147370265111 411315196345721055397667)
              ·
                refine ⟨616972794518581583096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411315196345721055397667 616972794518581583096501)
                ·
                  refine ⟨57841199486117023415297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 616972794518581583096501 57841199486117023415297)
                  ·
                    refine ⟨43380899614587767561473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57841199486117023415297 43380899614587767561473)
                    ·
                      refine ⟨32535674710940825671105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43380899614587767561473 32535674710940825671105)
                      ·
                        rfl

theorem cell23_63363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_63363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63363 prefixEnd_63363 := by exact prefixLift 63363
  have htrace : WordTrace (prefixWord ++ tailWord_63363) baseStart_63363 baseEnd_63363 := by
    simpa [prefixWord, tailWord_63363, baseEnd_63363] using wordTrace_append hprefix tailTrace_63363
  have hstable : (prefixWord ++ tailWord_63363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63363).length < 2 ^ (prefixWord ++ tailWord_63363).sum := by decide
  have hdescent : baseEnd_63363 < baseStart_63363 := by decide
  rcases family_descends (prefixWord ++ tailWord_63363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63367 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_63367 : Nat := 118140960795 + 63367 * 2 ^ 59
def prefixEnd_63367 : Nat := 4983230072969 + 3 ^ 40 * 63367 * 2
def baseEnd_63367 : Nat := 32537728633558810021087

theorem tailTrace_63367 : CollatzResearch.WordTrace tailWord_63367 prefixEnd_63367 32537728633558810021087 := by
  unfold tailWord_63367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311184361439656067108355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1540789574293104044738903 2311184361439656067108355)
  ·
    refine ⟨3466776542159484100662533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311184361439656067108355 3466776542159484100662533)
    ·
      refine ⟨650020601654903268874225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3466776542159484100662533 650020601654903268874225)
      ·
        refine ⟨487515451241177451655669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650020601654903268874225 487515451241177451655669)
        ·
          refine ⟨45704573553860386092719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 487515451241177451655669 45704573553860386092719)
          ·
            refine ⟨68556860330790579139079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45704573553860386092719 68556860330790579139079)
            ·
              refine ⟨102835290496185868708619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68556860330790579139079 102835290496185868708619)
              ·
                refine ⟨154252935744278803062929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102835290496185868708619 154252935744278803062929)
                ·
                  refine ⟨115689701808209102297197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154252935744278803062929 115689701808209102297197)
                  ·
                    refine ⟨43383638178078413361449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115689701808209102297197 43383638178078413361449)
                    ·
                      refine ⟨32537728633558810021087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43383638178078413361449 32537728633558810021087)
                      ·
                        rfl

theorem cell23_63367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_63367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63367 prefixEnd_63367 := by exact prefixLift 63367
  have htrace : WordTrace (prefixWord ++ tailWord_63367) baseStart_63367 baseEnd_63367 := by
    simpa [prefixWord, tailWord_63367, baseEnd_63367] using wordTrace_append hprefix tailTrace_63367
  have hstable : (prefixWord ++ tailWord_63367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63367).length < 2 ^ (prefixWord ++ tailWord_63367).sum := by decide
  have hdescent : baseEnd_63367 < baseStart_63367 := by decide
  rcases family_descends (prefixWord ++ tailWord_63367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63374 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_63374 : Nat := 118140960795 + 63374 * 2 ^ 59
def prefixEnd_63374 : Nat := 4983230072969 + 3 ^ 40 * 63374 * 2
def baseEnd_63374 : Nat := 32541322998140282633555

theorem tailTrace_63374 : CollatzResearch.WordTrace tailWord_63374 prefixEnd_63374 32541322998140282633555 := by
  unfold tailWord_63374
  simp only [CollatzResearch.WordTrace]
  refine ⟨288929959051787032826647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1540959781609530841742117 288929959051787032826647)
  ·
    refine ⟨433394938577680549239971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288929959051787032826647 433394938577680549239971)
    ·
      refine ⟨650092407866520823859957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433394938577680549239971 650092407866520823859957)
      ·
        refine ⟨60946163237486327236871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650092407866520823859957 60946163237486327236871)
        ·
          refine ⟨91419244856229490855307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60946163237486327236871 91419244856229490855307)
          ·
            refine ⟨137128867284344236282961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91419244856229490855307 137128867284344236282961)
            ·
              refine ⟨102846650463258177212221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137128867284344236282961 102846650463258177212221)
              ·
                refine ⟨38567493923721816454583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102846650463258177212221 38567493923721816454583)
                ·
                  refine ⟨57851240885582724681875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38567493923721816454583 57851240885582724681875)
                  ·
                    refine ⟨86776861328374087022813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57851240885582724681875 86776861328374087022813)
                    ·
                      refine ⟨32541322998140282633555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86776861328374087022813 32541322998140282633555)
                      ·
                        rfl

theorem cell23_63374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_63374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63374 prefixEnd_63374 := by exact prefixLift 63374
  have htrace : WordTrace (prefixWord ++ tailWord_63374) baseStart_63374 baseEnd_63374 := by
    simpa [prefixWord, tailWord_63374, baseEnd_63374] using wordTrace_append hprefix tailTrace_63374
  have hstable : (prefixWord ++ tailWord_63374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63374).length < 2 ^ (prefixWord ++ tailWord_63374).sum := by decide
  have hdescent : baseEnd_63374 < baseStart_63374 := by decide
  rcases family_descends (prefixWord ++ tailWord_63374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63379 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3]
def baseStart_63379 : Nat := 118140960795 + 63379 * 2 ^ 59
def prefixEnd_63379 : Nat := 4983230072969 + 3 ^ 40 * 63379 * 2
def baseEnd_63379 : Nat := 32543890401412763071031

theorem tailTrace_63379 : CollatzResearch.WordTrace tailWord_63379 prefixEnd_63379 32543890401412763071031 := by
  unfold tailWord_63379
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311622037396182116545191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1541081358264121411030127 2311622037396182116545191)
  ·
    refine ⟨3467433056094273174817787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311622037396182116545191 3467433056094273174817787)
    ·
      refine ⟨5201149584141409762226681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3467433056094273174817787 5201149584141409762226681)
      ·
        refine ⟨3900862188106057321670011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201149584141409762226681 3900862188106057321670011)
        ·
          refine ⟨5851293282159085982505017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900862188106057321670011 5851293282159085982505017)
          ·
            refine ⟨4388469961619314486878763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5851293282159085982505017 4388469961619314486878763)
            ·
              refine ⟨6582704942428971730318145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388469961619314486878763 6582704942428971730318145)
              ·
                refine ⟨4937028706821728797738609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582704942428971730318145 4937028706821728797738609)
                ·
                  refine ⟨3702771530116296598303957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937028706821728797738609 3702771530116296598303957)
                  ·
                    refine ⟨86783707737100701522749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3702771530116296598303957 86783707737100701522749)
                    ·
                      refine ⟨32543890401412763071031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86783707737100701522749 32543890401412763071031)
                      ·
                        rfl

theorem cell23_63379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_63379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63379 prefixEnd_63379 := by exact prefixLift 63379
  have htrace : WordTrace (prefixWord ++ tailWord_63379) baseStart_63379 baseEnd_63379 := by
    simpa [prefixWord, tailWord_63379, baseEnd_63379] using wordTrace_append hprefix tailTrace_63379
  have hstable : (prefixWord ++ tailWord_63379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63379).length < 2 ^ (prefixWord ++ tailWord_63379).sum := by decide
  have hdescent : baseEnd_63379 < baseStart_63379 := by decide
  rcases family_descends (prefixWord ++ tailWord_63379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63380 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_63380 : Nat := 118140960795 + 63380 * 2 ^ 59
def prefixEnd_63380 : Nat := 4983230072969 + 3 ^ 40 * 63380 * 2
def baseEnd_63380 : Nat := 32544403882067259158527

theorem tailTrace_63380 : CollatzResearch.WordTrace tailWord_63380 prefixEnd_63380 32544403882067259158527 := by
  unfold tailWord_63380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155829255196279643665797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1541105673595039524887729 1155829255196279643665797)
  ·
    refine ⟨216717985349302433187337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1155829255196279643665797 216717985349302433187337)
    ·
      refine ⟨162538489011976824890503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216717985349302433187337 162538489011976824890503)
      ·
        refine ⟨243807733517965237335755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162538489011976824890503 243807733517965237335755)
        ·
          refine ⟨365711600276947856003633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243807733517965237335755 365711600276947856003633)
          ·
            refine ⟨274283700207710892002725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365711600276947856003633 274283700207710892002725)
            ·
              refine ⟨51428193788945792250511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274283700207710892002725 51428193788945792250511)
              ·
                refine ⟨77142290683418688375767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51428193788945792250511 77142290683418688375767)
                ·
                  refine ⟨115713436025128032563651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77142290683418688375767 115713436025128032563651)
                  ·
                    refine ⟨173570154037692048845477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115713436025128032563651 173570154037692048845477)
                    ·
                      refine ⟨32544403882067259158527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 173570154037692048845477 32544403882067259158527)
                      ·
                        rfl

theorem cell23_63380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_63380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63380 prefixEnd_63380 := by exact prefixLift 63380
  have htrace : WordTrace (prefixWord ++ tailWord_63380) baseStart_63380 baseEnd_63380 := by
    simpa [prefixWord, tailWord_63380, baseEnd_63380] using wordTrace_append hprefix tailTrace_63380
  have hstable : (prefixWord ++ tailWord_63380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63380).length < 2 ^ (prefixWord ++ tailWord_63380).sum := by decide
  have hdescent : baseEnd_63380 < baseStart_63380 := by decide
  rcases family_descends (prefixWord ++ tailWord_63380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63383 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_63383 : Nat := 118140960795 + 63383 * 2 ^ 59
def prefixEnd_63383 : Nat := 4983230072969 + 3 ^ 40 * 63383 * 2
def baseEnd_63383 : Nat := 32545944324030747421013

theorem tailTrace_63383 : CollatzResearch.WordTrace tailWord_63383 prefixEnd_63383 32545944324030747421013 := by
  unfold tailWord_63383
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311767929381690799690803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1541178619587793866460535 2311767929381690799690803)
  ·
    refine ⟨3467651894072536199536205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2311767929381690799690803 3467651894072536199536205)
    ·
      refine ⟨1300369460277201074826077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3467651894072536199536205 1300369460277201074826077)
      ·
        refine ⟨487638547603950403059779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1300369460277201074826077 487638547603950403059779)
        ·
          refine ⟨731457821405925604589669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487638547603950403059779 731457821405925604589669)
          ·
            refine ⟨137148341513611050860563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 731457821405925604589669 137148341513611050860563)
            ·
              refine ⟨205722512270416576290845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137148341513611050860563 205722512270416576290845)
              ·
                refine ⟨77145942101406216109067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205722512270416576290845 77145942101406216109067)
                ·
                  refine ⟨115718913152109324163601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77145942101406216109067 115718913152109324163601)
                  ·
                    refine ⟨86789184864081993122701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115718913152109324163601 86789184864081993122701)
                    ·
                      refine ⟨32545944324030747421013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86789184864081993122701 32545944324030747421013)
                      ·
                        rfl

theorem cell23_63383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_63383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63383 prefixEnd_63383 := by exact prefixLift 63383
  have htrace : WordTrace (prefixWord ++ tailWord_63383) baseStart_63383 baseEnd_63383 := by
    simpa [prefixWord, tailWord_63383, baseEnd_63383] using wordTrace_append hprefix tailTrace_63383
  have hstable : (prefixWord ++ tailWord_63383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63383).length < 2 ^ (prefixWord ++ tailWord_63383).sum := by decide
  have hdescent : baseEnd_63383 < baseStart_63383 := by decide
  rcases family_descends (prefixWord ++ tailWord_63383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63400 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_63400 : Nat := 118140960795 + 63400 * 2 ^ 59
def prefixEnd_63400 : Nat := 4983230072969 + 3 ^ 40 * 63400 * 2
def baseEnd_63400 : Nat := 32554673495157180908435

theorem tailTrace_63400 : CollatzResearch.WordTrace tailWord_63400 prefixEnd_63400 32554673495157180908435 := by
  unfold tailWord_63400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156193985160051351529827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1541591980213401802039769 1156193985160051351529827)
  ·
    refine ⟨1734290977740077027294741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156193985160051351529827 1734290977740077027294741)
    ·
      refine ⟨81294889581566110654441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1734290977740077027294741 81294889581566110654441)
      ·
        refine ⟨60971167186174582990831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81294889581566110654441 60971167186174582990831)
        ·
          refine ⟨91456750779261874486247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60971167186174582990831 91456750779261874486247)
          ·
            refine ⟨137185126168892811729371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91456750779261874486247 137185126168892811729371)
            ·
              refine ⟨205777689253339217594057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137185126168892811729371 205777689253339217594057)
              ·
                refine ⟨154333266940004413195543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205777689253339217594057 154333266940004413195543)
                ·
                  refine ⟨231499900410006619793315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154333266940004413195543 231499900410006619793315)
                  ·
                    refine ⟨347249850615009929689973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231499900410006619793315 347249850615009929689973)
                    ·
                      refine ⟨32554673495157180908435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 347249850615009929689973 32554673495157180908435)
                      ·
                        rfl

theorem cell23_63400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_63400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63400 prefixEnd_63400 := by exact prefixLift 63400
  have htrace : WordTrace (prefixWord ++ tailWord_63400) baseStart_63400 baseEnd_63400 := by
    simpa [prefixWord, tailWord_63400, baseEnd_63400] using wordTrace_append hprefix tailTrace_63400
  have hstable : (prefixWord ++ tailWord_63400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63400).length < 2 ^ (prefixWord ++ tailWord_63400).sum := by decide
  have hdescent : baseEnd_63400 < baseStart_63400 := by decide
  rcases family_descends (prefixWord ++ tailWord_63400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63413 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_63413 : Nat := 118140960795 + 63413 * 2 ^ 59
def prefixEnd_63413 : Nat := 4983230072969 + 3 ^ 40 * 63413 * 2
def baseEnd_63413 : Nat := 32561348743665630045875

theorem tailTrace_63413 : CollatzResearch.WordTrace tailWord_63413 prefixEnd_63413 32561348743665630045875 := by
  unfold tailWord_63413
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312862119273005923282893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1541908079515337282188595 2312862119273005923282893)
  ·
    refine ⟨867323294727377221231085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2312862119273005923282893 867323294727377221231085)
    ·
      refine ⟨325246235522766457961657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 867323294727377221231085 325246235522766457961657)
      ·
        refine ⟨243934676642074843471243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325246235522766457961657 243934676642074843471243)
        ·
          refine ⟨365902014963112265206865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243934676642074843471243 365902014963112265206865)
          ·
            refine ⟨274426511222334198905149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365902014963112265206865 274426511222334198905149)
            ·
              refine ⟨102909941708375324589431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274426511222334198905149 102909941708375324589431)
              ·
                refine ⟨154364912562562986884147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102909941708375324589431 154364912562562986884147)
                ·
                  refine ⟨231547368843844480326221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154364912562562986884147 231547368843844480326221)
                  ·
                    refine ⟨86830263316441680122333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231547368843844480326221 86830263316441680122333)
                    ·
                      refine ⟨32561348743665630045875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 86830263316441680122333 32561348743665630045875)
                      ·
                        rfl

theorem cell23_63413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_63413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63413 prefixEnd_63413 := by exact prefixLift 63413
  have htrace : WordTrace (prefixWord ++ tailWord_63413) baseStart_63413 baseEnd_63413 := by
    simpa [prefixWord, tailWord_63413, baseEnd_63413] using wordTrace_append hprefix tailTrace_63413
  have hstable : (prefixWord ++ tailWord_63413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63413).length < 2 ^ (prefixWord ++ tailWord_63413).sum := by decide
  have hdescent : baseEnd_63413 < baseStart_63413 := by decide
  rcases family_descends (prefixWord ++ tailWord_63413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63419 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_63419 : Nat := 118140960795 + 63419 * 2 ^ 59
def prefixEnd_63419 : Nat := 4983230072969 + 3 ^ 40 * 63419 * 2
def baseEnd_63419 : Nat := 32564429627592606570847

theorem tailTrace_63419 : CollatzResearch.WordTrace tailWord_63419 prefixEnd_63419 32564429627592606570847 := by
  unfold tailWord_63419
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313080957251268948001311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542053971500845965334207 2313080957251268948001311)
  ·
    refine ⟨3469621435876903422001967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2313080957251268948001311 3469621435876903422001967)
    ·
      refine ⟨5204432153815355133002951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469621435876903422001967 5204432153815355133002951)
      ·
        refine ⟨7806648230723032699504427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204432153815355133002951 7806648230723032699504427)
        ·
          refine ⟨11709972346084549049256641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806648230723032699504427 11709972346084549049256641)
          ·
            refine ⟨8782479259563411786942481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11709972346084549049256641 8782479259563411786942481)
            ·
              refine ⟨6586859444672558840206861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8782479259563411786942481 6586859444672558840206861)
              ·
                refine ⟨2470072291752209565077573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6586859444672558840206861 2470072291752209565077573)
                ·
                  refine ⟨463138554703539293452045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470072291752209565077573 463138554703539293452045)
                  ·
                    refine ⟨173676958013827235044517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 463138554703539293452045 173676958013827235044517)
                    ·
                      refine ⟨32564429627592606570847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 173676958013827235044517 32564429627592606570847)
                      ·
                        rfl

theorem cell23_63419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_63419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63419 prefixEnd_63419 := by exact prefixLift 63419
  have htrace : WordTrace (prefixWord ++ tailWord_63419) baseStart_63419 baseEnd_63419 := by
    simpa [prefixWord, tailWord_63419, baseEnd_63419] using wordTrace_append hprefix tailTrace_63419
  have hstable : (prefixWord ++ tailWord_63419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63419).length < 2 ^ (prefixWord ++ tailWord_63419).sum := by decide
  have hdescent : baseEnd_63419 < baseStart_63419 := by decide
  rcases family_descends (prefixWord ++ tailWord_63419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63420 : List Nat := [2, 2, 2, 5, 1, 2, 2, 7]
def baseStart_63420 : Nat := 118140960795 + 63420 * 2 ^ 59
def prefixEnd_63420 : Nat := 4983230072969 + 3 ^ 40 * 63420 * 2
def baseEnd_63420 : Nat := 1206109004009151950309

theorem tailTrace_63420 : CollatzResearch.WordTrace tailWord_63420 prefixEnd_63420 1206109004009151950309 := by
  unfold tailWord_63420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156558715123823059393857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1542078286831764079191809 1156558715123823059393857)
  ·
    refine ⟨867419036342867294545393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156558715123823059393857 867419036342867294545393)
    ·
      refine ⟨650564277257150470909045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867419036342867294545393 650564277257150470909045)
      ·
        refine ⟨60990400992857856647723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 650564277257150470909045 60990400992857856647723)
        ·
          refine ⟨91485601489286784971585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60990400992857856647723 91485601489286784971585)
          ·
            refine ⟨68614201116965088728689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91485601489286784971585 68614201116965088728689)
            ·
              refine ⟨51460650837723816546517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68614201116965088728689 51460650837723816546517)
              ·
                refine ⟨1206109004009151950309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51460650837723816546517 1206109004009151950309)
                ·
                  rfl

theorem cell23_63420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 7].length) (baseStart_63420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63420 prefixEnd_63420 := by exact prefixLift 63420
  have htrace : WordTrace (prefixWord ++ tailWord_63420) baseStart_63420 baseEnd_63420 := by
    simpa [prefixWord, tailWord_63420, baseEnd_63420] using wordTrace_append hprefix tailTrace_63420
  have hstable : (prefixWord ++ tailWord_63420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63420).length < 2 ^ (prefixWord ++ tailWord_63420).sum := by decide
  have hdescent : baseEnd_63420 < baseStart_63420 := by decide
  rcases family_descends (prefixWord ++ tailWord_63420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63429 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_63429 : Nat := 118140960795 + 63429 * 2 ^ 59
def prefixEnd_63429 : Nat := 4983230072969 + 3 ^ 40 * 63429 * 2
def baseEnd_63429 : Nat := 10856521478045855815267

theorem tailTrace_63429 : CollatzResearch.WordTrace tailWord_63429 prefixEnd_63429 10856521478045855815267 := by
  unfold tailWord_63429
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313445687215040655865341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542297124810027103910227 2313445687215040655865341)
  ·
    refine ⟨867542132705640245949503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2313445687215040655865341 867542132705640245949503)
    ·
      refine ⟨1301313199058460368924255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867542132705640245949503 1301313199058460368924255)
      ·
        refine ⟨1951969798587690553386383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301313199058460368924255 1951969798587690553386383)
        ·
          refine ⟨2927954697881535830079575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951969798587690553386383 2927954697881535830079575)
          ·
            refine ⟨4391932046822303745119363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927954697881535830079575 4391932046822303745119363)
            ·
              refine ⟨6587898070233455617679045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391932046822303745119363 6587898070233455617679045)
              ·
                refine ⟨1235230888168772928314821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6587898070233455617679045 1235230888168772928314821)
                ·
                  refine ⟨231605791531644924059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235230888168772928314821 231605791531644924059029)
                  ·
                    refine ⟨10856521478045855815267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 231605791531644924059029 10856521478045855815267)
                    ·
                      rfl

theorem cell23_63429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_63429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63429 prefixEnd_63429 := by exact prefixLift 63429
  have htrace : WordTrace (prefixWord ++ tailWord_63429) baseStart_63429 baseEnd_63429 := by
    simpa [prefixWord, tailWord_63429, baseEnd_63429] using wordTrace_append hprefix tailTrace_63429
  have hstable : (prefixWord ++ tailWord_63429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63429).length < 2 ^ (prefixWord ++ tailWord_63429).sum := by decide
  have hdescent : baseEnd_63429 < baseStart_63429 := by decide
  rcases family_descends (prefixWord ++ tailWord_63429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63466 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_63466 : Nat := 118140960795 + 63466 * 2 ^ 59
def prefixEnd_63466 : Nat := 4983230072969 + 3 ^ 40 * 63466 * 2
def baseEnd_63466 : Nat := 32588563218353922683131

theorem tailTrace_63466 : CollatzResearch.WordTrace tailWord_63466 prefixEnd_63466 32588563218353922683131 := by
  unfold tailWord_63466
  simp only [CollatzResearch.WordTrace]
  refine ⟨578698797020248993740563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1543196792053997316641501 578698797020248993740563)
  ·
    refine ⟨868048195530373490610845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 578698797020248993740563 868048195530373490610845)
    ·
      refine ⟨325518073323890058979067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 868048195530373490610845 325518073323890058979067)
      ·
        refine ⟨488277109985835088468601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325518073323890058979067 488277109985835088468601)
        ·
          refine ⟨366207832489376316351451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488277109985835088468601 366207832489376316351451)
          ·
            refine ⟨549311748734064474527177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366207832489376316351451 549311748734064474527177)
            ·
              refine ⟨411983811550548355895383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549311748734064474527177 411983811550548355895383)
              ·
                refine ⟨617975717325822533843075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411983811550548355895383 617975717325822533843075)
                ·
                  refine ⟨926963575988733800764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617975717325822533843075 926963575988733800764613)
                  ·
                    refine ⟨173805670497887587643365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 926963575988733800764613 173805670497887587643365)
                    ·
                      refine ⟨32588563218353922683131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 173805670497887587643365 32588563218353922683131)
                      ·
                        rfl

theorem cell23_63466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_63466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63466 prefixEnd_63466 := by exact prefixLift 63466
  have htrace : WordTrace (prefixWord ++ tailWord_63466) baseStart_63466 baseEnd_63466 := by
    simpa [prefixWord, tailWord_63466, baseEnd_63466] using wordTrace_append hprefix tailTrace_63466
  have hstable : (prefixWord ++ tailWord_63466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63466).length < 2 ^ (prefixWord ++ tailWord_63466).sum := by decide
  have hdescent : baseEnd_63466 < baseStart_63466 := by decide
  rcases family_descends (prefixWord ++ tailWord_63466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63479 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_63479 : Nat := 118140960795 + 63479 * 2 ^ 59
def prefixEnd_63479 : Nat := 4983230072969 + 3 ^ 40 * 63479 * 2
def baseEnd_63479 : Nat := 32595238466862371820571

theorem tailTrace_63479 : CollatzResearch.WordTrace tailWord_63479 prefixEnd_63479 32595238466862371820571 := by
  unfold tailWord_63479
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315269337033899195185491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1543512891355932796790327 2315269337033899195185491)
  ·
    refine ⟨3472904005550848792778237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2315269337033899195185491 3472904005550848792778237)
    ·
      refine ⟨1302339002081568297291839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3472904005550848792778237 1302339002081568297291839)
      ·
        refine ⟨1953508503122352445937759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302339002081568297291839 1953508503122352445937759)
        ·
          refine ⟨2930262754683528668906639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953508503122352445937759 2930262754683528668906639)
          ·
            refine ⟨4395394132025293003359959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930262754683528668906639 4395394132025293003359959)
            ·
              refine ⟨6593091198037939505039939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395394132025293003359959 6593091198037939505039939)
              ·
                refine ⟨9889636797056909257559909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593091198037939505039939 9889636797056909257559909)
                ·
                  refine ⟨1854306899448170485792483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9889636797056909257559909 1854306899448170485792483)
                  ·
                    refine ⟨2781460349172255728688725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1854306899448170485792483 2781460349172255728688725)
                    ·
                      refine ⟨32595238466862371820571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 2781460349172255728688725 32595238466862371820571)
                      ·
                        rfl

theorem cell23_63479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_63479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63479 prefixEnd_63479 := by exact prefixLift 63479
  have htrace : WordTrace (prefixWord ++ tailWord_63479) baseStart_63479 baseEnd_63479 := by
    simpa [prefixWord, tailWord_63479, baseEnd_63479] using wordTrace_append hprefix tailTrace_63479
  have hstable : (prefixWord ++ tailWord_63479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63479).length < 2 ^ (prefixWord ++ tailWord_63479).sum := by decide
  have hdescent : baseEnd_63479 < baseStart_63479 := by decide
  rcases family_descends (prefixWord ++ tailWord_63479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63540 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_63540 : Nat := 118140960795 + 63540 * 2 ^ 59
def prefixEnd_63540 : Nat := 4983230072969 + 3 ^ 40 * 63540 * 2
def baseEnd_63540 : Nat := 10875520262262211052597

theorem tailTrace_63540 : CollatzResearch.WordTrace tailWord_63540 prefixEnd_63540 10875520262262211052597 := by
  unfold tailWord_63540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158747094906453306578037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1544996126541937742104049 1158747094906453306578037)
  ·
    refine ⟨108632540147479997491691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1158747094906453306578037 108632540147479997491691)
    ·
      refine ⟨162948810221219996237537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108632540147479997491691 162948810221219996237537)
      ·
        refine ⟨122211607665914997178153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162948810221219996237537 122211607665914997178153)
        ·
          refine ⟨91658705749436247883615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122211607665914997178153 91658705749436247883615)
          ·
            refine ⟨137488058624154371825423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91658705749436247883615 137488058624154371825423)
            ·
              refine ⟨206232087936231557738135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137488058624154371825423 206232087936231557738135)
              ·
                refine ⟨309348131904347336607203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206232087936231557738135 309348131904347336607203)
                ·
                  refine ⟨464022197856521004910805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309348131904347336607203 464022197856521004910805)
                  ·
                    refine ⟨10875520262262211052597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 464022197856521004910805 10875520262262211052597)
                    ·
                      rfl

theorem cell23_63540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_63540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63540 prefixEnd_63540 := by exact prefixLift 63540
  have htrace : WordTrace (prefixWord ++ tailWord_63540) baseStart_63540 baseEnd_63540 := by
    simpa [prefixWord, tailWord_63540, baseEnd_63540] using wordTrace_append hprefix tailTrace_63540
  have hstable : (prefixWord ++ tailWord_63540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63540).length < 2 ^ (prefixWord ++ tailWord_63540).sum := by decide
  have hdescent : baseEnd_63540 < baseStart_63540 := by decide
  rcases family_descends (prefixWord ++ tailWord_63540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63543 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_63543 : Nat := 118140960795 + 63543 * 2 ^ 59
def prefixEnd_63543 : Nat := 4983230072969 + 3 ^ 40 * 63543 * 2
def baseEnd_63543 : Nat := 32628101228750121420277

theorem tailTrace_63543 : CollatzResearch.WordTrace tailWord_63543 prefixEnd_63543 32628101228750121420277 := by
  unfold tailWord_63543
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317603608802038125515283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1545069072534692083676855 2317603608802038125515283)
  ·
    refine ⟨3476405413203057188272925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317603608802038125515283 3476405413203057188272925)
    ·
      refine ⟨1303652029951146445602347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3476405413203057188272925 1303652029951146445602347)
      ·
        refine ⟨1955478044926719668403521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303652029951146445602347 1955478044926719668403521)
        ·
          refine ⟨1466608533695039751302641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955478044926719668403521 1466608533695039751302641)
          ·
            refine ⟨1099956400271279813476981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466608533695039751302641 1099956400271279813476981)
            ·
              refine ⟨103120912525432482513467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1099956400271279813476981 103120912525432482513467)
              ·
                refine ⟨154681368788148723770201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103120912525432482513467 154681368788148723770201)
                ·
                  refine ⟨116011026591111542827651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154681368788148723770201 116011026591111542827651)
                  ·
                    refine ⟨174016539886667314241477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116011026591111542827651 174016539886667314241477)
                    ·
                      refine ⟨32628101228750121420277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 174016539886667314241477 32628101228750121420277)
                      ·
                        rfl

theorem cell23_63543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_63543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63543 prefixEnd_63543 := by exact prefixLift 63543
  have htrace : WordTrace (prefixWord ++ tailWord_63543) baseStart_63543 baseEnd_63543 := by
    simpa [prefixWord, tailWord_63543, baseEnd_63543] using wordTrace_append hprefix tailTrace_63543
  have hstable : (prefixWord ++ tailWord_63543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63543).length < 2 ^ (prefixWord ++ tailWord_63543).sum := by decide
  have hdescent : baseEnd_63543 < baseStart_63543 := by decide
  rcases family_descends (prefixWord ++ tailWord_63543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63647 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 1, 5]
def baseStart_63647 : Nat := 118140960795 + 63647 * 2 ^ 59
def prefixEnd_63647 : Nat := 4983230072969 + 3 ^ 40 * 63647 * 2
def baseEnd_63647 : Nat := 10893834405605904839933

theorem tailTrace_63647 : CollatzResearch.WordTrace tailWord_63647 prefixEnd_63647 10893834405605904839933 := by
  unfold tailWord_63647
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321396800425263887301195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1547597866950175924867463 2321396800425263887301195)
  ·
    refine ⟨3482095200637895830951793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2321396800425263887301195 3482095200637895830951793)
    ·
      refine ⟨2611571400478421873213845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3482095200637895830951793 2611571400478421873213845)
      ·
        refine ⟨122417409397426025306899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2611571400478421873213845 122417409397426025306899)
        ·
          refine ⟨183626114096139037960349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122417409397426025306899 183626114096139037960349)
          ·
            refine ⟨68859792786052139235131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183626114096139037960349 68859792786052139235131)
            ·
              refine ⟨103289689179078208852697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68859792786052139235131 103289689179078208852697)
              ·
                refine ⟨77467266884308656639523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103289689179078208852697 77467266884308656639523)
                ·
                  refine ⟨116200900326462984959285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77467266884308656639523 116200900326462984959285)
                  ·
                    refine ⟨10893834405605904839933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116200900326462984959285 10893834405605904839933)
                    ·
                      rfl

theorem cell23_63647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_63647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63647 prefixEnd_63647 := by exact prefixLift 63647
  have htrace : WordTrace (prefixWord ++ tailWord_63647) baseStart_63647 baseEnd_63647 := by
    simpa [prefixWord, tailWord_63647, baseEnd_63647] using wordTrace_append hprefix tailTrace_63647
  have hstable : (prefixWord ++ tailWord_63647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63647).length < 2 ^ (prefixWord ++ tailWord_63647).sum := by decide
  have hdescent : baseEnd_63647 < baseStart_63647 := by decide
  rcases family_descends (prefixWord ++ tailWord_63647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63678 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_63678 : Nat := 118140960795 + 63678 * 2 ^ 59
def prefixEnd_63678 : Nat := 4983230072969 + 3 ^ 40 * 63678 * 2
def baseEnd_63678 : Nat := 32697421117107093232157

theorem tailTrace_63678 : CollatzResearch.WordTrace tailWord_63678 prefixEnd_63678 32697421117107093232157 := by
  unfold tailWord_63678
  simp only [CollatzResearch.WordTrace]
  refine ⟨290315932914119522709961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1548351642208637454453125 290315932914119522709961)
  ·
    refine ⟨217736949685589642032471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290315932914119522709961 217736949685589642032471)
    ·
      refine ⟨326605424528384463048707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217736949685589642032471 326605424528384463048707)
      ·
        refine ⟨489908136792576694573061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326605424528384463048707 489908136792576694573061)
        ·
          refine ⟨91857775648608130232449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489908136792576694573061 91857775648608130232449)
          ·
            refine ⟨68893331736456097674337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91857775648608130232449 68893331736456097674337)
            ·
              refine ⟨51669998802342073255753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68893331736456097674337 51669998802342073255753)
              ·
                refine ⟨38752499101756554941815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51669998802342073255753 38752499101756554941815)
                ·
                  refine ⟨58128748652634832412723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38752499101756554941815 58128748652634832412723)
                  ·
                    refine ⟨87193122978952248619085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58128748652634832412723 87193122978952248619085)
                    ·
                      refine ⟨32697421117107093232157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87193122978952248619085 32697421117107093232157)
                      ·
                        rfl

theorem cell23_63678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_63678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63678 prefixEnd_63678 := by exact prefixLift 63678
  have htrace : WordTrace (prefixWord ++ tailWord_63678) baseStart_63678 baseEnd_63678 := by
    simpa [prefixWord, tailWord_63678, baseEnd_63678] using wordTrace_append hprefix tailTrace_63678
  have hstable : (prefixWord ++ tailWord_63678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63678).length < 2 ^ (prefixWord ++ tailWord_63678).sum := by decide
  have hdescent : baseEnd_63678 < baseStart_63678 := by decide
  rcases family_descends (prefixWord ++ tailWord_63678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63713 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_63713 : Nat := 118140960795 + 63713 * 2 ^ 59
def prefixEnd_63713 : Nat := 4983230072969 + 3 ^ 40 * 63713 * 2
def baseEnd_63713 : Nat := 32715392940014456294495

theorem tailTrace_63713 : CollatzResearch.WordTrace tailWord_63713 prefixEnd_63713 32715392940014456294495 := by
  unfold tailWord_63713
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323804018186157159203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1549202678790771439469195 2323804018186157159203793)
  ·
    refine ⟨1742853013639617869402845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2323804018186157159203793 1742853013639617869402845)
    ·
      refine ⟨653569880114856701026067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1742853013639617869402845 653569880114856701026067)
      ·
        refine ⟨980354820172285051539101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653569880114856701026067 980354820172285051539101)
        ·
          refine ⟨367633057564606894327163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980354820172285051539101 367633057564606894327163)
          ·
            refine ⟨551449586346910341490745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367633057564606894327163 551449586346910341490745)
            ·
              refine ⟨413587189760182756118059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551449586346910341490745 413587189760182756118059)
              ·
                refine ⟨620380784640274134177089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413587189760182756118059 620380784640274134177089)
                ·
                  refine ⟨465285588480205600632817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620380784640274134177089 465285588480205600632817)
                  ·
                    refine ⟨348964191360154200474613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 465285588480205600632817 348964191360154200474613)
                    ·
                      refine ⟨32715392940014456294495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 348964191360154200474613 32715392940014456294495)
                      ·
                        rfl

theorem cell23_63713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_63713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63713 prefixEnd_63713 := by exact prefixLift 63713
  have htrace : WordTrace (prefixWord ++ tailWord_63713) baseStart_63713 baseEnd_63713 := by
    simpa [prefixWord, tailWord_63713, baseEnd_63713] using wordTrace_append hprefix tailTrace_63713
  have hstable : (prefixWord ++ tailWord_63713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63713).length < 2 ^ (prefixWord ++ tailWord_63713).sum := by decide
  have hdescent : baseEnd_63713 < baseStart_63713 := by decide
  rcases family_descends (prefixWord ++ tailWord_63713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63734 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_63734 : Nat := 118140960795 + 63734 * 2 ^ 59
def prefixEnd_63734 : Nat := 4983230072969 + 3 ^ 40 * 63734 * 2
def baseEnd_63734 : Nat := 32726176033758874131899

theorem tailTrace_63734 : CollatzResearch.WordTrace tailWord_63734 prefixEnd_63734 32726176033758874131899 := by
  unfold tailWord_63734
  simp only [CollatzResearch.WordTrace]
  refine ⟨145285621944379859107391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1549713300740051830478837 145285621944379859107391)
  ·
    refine ⟨217928432916569788661087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145285621944379859107391 217928432916569788661087)
    ·
      refine ⟨326892649374854682991631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217928432916569788661087 326892649374854682991631)
      ·
        refine ⟨490338974062282024487447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326892649374854682991631 490338974062282024487447)
        ·
          refine ⟨735508461093423036731171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490338974062282024487447 735508461093423036731171)
          ·
            refine ⟨1103262691640134555096757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735508461093423036731171 1103262691640134555096757)
            ·
              refine ⟨103430877341262614540321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1103262691640134555096757 103430877341262614540321)
              ·
                refine ⟨77573158005946960905241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103430877341262614540321 77573158005946960905241)
                ·
                  refine ⟨58179868504460220678931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77573158005946960905241 58179868504460220678931)
                  ·
                    refine ⟨87269802756690331018397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58179868504460220678931 87269802756690331018397)
                    ·
                      refine ⟨32726176033758874131899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87269802756690331018397 32726176033758874131899)
                      ·
                        rfl

theorem cell23_63734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_63734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63734 prefixEnd_63734 := by exact prefixLift 63734
  have htrace : WordTrace (prefixWord ++ tailWord_63734) baseStart_63734 baseEnd_63734 := by
    simpa [prefixWord, tailWord_63734, baseEnd_63734] using wordTrace_append hprefix tailTrace_63734
  have hstable : (prefixWord ++ tailWord_63734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63734).length < 2 ^ (prefixWord ++ tailWord_63734).sum := by decide
  have hdescent : baseEnd_63734 < baseStart_63734 := by decide
  rcases family_descends (prefixWord ++ tailWord_63734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63751 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_63751 : Nat := 118140960795 + 63751 * 2 ^ 59
def prefixEnd_63751 : Nat := 4983230072969 + 3 ^ 40 * 63751 * 2
def baseEnd_63751 : Nat := 32734905204885307619321

theorem tailTrace_63751 : CollatzResearch.WordTrace tailWord_63751 prefixEnd_63751 32734905204885307619321 := by
  unfold tailWord_63751
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325189992048489649087107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1550126661365659766058071 2325189992048489649087107)
  ·
    refine ⟨3487784988072734473630661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2325189992048489649087107 3487784988072734473630661)
    ·
      refine ⟨653959685263637713805749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3487784988072734473630661 653959685263637713805749)
      ·
        refine ⟨61308720493466035669289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 653959685263637713805749 61308720493466035669289)
        ·
          refine ⟨45981540370099526751967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61308720493466035669289 45981540370099526751967)
          ·
            refine ⟨68972310555149290127951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45981540370099526751967 68972310555149290127951)
            ·
              refine ⟨103458465832723935191927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68972310555149290127951 103458465832723935191927)
              ·
                refine ⟨155187698749085902787891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103458465832723935191927 155187698749085902787891)
                ·
                  refine ⟨232781548123628854181837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155187698749085902787891 232781548123628854181837)
                  ·
                    refine ⟨87293080546360820318189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232781548123628854181837 87293080546360820318189)
                    ·
                      refine ⟨32734905204885307619321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87293080546360820318189 32734905204885307619321)
                      ·
                        rfl

theorem cell23_63751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_63751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63751 prefixEnd_63751 := by exact prefixLift 63751
  have htrace : WordTrace (prefixWord ++ tailWord_63751) baseStart_63751 baseEnd_63751 := by
    simpa [prefixWord, tailWord_63751, baseEnd_63751] using wordTrace_append hprefix tailTrace_63751
  have hstable : (prefixWord ++ tailWord_63751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63751).length < 2 ^ (prefixWord ++ tailWord_63751).sum := by decide
  have hdescent : baseEnd_63751 < baseStart_63751 := by decide
  rcases family_descends (prefixWord ++ tailWord_63751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63847 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_63847 : Nat := 118140960795 + 63847 * 2 ^ 59
def prefixEnd_63847 : Nat := 4983230072969 + 3 ^ 40 * 63847 * 2
def baseEnd_63847 : Nat := 32784199347716932018879

theorem tailTrace_63847 : CollatzResearch.WordTrace tailWord_63847 prefixEnd_63847 32784199347716932018879 := by
  unfold tailWord_63847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328691399700698044581795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1552460933133798696387863 2328691399700698044581795)
  ·
    refine ⟨3493037099551047066872693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2328691399700698044581795 3493037099551047066872693)
    ·
      refine ⟨327472228082910662519315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3493037099551047066872693 327472228082910662519315)
      ·
        refine ⟨491208342124365993778973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327472228082910662519315 491208342124365993778973)
        ·
          refine ⟨184203128296637247667115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491208342124365993778973 184203128296637247667115)
          ·
            refine ⟨276304692444955871500673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184203128296637247667115 276304692444955871500673)
            ·
              refine ⟨207228519333716903625505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276304692444955871500673 207228519333716903625505)
              ·
                refine ⟨155421389500287677719129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207228519333716903625505 155421389500287677719129)
                ·
                  refine ⟨116566042125215758289347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155421389500287677719129 116566042125215758289347)
                  ·
                    refine ⟨174849063187823637434021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116566042125215758289347 174849063187823637434021)
                    ·
                      refine ⟨32784199347716932018879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 174849063187823637434021 32784199347716932018879)
                      ·
                        rfl

theorem cell23_63847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_63847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63847 prefixEnd_63847 := by exact prefixLift 63847
  have htrace : WordTrace (prefixWord ++ tailWord_63847) baseStart_63847 baseEnd_63847 := by
    simpa [prefixWord, tailWord_63847, baseEnd_63847] using wordTrace_append hprefix tailTrace_63847
  have hstable : (prefixWord ++ tailWord_63847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63847).length < 2 ^ (prefixWord ++ tailWord_63847).sum := by decide
  have hdescent : baseEnd_63847 < baseStart_63847 := by decide
  rcases family_descends (prefixWord ++ tailWord_63847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63884 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_63884 : Nat := 118140960795 + 63884 * 2 ^ 59
def prefixEnd_63884 : Nat := 4983230072969 + 3 ^ 40 * 63884 * 2
def baseEnd_63884 : Nat := 32803198131933287256209

theorem tailTrace_63884 : CollatzResearch.WordTrace tailWord_63884 prefixEnd_63884 32803198131933287256209 := by
  unfold tailWord_63884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165020450283326681839353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1553360600377768909119137 1165020450283326681839353)
  ·
    refine ⟨873765337712495011379515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1165020450283326681839353 873765337712495011379515)
    ·
      refine ⟨1310648006568742517069273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 873765337712495011379515 1310648006568742517069273)
      ·
        refine ⟨982986004926556887801955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310648006568742517069273 982986004926556887801955)
        ·
          refine ⟨1474479007389835331702933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982986004926556887801955 1474479007389835331702933)
          ·
            refine ⟨69116203471398531173575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1474479007389835331702933 69116203471398531173575)
            ·
              refine ⟨103674305207097796760363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69116203471398531173575 103674305207097796760363)
              ·
                refine ⟨155511457810646695140545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103674305207097796760363 155511457810646695140545)
                ·
                  refine ⟨116633593357985021355409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155511457810646695140545 116633593357985021355409)
                  ·
                    refine ⟨87475195018488766016557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116633593357985021355409 87475195018488766016557)
                    ·
                      refine ⟨32803198131933287256209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87475195018488766016557 32803198131933287256209)
                      ·
                        rfl

theorem cell23_63884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_63884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63884 prefixEnd_63884 := by exact prefixLift 63884
  have htrace : WordTrace (prefixWord ++ tailWord_63884) baseStart_63884 baseEnd_63884 := by
    simpa [prefixWord, tailWord_63884, baseEnd_63884] using wordTrace_append hprefix tailTrace_63884
  have hstable : (prefixWord ++ tailWord_63884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63884).length < 2 ^ (prefixWord ++ tailWord_63884).sum := by decide
  have hdescent : baseEnd_63884 < baseStart_63884 := by decide
  rcases family_descends (prefixWord ++ tailWord_63884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63897 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_63897 : Nat := 118140960795 + 63897 * 2 ^ 59
def prefixEnd_63897 : Nat := 4983230072969 + 3 ^ 40 * 63897 * 2
def baseEnd_63897 : Nat := 32809873380441736393649

theorem tailTrace_63897 : CollatzResearch.WordTrace tailWord_63897 prefixEnd_63897 32809873380441736393649 := by
  unfold tailWord_63897
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330515049519556583901945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553676699679704389267963 2330515049519556583901945)
  ·
    refine ⟨1747886287139667437926459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330515049519556583901945 1747886287139667437926459)
    ·
      refine ⟨2621829430709501156889689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747886287139667437926459 2621829430709501156889689)
      ·
        refine ⟨1966372073032125867667267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2621829430709501156889689 1966372073032125867667267)
        ·
          refine ⟨2949558109548188801500901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966372073032125867667267 2949558109548188801500901)
          ·
            refine ⟨553042145540285400281419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2949558109548188801500901 553042145540285400281419)
            ·
              refine ⟨829563218310428100422129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553042145540285400281419 829563218310428100422129)
              ·
                refine ⟨622172413732821075316597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829563218310428100422129 622172413732821075316597)
                ·
                  refine ⟨58328663787451975810931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622172413732821075316597 58328663787451975810931)
                  ·
                    refine ⟨87492995681177963716397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58328663787451975810931 87492995681177963716397)
                    ·
                      refine ⟨32809873380441736393649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87492995681177963716397 32809873380441736393649)
                      ·
                        rfl

theorem cell23_63897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_63897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63897 prefixEnd_63897 := by exact prefixLift 63897
  have htrace : WordTrace (prefixWord ++ tailWord_63897) baseStart_63897 baseEnd_63897 := by
    simpa [prefixWord, tailWord_63897, baseEnd_63897] using wordTrace_append hprefix tailTrace_63897
  have hstable : (prefixWord ++ tailWord_63897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63897).length < 2 ^ (prefixWord ++ tailWord_63897).sum := by decide
  have hdescent : baseEnd_63897 < baseStart_63897 := by decide
  rcases family_descends (prefixWord ++ tailWord_63897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63957 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_63957 : Nat := 118140960795 + 63957 * 2 ^ 59
def prefixEnd_63957 : Nat := 4983230072969 + 3 ^ 40 * 63957 * 2
def baseEnd_63957 : Nat := 32840682219711501643373

theorem tailTrace_63957 : CollatzResearch.WordTrace tailWord_63957 prefixEnd_63957 32840682219711501643373 := by
  unfold tailWord_63957
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332703429302186831086125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555135619534791220724083 2332703429302186831086125)
  ·
    refine ⟨874763785988320061657297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2332703429302186831086125 874763785988320061657297)
    ·
      refine ⟨656072839491240046242973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874763785988320061657297 656072839491240046242973)
      ·
        refine ⟨246027314809215017341115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656072839491240046242973 246027314809215017341115)
        ·
          refine ⟨369040972213822526011673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246027314809215017341115 369040972213822526011673)
          ·
            refine ⟨276780729160366894508755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369040972213822526011673 276780729160366894508755)
            ·
              refine ⟨415171093740550341763133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276780729160366894508755 415171093740550341763133)
              ·
                refine ⟨155689160152706378161175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415171093740550341763133 155689160152706378161175)
                ·
                  refine ⟨233533740229059567241763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155689160152706378161175 233533740229059567241763)
                  ·
                    refine ⟨350300610343589350862645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233533740229059567241763 350300610343589350862645)
                    ·
                      refine ⟨32840682219711501643373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 350300610343589350862645 32840682219711501643373)
                      ·
                        rfl

theorem cell23_63957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_63957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63957 prefixEnd_63957 := by exact prefixLift 63957
  have htrace : WordTrace (prefixWord ++ tailWord_63957) baseStart_63957 baseEnd_63957 := by
    simpa [prefixWord, tailWord_63957, baseEnd_63957] using wordTrace_append hprefix tailTrace_63957
  have hstable : (prefixWord ++ tailWord_63957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63957).length < 2 ^ (prefixWord ++ tailWord_63957).sum := by decide
  have hdescent : baseEnd_63957 < baseStart_63957 := by decide
  rcases family_descends (prefixWord ++ tailWord_63957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63980 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_63980 : Nat := 118140960795 + 63980 * 2 ^ 59
def prefixEnd_63980 : Nat := 4983230072969 + 3 ^ 40 * 63980 * 2
def baseEnd_63980 : Nat := 32852492274764911655767

theorem tailTrace_63980 : CollatzResearch.WordTrace tailWord_63980 prefixEnd_63980 32852492274764911655767 := by
  unfold tailWord_63980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166771154109430879586697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1555694872145907839448929 1166771154109430879586697)
  ·
    refine ⟨875078365582073159690023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1166771154109430879586697 875078365582073159690023)
    ·
      refine ⟨1312617548373109739535035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875078365582073159690023 1312617548373109739535035)
      ·
        refine ⟨1968926322559664609302553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312617548373109739535035 1968926322559664609302553)
        ·
          refine ⟨1476694741919748456976915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968926322559664609302553 1476694741919748456976915)
          ·
            refine ⟨2215042112879622685465373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476694741919748456976915 2215042112879622685465373)
            ·
              refine ⟨830640792329858507049515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2215042112879622685465373 830640792329858507049515)
              ·
                refine ⟨1245961188494787760574273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 830640792329858507049515 1245961188494787760574273)
                ·
                  refine ⟨934470891371090820430705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1245961188494787760574273 934470891371090820430705)
                  ·
                    refine ⟨700853168528318115323029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 934470891371090820430705 700853168528318115323029)
                    ·
                      refine ⟨32852492274764911655767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 700853168528318115323029 32852492274764911655767)
                      ·
                        rfl

theorem cell23_63980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_63980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63980 prefixEnd_63980 := by exact prefixLift 63980
  have htrace : WordTrace (prefixWord ++ tailWord_63980) baseStart_63980 baseEnd_63980 := by
    simpa [prefixWord, tailWord_63980, baseEnd_63980] using wordTrace_append hprefix tailTrace_63980
  have hstable : (prefixWord ++ tailWord_63980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63980).length < 2 ^ (prefixWord ++ tailWord_63980).sum := by decide
  have hdescent : baseEnd_63980 < baseStart_63980 := by decide
  rcases family_descends (prefixWord ++ tailWord_63980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63981 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_63981 : Nat := 118140960795 + 63981 * 2 ^ 59
def prefixEnd_63981 : Nat := 4983230072969 + 3 ^ 40 * 63981 * 2
def baseEnd_63981 : Nat := 10951001918473135914421

theorem tailTrace_63981 : CollatzResearch.WordTrace tailWord_63981 prefixEnd_63981 10951001918473135914421 := by
  unfold tailWord_63981
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333578781215238929959797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555719187476825953306531 2333578781215238929959797)
  ·
    refine ⟨218773010738928649683731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2333578781215238929959797 218773010738928649683731)
    ·
      refine ⟨328159516108392974525597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218773010738928649683731 328159516108392974525597)
      ·
        refine ⟨123059818540647365447099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328159516108392974525597 123059818540647365447099)
        ·
          refine ⟨184589727810971048170649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123059818540647365447099 184589727810971048170649)
          ·
            refine ⟨138442295858228286127987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184589727810971048170649 138442295858228286127987)
            ·
              refine ⟨207663443787342429191981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138442295858228286127987 207663443787342429191981)
              ·
                refine ⟨77873791420253410946993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207663443787342429191981 77873791420253410946993)
                ·
                  refine ⟨58405343565190058210245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77873791420253410946993 58405343565190058210245)
                  ·
                    refine ⟨10951001918473135914421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58405343565190058210245 10951001918473135914421)
                    ·
                      rfl

theorem cell23_63981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_63981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63981 prefixEnd_63981 := by exact prefixLift 63981
  have htrace : WordTrace (prefixWord ++ tailWord_63981) baseStart_63981 baseEnd_63981 := by
    simpa [prefixWord, tailWord_63981, baseEnd_63981] using wordTrace_append hprefix tailTrace_63981
  have hstable : (prefixWord ++ tailWord_63981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63981).length < 2 ^ (prefixWord ++ tailWord_63981).sum := by decide
  have hdescent : baseEnd_63981 < baseStart_63981 := by decide
  rcases family_descends (prefixWord ++ tailWord_63981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63987 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3]
def baseStart_63987 : Nat := 118140960795 + 63987 * 2 ^ 59
def prefixEnd_63987 : Nat := 4983230072969 + 3 ^ 40 * 63987 * 2
def baseEnd_63987 : Nat := 32856086639346384268235

theorem tailTrace_63987 : CollatzResearch.WordTrace tailWord_63987 prefixEnd_63987 32856086639346384268235 := by
  unfold tailWord_63987
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333797619193501954678215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555865079462334636452143 2333797619193501954678215)
  ·
    refine ⟨3500696428790252932017323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333797619193501954678215 3500696428790252932017323)
    ·
      refine ⟨5251044643185379398025985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500696428790252932017323 5251044643185379398025985)
      ·
        refine ⟨3938283482389034548519489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5251044643185379398025985 3938283482389034548519489)
        ·
          refine ⟨2953712611791775911389617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3938283482389034548519489 2953712611791775911389617)
          ·
            refine ⟨2215284458843831933542213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2953712611791775911389617 2215284458843831933542213)
            ·
              refine ⟨415365836033218487539165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2215284458843831933542213 415365836033218487539165)
              ·
                refine ⟨155762188512456932827187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415365836033218487539165 155762188512456932827187)
                ·
                  refine ⟨233643282768685399240781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155762188512456932827187 233643282768685399240781)
                  ·
                    refine ⟨87616231038257024715293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233643282768685399240781 87616231038257024715293)
                    ·
                      refine ⟨32856086639346384268235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87616231038257024715293 32856086639346384268235)
                      ·
                        rfl

theorem cell23_63987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_63987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_63987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_63987 prefixEnd_63987 := by exact prefixLift 63987
  have htrace : WordTrace (prefixWord ++ tailWord_63987) baseStart_63987 baseEnd_63987 := by
    simpa [prefixWord, tailWord_63987, baseEnd_63987] using wordTrace_append hprefix tailTrace_63987
  have hstable : (prefixWord ++ tailWord_63987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63987).length < 2 ^ (prefixWord ++ tailWord_63987).sum := by decide
  have hdescent : baseEnd_63987 < baseStart_63987 := by decide
  rcases family_descends (prefixWord ++ tailWord_63987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64004 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_64004 : Nat := 118140960795 + 64004 * 2 ^ 59
def prefixEnd_64004 : Nat := 4983230072969 + 3 ^ 40 * 64004 * 2
def baseEnd_64004 : Nat := 32864815810472817755657

theorem tailTrace_64004 : CollatzResearch.WordTrace tailWord_64004 prefixEnd_64004 32864815810472817755657 := by
  unfold tailWord_64004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167208830065956929023533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1556278440087942572031377 1167208830065956929023533)
  ·
    refine ⟨437703311274733848383825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1167208830065956929023533 437703311274733848383825)
    ·
      refine ⟨328277483456050386287869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437703311274733848383825 328277483456050386287869)
      ·
        refine ⟨123104056296018894857951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328277483456050386287869 123104056296018894857951)
        ·
          refine ⟨184656084444028342286927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123104056296018894857951 184656084444028342286927)
          ·
            refine ⟨276984126666042513430391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184656084444028342286927 276984126666042513430391)
            ·
              refine ⟨415476189999063770145587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276984126666042513430391 415476189999063770145587)
              ·
                refine ⟨623214284998595655218381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415476189999063770145587 623214284998595655218381)
                ·
                  refine ⟨233705356874473370706893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623214284998595655218381 233705356874473370706893)
                  ·
                    refine ⟨87639508827927514015085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233705356874473370706893 87639508827927514015085)
                    ·
                      refine ⟨32864815810472817755657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87639508827927514015085 32864815810472817755657)
                      ·
                        rfl

theorem cell23_64004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_64004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64004 prefixEnd_64004 := by exact prefixLift 64004
  have htrace : WordTrace (prefixWord ++ tailWord_64004) baseStart_64004 baseEnd_64004 := by
    simpa [prefixWord, tailWord_64004, baseEnd_64004] using wordTrace_append hprefix tailTrace_64004
  have hstable : (prefixWord ++ tailWord_64004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64004).length < 2 ^ (prefixWord ++ tailWord_64004).sum := by decide
  have hdescent : baseEnd_64004 < baseStart_64004 := by decide
  rcases family_descends (prefixWord ++ tailWord_64004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64021 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_64021 : Nat := 118140960795 + 64021 * 2 ^ 59
def prefixEnd_64021 : Nat := 4983230072969 + 3 ^ 40 * 64021 * 2
def baseEnd_64021 : Nat := 32873544981599251243079

theorem tailTrace_64021 : CollatzResearch.WordTrace tailWord_64021 prefixEnd_64021 32873544981599251243079 := by
  unfold tailWord_64021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335037701070325761415917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1556691800713550507610611 2335037701070325761415917)
  ·
    refine ⟨875639137901372160530969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2335037701070325761415917 875639137901372160530969)
    ·
      refine ⟨656729353426029120398227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875639137901372160530969 656729353426029120398227)
      ·
        refine ⟨985094030139043680597341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656729353426029120398227 985094030139043680597341)
        ·
          refine ⟨369410261302141380224003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985094030139043680597341 369410261302141380224003)
          ·
            refine ⟨554115391953212070336005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369410261302141380224003 554115391953212070336005)
            ·
              refine ⟨103896635991227263188001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554115391953212070336005 103896635991227263188001)
              ·
                refine ⟨77922476993420447391001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103896635991227263188001 77922476993420447391001)
                ·
                  refine ⟨58441857745065335543251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77922476993420447391001 58441857745065335543251)
                  ·
                    refine ⟨87662786617598003314877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58441857745065335543251 87662786617598003314877)
                    ·
                      refine ⟨32873544981599251243079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 87662786617598003314877 32873544981599251243079)
                      ·
                        rfl

theorem cell23_64021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_64021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64021 prefixEnd_64021 := by exact prefixLift 64021
  have htrace : WordTrace (prefixWord ++ tailWord_64021) baseStart_64021 baseEnd_64021 := by
    simpa [prefixWord, tailWord_64021, baseEnd_64021] using wordTrace_append hprefix tailTrace_64021
  have hstable : (prefixWord ++ tailWord_64021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64021).length < 2 ^ (prefixWord ++ tailWord_64021).sum := by decide
  have hdescent : baseEnd_64021 < baseStart_64021 := by decide
  rcases family_descends (prefixWord ++ tailWord_64021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64057 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_64057 : Nat := 118140960795 + 64057 * 2 ^ 59
def prefixEnd_64057 : Nat := 4983230072969 + 3 ^ 40 * 64057 * 2
def baseEnd_64057 : Nat := 32892030285161110392913

theorem tailTrace_64057 : CollatzResearch.WordTrace tailWord_64057 prefixEnd_64057 32892030285161110392913 := by
  unfold tailWord_64057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336350728939903909726425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1557567152626602606484283 2336350728939903909726425)
  ·
    refine ⟨1752263046704927932294819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2336350728939903909726425 1752263046704927932294819)
    ·
      refine ⟨2628394570057391898442229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752263046704927932294819 2628394570057391898442229)
      ·
        refine ⟨246411990942880490478959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2628394570057391898442229 246411990942880490478959)
        ·
          refine ⟨369617986414320735718439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246411990942880490478959 369617986414320735718439)
          ·
            refine ⟨554426979621481103577659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369617986414320735718439 554426979621481103577659)
            ·
              refine ⟨831640469432221655366489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554426979621481103577659 831640469432221655366489)
              ·
                refine ⟨623730352074166241524867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 831640469432221655366489 623730352074166241524867)
                ·
                  refine ⟨935595528111249362287301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623730352074166241524867 935595528111249362287301)
                  ·
                    refine ⟨175424161520859255428869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 935595528111249362287301 175424161520859255428869)
                    ·
                      refine ⟨32892030285161110392913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 175424161520859255428869 32892030285161110392913)
                      ·
                        rfl

theorem cell23_64057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_64057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64057 prefixEnd_64057 := by exact prefixLift 64057
  have htrace : WordTrace (prefixWord ++ tailWord_64057) baseStart_64057 baseEnd_64057 := by
    simpa [prefixWord, tailWord_64057, baseEnd_64057] using wordTrace_append hprefix tailTrace_64057
  have hstable : (prefixWord ++ tailWord_64057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64057).length < 2 ^ (prefixWord ++ tailWord_64057).sum := by decide
  have hdescent : baseEnd_64057 < baseStart_64057 := by decide
  rcases family_descends (prefixWord ++ tailWord_64057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64061 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_64061 : Nat := 118140960795 + 64061 * 2 ^ 59
def prefixEnd_64061 : Nat := 4983230072969 + 3 ^ 40 * 64061 * 2
def baseEnd_64061 : Nat := 32894084207779094742895

theorem tailTrace_64061 : CollatzResearch.WordTrace tailWord_64061 prefixEnd_64061 32894084207779094742895 := by
  unfold tailWord_64061
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336496620925412592872037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1557664413950275061914691 2336496620925412592872037)
  ·
    refine ⟨438093116423514861163507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2336496620925412592872037 438093116423514861163507)
    ·
      refine ⟨657139674635272291745261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438093116423514861163507 657139674635272291745261)
      ·
        refine ⟨246427377988227109404473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657139674635272291745261 246427377988227109404473)
        ·
          refine ⟨184820533491170332053355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246427377988227109404473 184820533491170332053355)
          ·
            refine ⟨277230800236755498080033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184820533491170332053355 277230800236755498080033)
            ·
              refine ⟨207923100177566623560025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277230800236755498080033 207923100177566623560025)
              ·
                refine ⟨155942325133174967670019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207923100177566623560025 155942325133174967670019)
                ·
                  refine ⟨233913487699762451505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155942325133174967670019 233913487699762451505029)
                  ·
                    refine ⟨43858778943705459657193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 233913487699762451505029 43858778943705459657193)
                    ·
                      refine ⟨32894084207779094742895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43858778943705459657193 32894084207779094742895)
                      ·
                        rfl

theorem cell23_64061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_64061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64061 prefixEnd_64061 := by exact prefixLift 64061
  have htrace : WordTrace (prefixWord ++ tailWord_64061) baseStart_64061 baseEnd_64061 := by
    simpa [prefixWord, tailWord_64061, baseEnd_64061] using wordTrace_append hprefix tailTrace_64061
  have hstable : (prefixWord ++ tailWord_64061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64061).length < 2 ^ (prefixWord ++ tailWord_64061).sum := by decide
  have hdescent : baseEnd_64061 < baseStart_64061 := by decide
  rcases family_descends (prefixWord ++ tailWord_64061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64065 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_64065 : Nat := 118140960795 + 64065 * 2 ^ 59
def prefixEnd_64065 : Nat := 4983230072969 + 3 ^ 40 * 64065 * 2
def baseEnd_64065 : Nat := 32896138130397079092877

theorem tailTrace_64065 : CollatzResearch.WordTrace tailWord_64065 prefixEnd_64065 32896138130397079092877 := by
  unfold tailWord_64065
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336642512910921276017649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1557761675273947517345099 2336642512910921276017649)
  ·
    refine ⟨1752481884683190957013237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2336642512910921276017649 1752481884683190957013237)
    ·
      refine ⟨164295176689049152219991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1752481884683190957013237 164295176689049152219991)
      ·
        refine ⟨246442765033573728329987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164295176689049152219991 246442765033573728329987)
        ·
          refine ⟨369664147550360592494981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246442765033573728329987 369664147550360592494981)
          ·
            refine ⟨69312027665692611092809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369664147550360592494981 69312027665692611092809)
            ·
              refine ⟨51984020749269458319607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69312027665692611092809 51984020749269458319607)
              ·
                refine ⟨77976031123904187479411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51984020749269458319607 77976031123904187479411)
                ·
                  refine ⟨116964046685856281219117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77976031123904187479411 116964046685856281219117)
                  ·
                    refine ⟨43861517507196105457169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116964046685856281219117 43861517507196105457169)
                    ·
                      refine ⟨32896138130397079092877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43861517507196105457169 32896138130397079092877)
                      ·
                        rfl

theorem cell23_64065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_64065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64065 prefixEnd_64065 := by exact prefixLift 64065
  have htrace : WordTrace (prefixWord ++ tailWord_64065) baseStart_64065 baseEnd_64065 := by
    simpa [prefixWord, tailWord_64065, baseEnd_64065] using wordTrace_append hprefix tailTrace_64065
  have hstable : (prefixWord ++ tailWord_64065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64065).length < 2 ^ (prefixWord ++ tailWord_64065).sum := by decide
  have hdescent : baseEnd_64065 < baseStart_64065 := by decide
  rcases family_descends (prefixWord ++ tailWord_64065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64078 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_64078 : Nat := 118140960795 + 64078 * 2 ^ 59
def prefixEnd_64078 : Nat := 4983230072969 + 3 ^ 40 * 64078 * 2
def baseEnd_64078 : Nat := 32902813378905528230317

theorem tailTrace_64078 : CollatzResearch.WordTrace tailWord_64078 prefixEnd_64078 32902813378905528230317 := by
  unfold tailWord_64078
  simp only [CollatzResearch.WordTrace]
  refine ⟨292139582732978062030111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1558077774575882997493925 292139582732978062030111)
  ·
    refine ⟨438209374099467093045167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292139582732978062030111 438209374099467093045167)
    ·
      refine ⟨657314061149200639567751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438209374099467093045167 657314061149200639567751)
      ·
        refine ⟨985971091723800959351627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657314061149200639567751 985971091723800959351627)
        ·
          refine ⟨1478956637585701439027441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985971091723800959351627 1478956637585701439027441)
          ·
            refine ⟨1109217478189276079270581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478956637585701439027441 1109217478189276079270581)
            ·
              refine ⟨103989138580244632431617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1109217478189276079270581 103989138580244632431617)
              ·
                refine ⟨77991853935183474323713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103989138580244632431617 77991853935183474323713)
                ·
                  refine ⟨58493890451387605742785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77991853935183474323713 58493890451387605742785)
                  ·
                    refine ⟨43870417838540704307089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58493890451387605742785 43870417838540704307089)
                    ·
                      refine ⟨32902813378905528230317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43870417838540704307089 32902813378905528230317)
                      ·
                        rfl

theorem cell23_64078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_64078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64078 prefixEnd_64078 := by exact prefixLift 64078
  have htrace : WordTrace (prefixWord ++ tailWord_64078) baseStart_64078 baseEnd_64078 := by
    simpa [prefixWord, tailWord_64078, baseEnd_64078] using wordTrace_append hprefix tailTrace_64078
  have hstable : (prefixWord ++ tailWord_64078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64078).length < 2 ^ (prefixWord ++ tailWord_64078).sum := by decide
  have hdescent : baseEnd_64078 < baseStart_64078 := by decide
  rcases family_descends (prefixWord ++ tailWord_64078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64084 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 7]
def baseStart_64084 : Nat := 118140960795 + 64084 * 2 ^ 59
def prefixEnd_64084 : Nat := 4983230072969 + 3 ^ 40 * 64084 * 2
def baseEnd_64084 : Nat := 3656210473648056083921

theorem tailTrace_64084 : CollatzResearch.WordTrace tailWord_64084 prefixEnd_64084 3656210473648056083921 := by
  unfold tailWord_64084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168667749921043760479653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1558223666561391680639537 1168667749921043760479653)
  ·
    refine ⟨219125203110195705089935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1168667749921043760479653 219125203110195705089935)
    ·
      refine ⟨328687804665293557634903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219125203110195705089935 328687804665293557634903)
      ·
        refine ⟨493031706997940336452355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328687804665293557634903 493031706997940336452355)
        ·
          refine ⟨739547560496910504678533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493031706997940336452355 739547560496910504678533)
          ·
            refine ⟨138665167593170719627225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 739547560496910504678533 138665167593170719627225)
            ·
              refine ⟨103998875694878039720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138665167593170719627225 103998875694878039720419)
              ·
                refine ⟨155998313542317059580629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103998875694878039720419 155998313542317059580629)
                ·
                  refine ⟨3656210473648056083921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155998313542317059580629 3656210473648056083921)
                  ·
                    rfl

theorem cell23_64084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_64084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64084 prefixEnd_64084 := by exact prefixLift 64084
  have htrace : WordTrace (prefixWord ++ tailWord_64084) baseStart_64084 baseEnd_64084 := by
    simpa [prefixWord, tailWord_64084, baseEnd_64084] using wordTrace_append hprefix tailTrace_64084
  have hstable : (prefixWord ++ tailWord_64084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64084).length < 2 ^ (prefixWord ++ tailWord_64084).sum := by decide
  have hdescent : baseEnd_64084 < baseStart_64084 := by decide
  rcases family_descends (prefixWord ++ tailWord_64084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64097 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_64097 : Nat := 118140960795 + 64097 * 2 ^ 59
def prefixEnd_64097 : Nat := 4983230072969 + 3 ^ 40 * 64097 * 2
def baseEnd_64097 : Nat := 10970856503780317964243

theorem tailTrace_64097 : CollatzResearch.WordTrace tailWord_64097 prefixEnd_64097 10970856503780317964243 := by
  unfold tailWord_64097
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337809648794990741182545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558539765863327160788363 2337809648794990741182545)
  ·
    refine ⟨1753357236596243055886909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2337809648794990741182545 1753357236596243055886909)
    ·
      refine ⟨657508963723591145957591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1753357236596243055886909 657508963723591145957591)
      ·
        refine ⟨986263445585386718936387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657508963723591145957591 986263445585386718936387)
        ·
          refine ⟨1479395168378080078404581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986263445585386718936387 1479395168378080078404581)
          ·
            refine ⟨277386594070890014700859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1479395168378080078404581 277386594070890014700859)
            ·
              refine ⟨416079891106335022051289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277386594070890014700859 416079891106335022051289)
              ·
                refine ⟨312059918329751266538467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416079891106335022051289 312059918329751266538467)
                ·
                  refine ⟨468089877494626899807701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312059918329751266538467 468089877494626899807701)
                  ·
                    refine ⟨10970856503780317964243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 468089877494626899807701 10970856503780317964243)
                    ·
                      rfl

theorem cell23_64097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_64097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64097 prefixEnd_64097 := by exact prefixLift 64097
  have htrace : WordTrace (prefixWord ++ tailWord_64097) baseStart_64097 baseEnd_64097 := by
    simpa [prefixWord, tailWord_64097, baseEnd_64097] using wordTrace_append hprefix tailTrace_64097
  have hstable : (prefixWord ++ tailWord_64097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64097).length < 2 ^ (prefixWord ++ tailWord_64097).sum := by decide
  have hdescent : baseEnd_64097 < baseStart_64097 := by decide
  rcases family_descends (prefixWord ++ tailWord_64097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64197 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_64197 : Nat := 118140960795 + 64197 * 2 ^ 59
def prefixEnd_64197 : Nat := 4983230072969 + 3 ^ 40 * 64197 * 2
def baseEnd_64197 : Nat := 32963917576790562642269

theorem tailTrace_64197 : CollatzResearch.WordTrace tailWord_64197 prefixEnd_64197 32963917576790562642269 := by
  unfold tailWord_64197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341456948432707819822845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1560971298955138546548563 2341456948432707819822845)
  ·
    refine ⟨878046355662265432433567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2341456948432707819822845 878046355662265432433567)
    ·
      refine ⟨1317069533493398148650351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878046355662265432433567 1317069533493398148650351)
      ·
        refine ⟨1975604300240097222975527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317069533493398148650351 1975604300240097222975527)
        ·
          refine ⟨2963406450360145834463291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975604300240097222975527 2963406450360145834463291)
          ·
            refine ⟨4445109675540218751694937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963406450360145834463291 4445109675540218751694937)
            ·
              refine ⟨3333832256655164063771203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445109675540218751694937 3333832256655164063771203)
              ·
                refine ⟨5000748384982746095656805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333832256655164063771203 5000748384982746095656805)
                ·
                  refine ⟨937640322184264892935651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5000748384982746095656805 937640322184264892935651)
                  ·
                    refine ⟨1406460483276397339403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 937640322184264892935651 1406460483276397339403477)
                    ·
                      refine ⟨32963917576790562642269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1406460483276397339403477 32963917576790562642269)
                      ·
                        rfl

theorem cell23_64197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_64197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64197 prefixEnd_64197 := by exact prefixLift 64197
  have htrace : WordTrace (prefixWord ++ tailWord_64197) baseStart_64197 baseEnd_64197 := by
    simpa [prefixWord, tailWord_64197, baseEnd_64197] using wordTrace_append hprefix tailTrace_64197
  have hstable : (prefixWord ++ tailWord_64197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64197).length < 2 ^ (prefixWord ++ tailWord_64197).sum := by decide
  have hdescent : baseEnd_64197 < baseStart_64197 := by decide
  rcases family_descends (prefixWord ++ tailWord_64197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
